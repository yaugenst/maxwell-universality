#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "matplotlib>=3.9,<4"]
# ///
"""Regenerate the extended device, precision and robustness report from receipts."""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from analyze import cell_intensity


ROOT=Path(__file__).parent
RESULTS=ROOT/"results"
OUT=ROOT/"report"


def read(path):
    return json.loads(path.read_text())


def label(name):
    if name=="signed_spd":
        return "s = 0"
    if name=="conditioned_spd":
        return "0.2 I + 11ᵀ"
    return f"s = {int(name.split('_')[1])/100:g}"


def main():
    cases=[]
    for group in ("direct_refinement_a","direct_refinement_b"):
        for row in read(RESULTS/group/"summary.json"):
            row["group"]=group
            cases.append(row)
    cases.sort(key=lambda d:d["target_condition"])
    if len(cases)!=7:
        raise ValueError("The report requires all seven final matrix cases")
    robust=read(RESULTS/"robustness/robustness.json")
    by_name={r["name"]:r for r in robust}
    precision=read(RESULTS/"precision/joint_rounding.json")
    residual=read(RESULTS/"precision/adversarial_residual.json")
    modes=read(RESULTS/"mode_diagnosis/diagnosis.json")
    original=next(r for r in read(RESULTS/"tuned_control/fixed_device_refinement.json") if abs(r["h"]-1/6)<1e-9)
    ideal=np.array(original["decoded_solutions"])[:,:2]
    gamma=np.array(original["target"])
    for r in precision:
        r["rounding_equation_operator_increment"]=float(np.linalg.norm(gamma@(np.array(r["decoded_response_real"])-ideal),2))
    passing=[r for r in cases if max(v["worst_relative_equation_residual"] for v in r["verification"][1:])<.01]
    condition=read(RESULTS/"conditioning_v3/conditioning.json")+read(RESULTS/"final_instability_spectrum/conditioning.json")
    unstable=condition[-1]
    near_zero=unstable["nearest_eigenpairs"][0]
    spectral=read(RESULTS/"spectral_refinement/summary.json")
    high_order=read(RESULTS/"order12_refinement/summary.json")[0]
    order_control=read(RESULTS/"fixed_device_order_comparison/summary.json")[0]
    summary={"final_devices":cases,"devices_below_one_percent_on_both_finer_grids":[r["name"] for r in passing],
             "joint_input_precision":precision,"full_field_residual_test":residual,
             "original_device_robustness":robust,"mode_truncation":modes,"spectral_estimates":condition,
             "smooth_source_comparison":spectral,"order12_control":high_order,"same_device_order_comparison":order_control}
    OUT.mkdir(exist_ok=True)
    (OUT/"extended_summary.json").write_text(json.dumps(summary,indent=2)+"\n")

    plt.rcParams.update({"font.size":10,"axes.titlesize":11,"axes.spines.top":False,
                         "axes.spines.right":False,"figure.facecolor":"white","savefig.facecolor":"white"})
    selected=min(cases,key=lambda r:max(v["worst_relative_equation_residual"] for v in r["verification"][1:]))
    last=selected["verification"][-1]
    base=RESULTS/selected["group"]/selected["name"]/f"h{last['h']:.8g}"
    arrays=np.load(base/"verification_fields.npz")
    metadata=read(base/"metadata.json")
    extent=[-4,4,-4,4]
    mid=int(arrays["shape"][1]//2)
    fig,ax=plt.subplots(2,2,figsize=(12,9),layout="constrained")
    im=ax[0,0].imshow(arrays["eps_cells"][:,mid,:].T,origin="lower",extent=extent,cmap="viridis")
    for i,(x,y,z) in enumerate(metadata["centers"]):
        ax[0,0].text(x,z,f"T{i+1}" if i<3 else str(i+1),color="white",ha="center",va="center",fontsize=9)
    ax[0,0].set(xlabel="x",ylabel="z",title=f"a  Scalar dielectric: three terminals, six defects ({label(selected['name'])})")
    fig.colorbar(im,ax=ax[0,0],label="Permittivity ε",shrink=.8)
    intensity=cell_intensity(arrays)
    im=ax[0,1].imshow(np.log10(np.maximum(intensity[:,mid,:].T/intensity.max(),1e-8)),origin="lower",
                      extent=extent,cmap="magma",vmin=-8,vmax=0)
    ax[0,1].set(xlabel="x",ylabel="z",title="b  Full-vector Maxwell field for the first basis input")
    fig.colorbar(im,ax=ax[0,1],label="log₁₀ normalized |E|²",shrink=.8)
    colors=plt.get_cmap("tab10")(np.arange(len(cases)))
    for row,color in zip(cases,colors):
        checks=row["verification"]
        ax[1,0].semilogy([v["h"] for v in checks],[v["worst_relative_equation_residual"] for v in checks],
                         "o-",color=color,label=label(row["name"]))
        error=max(v["worst_relative_equation_residual"] for v in checks[1:])
        indefinite=min(np.linalg.eigvalsh(row["target"]))<0
        ax[1,1].plot(row["target_condition"],error,"D" if indefinite else "o",color=color,ms=7)
        offset={"signed_spd":(-5,-14),"shift_50":(-5,0)}.get(row["name"],(5,5))
        ax[1,1].annotate(label(row["name"]),(row["target_condition"],error),xytext=offset,
                         ha="right" if offset[0]<0 else "left",textcoords="offset points",fontsize=8)
    ax[1,0].axhline(.01,color="black",ls="--",lw=1,label="1% equation error")
    ax[1,0].invert_xaxis()
    ax[1,0].set(xlabel="Maxwell grid spacing h",ylabel="Worst relative equation residual",
                title="c  One calibration mesh, then two frozen-device checks")
    ax[1,0].legend(fontsize=8,ncol=2,loc="lower right")
    ax[1,1].set(xscale="log",yscale="log",xlabel="Condition number of the 3 × 3 target",
                ylabel="Worst error across both finer grids",title="d  Conditioning sweep; diamond denotes indefinite target")
    ax[1,1].axhline(.01,color="black",ls="--",lw=1)
    ax[1,1].margins(x=.35,y=.35)
    for a in ax[1]:
        a.grid(alpha=.18,which="both")
    for suffix in ("png","pdf"):
        fig.savefig(OUT/f"extended_devices.{suffix}",dpi=180)
    plt.close(fig)

    fig,ax=plt.subplots(1,2,figsize=(11.5,4.5),layout="constrained")
    names=[r["name"] for r in spectral]
    original_by_name={r["name"]:r for r in cases}
    for offset,data,title,color in ((-.18,[original_by_name[n] for n in names],"Cubic source interpolant","#2563eb"),
                                   (.18,spectral,"Smooth PEC Fourier source","#0f766e")):
        ax[0].bar(np.arange(len(names))+offset,[max(v["worst_relative_equation_residual"] for v in r["verification"][1:]) for r in data],
                  width=.34,label=title,color=color)
    ax[0].set(xticks=np.arange(len(names)),xticklabels=[label(n) for n in names],yscale="log",
              ylabel="Worst equation error on two finer grids",title="a  Source smoothing does not remove the difficult cases")
    ax[0].axhline(.01,color="black",ls="--",lw=1)
    ax[0].legend(fontsize=9)
    for checks,title in ((order_control["verification"],"Order 8"),(high_order["verification"][1:],"Order 12")):
        ax[1].plot([r["h"] for r in checks],[r["worst_relative_equation_residual"] for r in checks],"o-",label=title)
    ax[1].set(xlabel="Grid spacing h",ylabel="Worst relative equation residual",
              title="b  Same fixed dielectric and smooth sources, two stencil orders")
    ax[1].invert_xaxis()
    ax[1].legend()
    for a in ax:
        a.grid(alpha=.18,which="both")
    for suffix in ("png","pdf"):
        fig.savefig(OUT/f"discretization_controls.{suffix}",dpi=180)
    plt.close(fig)

    fig,ax=plt.subplots(2,2,figsize=(12,8.5),layout="constrained")
    ax[0,0].semilogy([r["fractional_bits"] for r in precision],[r["worst_relative_equation_residual"] for r in precision],"o-",label="Total error on finer grid")
    ax[0,0].semilogy([r["fractional_bits"] for r in precision],[r["rounding_equation_operator_increment"] for r in precision],"s-",label="Increment from joint rounding")
    ax[0,0].axhline(np.linalg.norm(gamma@ideal-np.eye(2),2),color="gray",ls="--",label="Unrounded device on same grid")
    ax[0,0].set(xlabel="Fractional bits in supplied parameters",ylabel="Worst relative equation residual",title="a  Joint material, drive and source/readout precision")
    ax[0,0].legend(fontsize=8)
    controls=[("Strength −1%","uniform_strength_-0.01"),("Radius −1%","radius_-0.01"),
              ("Shift x by 0.025","material_shift_x_0.025"),("Im ε = 0.001","absorption_0.001"),
              ("Longer cavity","buffer_longitudinal"),("Wider cavity","buffer_transverse")]
    ax[0,1].barh([r[0] for r in controls],[by_name[r[1]]["worst_relative_equation_residual"] for r in controls],color="#0f766e")
    ax[0,1].set(xscale="log",xlabel="Worst relative equation residual",title="b  Perturb the original working two-variable device")
    ax[0,1].invert_yaxis()
    samples=residual["samples"]
    ax[1,0].loglog([r["measured_relative_maxwell_residual"] for r in samples],[r["equation_error_increment"] for r in samples],"o",ms=7,label="Explicit perturbed fields")
    ax[1,0].loglog([r["requested_relative_maxwell_residual"] for r in samples],[r["norm_prediction"] for r in samples],"--",label=f"Norm prediction: {residual['residual_gain']:.2f} η")
    ax[1,0].set(xlabel="Relative residual of the full Maxwell field",ylabel="Increment in target equation error",title="c  Adversarial residual direction, including all field coordinates")
    ax[1,0].legend(fontsize=9)
    for design in modes:
        data=[r for r in design["ranks"] if r["modes_per_defect"]<=1024]
        ax[1,1].loglog([r["modes_per_defect"] for r in data],[r["terminal_equation_prediction_error"] for r in data],"o-",label=design["name"].replace("_"," "))
    ax[1,1].set(xlabel="Local eigenmodes retained per defect",ylabel="Equation-operator error versus full support",title="d  The chosen single-mode approximation is inadequate")
    ax[1,1].legend(fontsize=9)
    for a in ax.ravel():
        a.grid(alpha=.18,which="both")
    for suffix in ("png","pdf"):
        fig.savefig(OUT/f"precision_and_robustness.{suffix}",dpi=180)
    plt.close(fig)

    table=[]
    for r in cases:
        checks=r["verification"]
        table.append(f"| {label(r['name'])} | {r['target_condition']:.3g} | {'indefinite' if min(np.linalg.eigvalsh(r['target']))<0 else 'positive definite'} | "+" | ".join(f"{100*v['worst_relative_equation_residual']:.4g}%" for v in checks)+f" | {'yes' if r['calibration_converged'] else 'no'} |")
    precision_table="\n".join(f"| {r['fractional_bits']} | {100*r['worst_relative_equation_residual']:.4g}% | {100*r['rounding_equation_operator_increment']:.4g}% |" for r in precision)
    spectral_table="\n".join(f"| {r['case']} | {r['nearest_eigenpairs'][0]['rayleigh_eigenvalue']:.4g} | {r['nearest_eigenpairs'][0]['absolute_eigen_residual']:.3g} | {r['estimated_spectral_condition']:.3g} |" for r in condition)
    best=max(v["worst_relative_equation_residual"] for v in selected["verification"][1:])
    report=f"""# Extended Maxwell implementation study

The study now includes **seven prescribed three-variable designs**, a joint finite-precision input test, material and geometry perturbations, and an adversarial field-residual experiment. **{len(passing)} of the seven final designs have less than 1% worst-case equation error on both independent finer grids.** The best such two-grid result is {100*best:.4g}%. All targets and failed searches are retained. This is numerical evidence for calibrated dielectric designs, not manufactured hardware, a continuum certificate, or the theorem's scalable local encoder.

![Three-variable devices and frozen refinement](extended_devices.png)

## What is stronger than the original demonstration

The full-vector, lossless PEC equation is solved with bounded scalar dielectric, all polarizations and gradient channels present, and no momentum filter. Three independent source fields span every right-hand side of each target; the reported error is the operator norm `||Γ X − I||₂`, not an average over selected inputs. The grid grows from 237,444 unknowns at calibration to 302,991 and 379,610 for independent verification. Material strengths, continuous source/readout functions, drive gain and decoder are frozen across these checks.

The six defects occupy the same `8 × 6 × 8` cavity in every three-variable case. The signed target family is

`Γ_s = [[3, −0.6, 0.4], [−0.6, 2.5, 0.8], [0.4, 0.8, 3.5]] − s I`,

with `s = 0, 0.5, 1, 1.5, 1.6, 2`. The last is indefinite. The additional target `0.2 I + 11ᵀ` has condition number 16. These matrices were supplied to the calibration procedure; none was defined by inverting a measured device response. The shift family was added after the original signed case succeeded, so it is an adaptive extension, not an independently blinded matrix sample.

Full-background calibration supplies the initial designs. Final tuning changes only the six material amplitudes using full Maxwell solves and the exact discrete derivative `dX/dv_i = Eᵀ W_i E / α`. Source profiles, source gains and the decoder remain fixed even during this final tuning. A separate finite-difference material perturbation checks this derivative to {read(RESULTS/'material_gradient_check.json')['relative_directional_derivative_difference']:.3g} relative difference. No inverse of the target appears in source programming or decoding. Calibration itself is expensive global inverse design, and its cost is not claimed to be smaller than solving the input system.

| Target | κ₂(Γ) | Type | Calibration h=1/6 | Frozen h=2/13 | Frozen h=1/7 | Calibration reached 1e−7 |
| --- | ---: | --- | ---: | ---: | ---: | --- |
{chr(10).join(table)}

The field image is one actual basis-source solve. Its cell-centred intensity interpolation is for visualization; quantitative residuals use the original staggered fields. Changing the verification grid does not retune the material or rebuild its source functions.

## Precision and robustness are now measured

![Precision, perturbations, residual amplification and model error](precision_and_robustness.png)

These controls use the **original two-variable working device**, not the new three-variable family. The joint rounding test applies spacing `2^(−bits)` to the background constant, every defect strength, drive gain and every physical spline sample specifying source/readout profiles. Geometry, the analytic cosine/bump functions and solver arithmetic are unchanged. It is a finite parameter-precision test, not a measurement of asymptotic `O(log m)` bit complexity.

| Fractional bits | Total equation error on h=1/6 | Additional equation-operator error from rounding |
| ---: | ---: | ---: |
{precision_table}

The extra-error column compares to the unrounded device on the **same** grid, avoiding credit for accidental cancellation of discretization error. At 16 bits the rounding increment is {100*precision[-1]['rounding_equation_operator_increment']:.4g}%.

For arbitrary full-field residuals, reciprocity gives a discrete recovery norm. Explicitly constructed perturbations attain the measured factor **{residual['residual_gain']:.5g}**: a relative Maxwell residual η causes a target-equation error increment of {residual['residual_gain']:.5g}η in the worst tested direction. The residual direction spans the complete electric field space, including components outside the source/probe span. This checks recovery sensitivity at one finite discretization; it does not certify continuum conditioning or its dependence on problem size.

For the same original device, a uniform −1% strength perturbation gives {100*by_name['uniform_strength_-0.01']['worst_relative_equation_residual']:.3g}% equation error, shrinking radii by 1% gives {100*by_name['radius_-0.01']['worst_relative_equation_residual']:.3g}%, and adding imaginary permittivity 0.001 gives {100*by_name['absorption_0.001']['worst_relative_equation_residual']:.3g}%. The absorbing control lies outside the lossless theorem. Changing the longitudinal or transverse PEC walls gives errors of {100*by_name['buffer_longitudinal']['worst_relative_equation_residual']:.3g}% and {100*by_name['buffer_transverse']['worst_relative_equation_residual']:.3g}%. The designs depend on the whole cavity; locality and fabrication tolerance have not been established by good nominal accuracy.

## Failures that constrain the interpretation

The originally prescribed unequal positive target `[[4,1,0.5],[1,3,0.75],[0.5,0.75,2.5]]` did not reach the calibration criterion in the recorded six-site searches. Adding two material sites improved its best calibration error to about 5.17%, but still failed. These are failed bounded searches, not a proof that the target cannot be realized. They rule out describing this experiment as an arbitrary-matrix compiler.

The initial single-mode local gadget remains inaccurate. A controlled truncation retaining the selected port mode and then local modes in decreasing absolute compressed-resolvent eigenvalue converges slowly: hundreds of modes are needed in this particular basis. The full 1,494 coordinates per defect recover the exact finite-support response. This does not prove that every possible reduced basis needs that many modes. Direct terminal coupling and discarded-mode corrections are both measured; the implementation retains them in global calibration rather than asserting locality.

An exact fit on a calibration grid is insufficient. The original coherent condition-16 target had about 96% error after refining its coarse calibration. Even calibration at h=0.2 left roughly 66% error at h=2/13 before the final material-only correction above. These failed stages are preserved in `network_free_scale` and `network_fine`.

![Source regularity and higher-order controls](discretization_controls.png)

Two further controls test implementation alternatives. The smooth-source variant uses a fixed finite sine/cosine expansion compatible with the PEC grid, multiplied by the compact smooth bump. It is infinitely differentiable and reproduces the reference source samples to {read(RESULTS/'spectral_source_check.json')['relative_reconstruction_error']:.3g} relative error. It does not restrict the operator's modes. Repeating calibration and refinement for three targets changes the errors only modestly; the source interpolation is not the main explanation of the difficult cases.

The twelfth-order stencil uses exact rational Lagrange derivative coefficients rounded once to floating point. A variable-material analytic cavity solution gives observed convergence order {read(RESULTS/'validation_order12_final/validation.json')['last_observed_order']:.3f}, with zero measured curl-gradient product. An independent higher-order calibration of the coherent condition-16 target at h=0.2 still gives errors of {100*high_order['verification'][1]['worst_relative_equation_residual']:.3g}% and {100*high_order['verification'][2]['worst_relative_equation_residual']:.3g}% on h=2/11 and h=1/6. The plot compares both stencil orders on that **same final dielectric, source and decoder**. Neither a smoother source nor this order increase establishes accuracy for this case.

## Full-matrix spectral diagnostics

Shift-invert Lanczos acts on the complete assembled Maxwell operator, independently of the terminal response. The table gives numerical estimates and directly evaluated eigen-residuals, not certified spectral enclosures or continuum bounds.

| Saved case | Estimated nearest eigenvalue to zero | Absolute eigen-residual | Estimated matrix κ₂ |
| --- | ---: | ---: | ---: |
{spectral_table}

The final coherent design is especially informative: its target has condition number 16, but its full Maxwell matrix on the failing `h=2/13` mesh has estimated condition number {unstable['estimated_spectral_condition']:.3g}. A near-zero eigenvalue {near_zero['rayleigh_eigenvalue']:.3g}, with absolute eigen-residual {near_zero['absolute_eigen_residual']:.3g}, has normalized source overlap {near_zero['normalized_source_overlap']:.4g}. This is evidence of a resonance coupled to the sources, consistent with the large response error. The calibration controls the terminal response at one mesh without imposing a lower bound on the full operator's distance from singularity. A successful fit therefore does not establish the stability needed for a general implementation.

Matrix condition numbers also include the mesh-dependent largest curl eigenvalue; they are not themselves continuum resolvent norms. See the saved spectra for source overlap and inverse-solve residuals. Two earlier spectral-diagnostic attempts failed in wrapper handling (RHS strides and an object lifetime); they produced no spectral conclusions and are not included above.

## Reproduction and evidence

All work is confined to this experiment directory; the manuscript and paused Lean work were not edited. [Protocol and commands](../README.md), [full Maxwell tuning](../refine_device.py), [precision experiment](../precision.py), [robustness experiment](../robustness.py), [spectral diagnostic](../conditioning.py), and [machine-readable extended results](extended_summary.json) accompany this report. Regenerate the figures and report with `uv run --script analyze_extended.py`.

The extended runs used one GPU per job with two host numerical-library threads per job. Dense calibration used CuPy/cuSOLVER; sparse field solves used cuDSS. The 379,610-unknown case was admitted after cuDSS's memory plan estimated 112.6 GB peak device memory, within the allocated device memory. The twelfth-order test also had a checked memory plan (100.8 GB at its largest grid). These are resource records, not performance benchmarks. Run directories preserve source snapshots, dependency versions and raw field outputs. All failed scientific candidates remain in the record. [Independent raw-field audit](full_field_audit.json) reconstructs source programming, decoding and two-curl PDE residuals directly from saved fields.
"""
    (OUT/"EXTENDED.md").write_text(report)
    print(json.dumps({"designs":len(cases),"below_one_percent":len(passing),"best_two_grid_residual":best},indent=2))


if __name__=="__main__":
    main()
