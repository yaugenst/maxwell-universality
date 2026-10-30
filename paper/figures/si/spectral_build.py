# /// script
# requires-python = ">=3.11"
# dependencies = ["matplotlib==3.10.8", "numpy==2.4.1"]
# ///
"""Render FIG-2/3 from exact saved data; optionally refresh from frozen sources.

    uv run --script figures/si/spectral_build.py
    uv run --script figures/si/spectral_build.py --refresh-from ROOT

The first command needs only the bundled data. The second extracts exact data
from the original research directory ROOT (with its ``work/``, ``verification/``
and ``snapshot/`` trees, which the companion archives do not reproduce),
verifies source bindings and rational inequalities, then renders. Neither command modifies research evidence or executes the matrix
verifiers. Exact rational computations precede conversion to display floats.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
from itertools import product
import json
import os
from pathlib import Path

for variable in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[variable] = "1"

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection
from matplotlib.patches import Circle, Ellipse, FancyArrowPatch, Patch
import numpy as np

HERE = Path(__file__).resolve().parent
BLUE = "#28658b"
PALE_BLUE = "#d4e5ef"
ORANGE = "#bc642e"
PALE_ORANGE = "#f0c7a6"
GREEN = "#42866c"
PALE_GREEN = "#bcdccd"
INK = "#202e3b"
GREY = "#65717c"
LABELS = ("L++-", "L+++", "L-++", "L+-+")
TEX_LABEL = {k: r"$\mathrm{L}_{" + k[1:] + "}$" for k in LABELS}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def extract(root):
    manifest = {}

    def read(relative):
        p = root / relative
        manifest[relative] = digest(p)
        return json.loads(p.read_text())

    material = read("results/defects/inversion_edge_material.json")
    proposals = read("work/bulk/global_certificate/cover_proposals.json")
    audit = read("verification/final_evidence_audit.json")
    run = "verification/final_clean_all_dependencies_retry/"
    inputs = read(run + "input_manifest.json")
    assert manifest[run + "input_manifest.json"] == audit["input_manifest_sha256"]

    def accepted(relative):
        d = read(run + relative)
        assert manifest[run + relative] == audit["output_sha256"][relative]
        return d

    geometry = accepted("snapshot/artifacts/global_atomic/geometry_acceptance.json")
    point = accepted("snapshot/artifacts/inversion_point_residuals.json")
    local = read("results/main/local_edge_scalar_acceptance.json")
    accepted("snapshot/work/bulk/edge_isolation/uniform_local_isolation_acceptance.json")
    curvature = {}
    for suffix in ("lppm", "lppp", "lmpp", "lpmp"):
        c = accepted(f"snapshot/artifacts/curvature_gram_{suffix}.json")
        assert c["status"] == "PASS" and c["material_matches_common_exact_integer_candidate"]
        curvature[suffix] = {
            k: c[k] for k in ("point_primitive_k_twice", "full_quadratic_residual_gram_relative_constant",
                              "feshbach_hessian_upper_bound", "relative_gram_ldl_pivots", "ldl_pivots")
        }
    for relative in ("results/main/global_edge_assembly_audit.md",
                     "results/main/local_edge_polynomial_lemma.md",
                     "results/main/composition_audit.md",
                     "results/main/discrete_edge_green_lemma.md",
                     "results/defects/exact_edge_arithmetic.py"):
        manifest[relative] = digest(root / relative)
    assert audit["all_22_required_jobs_passed"] and audit["all_staged_and_current_inputs_match"]
    assert audit["atomic_receipt_counts"]["global_atomic"] == 2056
    assert geometry["proposal_sha256"] == manifest["work/bulk/global_certificate/cover_proposals.json"]
    assert geometry["pending"] == geometry["uncovered"] == 0
    assert geometry["status"] == "EXACT_COVER_AND_ANALYTIC_COMPARATOR_PASS"
    assert point["status"] == "PASS" and point["material_matches_canonical_full_integer_table"]
    for relative,sha256 in manifest.items():
        if relative in inputs["files"]:
            assert sha256 == inputs["files"][relative]["sha256"], relative

    p = material["full_conventional_perturbation_numerators"]
    assert material["period"] == 20 and material["perturbation_denominator"] == 2**21
    assert material["primitive_perturbation_numerators"] == [p[x][y][z] for x,y,z in product(range(20),range(10),range(10))]

    def base_cell(r):
        # Identical doubled-cell closed-ball convention as exact_edge_arithmetic.py.
        center = tuple(2*a+1 for a in r)
        for fcc in ((0,0,0), (0,20,20), (20,0,20), (20,20,0)):
            for offset in (-5,5):
                delta = [(center[j]-fcc[j]-offset+20) % 40-20 for j in range(3)]
                if sum(a*a for a in delta) <= 100:
                    return 12
        return 1

    values = []
    for r in product(range(20), repeat=3):
        value = p[r[0]][r[1]][r[2]]
        assert isinstance(value,int) and 0 <= value <= 2046
        inv = tuple((-a-1) % 20 for a in r)
        assert value == p[inv[0]][inv[1]][inv[2]]
        for tr in ((0,10,10),(10,0,10),(10,10,0)):
            s = tuple((r[j]+tr[j]) % 20 for j in range(3))
            assert value == p[s[0]][s[1]][s[2]]
        values.append(F(base_cell(r)) + F(value,2**21))
    z_index = 4
    cells = [[str(F(base_cell((x,y,z_index))) + F(p[x][y][z_index],2**21)) for x in range(20)] for y in range(20)]
    boxes = []
    for group,key in (("matrix","accepted"),("gamma","analytic_gamma_boxes"),("L_ball","excluded_L_boxes")):
        for item in proposals[key]:
            if group == "matrix":
                center,halfwidth,depth = item["center"], item["halfwidth"], item["depth"]
            else:
                center,halfwidth,depth = item
            b = {"class":group,"center":[str(F(c)) for c in center],"halfwidth":str(F(halfwidth)),"depth":depth}
            if group == "matrix":
                b["witness"] = item["witness"]
            boxes.append(b)
    return {
        "schema_version":1,
        "scope":"Exact display data from the frozen accepted release; no new spectral computation or instantiated defect.",
        "source_root_hint":"../maxwell_sparse_reduction",
        "source_sha256":manifest,
        "accepted_run_summary_sha256":audit["run_summary_sha256"],
        "material":{
            "period":20,"primitive_basis":material["primitive_basis"],
            "formula":"epsilon(c)=epsilon_0(c)+p_c/2^21, epsilon_0 in {1,12}",
            "cell_base_rule":material["cell_base_rule"],
            "perturbation_denominator":2**21,"perturbation_numerator_bound":[0,2046],
            "actual_full_cell_range":[str(min(values)),str(max(values))],
            "slice_z_cell_index":z_index,"slice_z_cell_center":"9/2",
            "slice_array_order":"rows=y, columns=x; cell (x,y,4) occupies [x,x+1] x [y,y+1]",
            "slice_epsilon_exact":cells,
        },
        "coordinates":{
            "cartesian_reciprocal":"kappa; Bloch phase for translation R is exp(2 pi i kappa dot R/20)",
            "primitive_reciprocal_lattice":"integer triples with all coordinates of the same parity",
            "voronoi_zone":"abs(kappa_j)<=1 and sum(abs(kappa_j))<=3/2",
            "canonical_wedge":"0<=kappa_z<=kappa_y<=kappa_x<=1 and sum(kappa)<=3/2",
            "cover_slice":"(kappa_x,kappa_y,kappa_z)=(x,u,u)",
            "primitive_phase_coordinates":"(kappa_x,(kappa_x+kappa_y)/2,(kappa_x+kappa_z)/2)",
            "conventional_radian_coordinates":"k=2 pi kappa, modulo 2 pi Z^3",
            "L_representatives":{"L+++":['1/2','1/2','1/2'],"L++-":['1/2','1/2','-1/2'],"L+-+":['1/2','-1/2','1/2'],"L-++":['-1/2','1/2','1/2']},
        },
        "spectral":{
            "energy_operator":"H_p(kappa)=C(kappa)^*C(kappa)-diag(edge_average(epsilon))/64",
            "point_intervals":{label:[entry["interval_exact"] for entry in records] for label,records in point["points"].items()},
            "point_primitive_k_twice_modulo_2":{label:records[0]["primitive_k_twice_modulo_2"] for label,records in point["points"].items()},
            "local_radius":local["radius"],"quadratic_coefficient":local["band_coercivity_target"],
            "certified_quadratic_coefficient_lower":local["band_coercivity_lower"],
            "curvature_acceptance":curvature,
            "center_gap_lower":point["gap_to_other_L_lower_branches_lower_bound"],
            "center_gap_exact":point["gap_to_other_L_lower_branches_exact"],
            "selected_center_upper":point["lowest_L_value_upper_bound"],
            "outside_lower":geometry["analytic_comparator"]["perturbed_positive_band_threshold"],
            "outside_gap_lower":"1/500000", "shift":"157/16384","sigma":"1/16777216","rho":"1023/67108864",
            "display_energy_reference":"956519/100000000",
        },
        "cover":{"counts":geometry["counts"],"boxes":boxes,"pending":0,"uncovered":0,
                 "proposal_sha256":geometry["proposal_sha256"],
                 "classification":"Independent exact polytope/tree acceptance plus the separately replayed 2056 matrices; 1449 infeasible leaves omitted."},
    }


def clip_polygon(poly, a, b, bound):
    result=[]
    for p,q in zip(poly,poly[1:]+poly[:1]):
        vp=a*p[0]+b*p[1]-bound
        vq=a*q[0]+b*q[1]-bound
        if vp <= 0:
            result.append(p)
        if (vp < 0 < vq) or (vq < 0 < vp):
            t=vp/(vp-vq)
            result.append((p[0]+t*(q[0]-p[0]),p[1]+t*(q[1]-p[1])))
    return result


def polygon_area(poly):
    return abs(sum(p[0]*q[1]-q[0]*p[1] for p,q in zip(poly,poly[1:]+poly[:1])))/2


def cover_slice(data):
    polygons={"matrix":[],"gamma":[],"L_ball":[]}
    seen=set()
    for box in data["cover"]["boxes"]:
        c=list(map(F,box["center"]));h=F(box["halfwidth"])
        lo=[x-h for x in c];hi=[x+h for x in c]
        bottom=max(lo[1:]);top=min(hi[1:])
        if bottom >= top:
            continue
        poly=[(lo[0],bottom),(hi[0],bottom),(hi[0],top),(lo[0],top)]
        for a,b,d in ((-1,0,0),(1,0,1),(0,-1,0),(-1,1,0),(1,2,F(3,2))):
            poly=clip_polygon(poly,F(a),F(b),F(d))
        if not poly or not polygon_area(poly):
            continue
        # Exact clipping may repeat vertices on a closed polytope face.
        key=tuple(sorted(set(poly)))
        if key not in seen:
            seen.add(key)
            polygons[box["class"]].append(poly)
    area=sum(polygon_area(p) for group in polygons.values() for p in group)
    assert area == F(5,16), f"slice area mismatch: {area}"
    return polygons


def verify(data):
    s=data["spectral"]
    intervals={label:[tuple(map(F,p)) for p in pairs] for label,pairs in s["point_intervals"].items()}
    selected=intervals["L++-"][0]
    for label,pairs in intervals.items():
        assert pairs[0][0]<pairs[0][1]<pairs[1][0]<pairs[1][1]
        for lo,hi in pairs:
            assert (hi-lo)/2 <= F(1,2**47)
        if label != "L++-":
            assert pairs[0][0]-selected[1] > F(s["center_gap_lower"])
    margin=min(intervals[k][0][0] for k in LABELS if k!="L++-")-selected[1]
    assert all(intervals[left][0][1]<intervals[right][0][0] for left,right in zip(LABELS,LABELS[1:]))
    assert margin == F(s["center_gap_exact"])
    assert selected[1]<F(s["selected_center_upper"])
    assert F(s["outside_lower"]) == F(s["shift"])+F(s["sigma"])-F(s["rho"])
    assert F(s["outside_lower"])-F(s["selected_center_upper"])>F(s["outside_gap_lower"])
    assert F(s["certified_quadratic_coefficient_lower"])>F(s["quadratic_coefficient"])==F(1,600)
    for c in s["curvature_acceptance"].values():
        assert all(F(p)>0 for key in ("relative_gram_ldl_pivots","ldl_pivots") for p in c[key])
    for label,coords in data["coordinates"]["L_representatives"].items():
        x,y,z=map(F,coords)
        twice=(2*x,x+y,x+z)
        assert [int(v)%2 for v in twice] == s["point_primitive_k_twice_modulo_2"][label]
    counts={k:0 for k in ("matrix","gamma","L_ball")}
    for box in data["cover"]["boxes"]:
        counts[box["class"]]+=1
        h=F(box["halfwidth"]);c=list(map(F,box["center"]))
        assert h==F(1,2**(box["depth"]+1))
        if box["class"]=="L_ball":
            assert sum(max((x-h-F(1,2))**2,(x+h-F(1,2))**2) for x in c)<=F(s["local_radius"])**2
        elif box["class"]=="gamma":
            assert max(x+h for x in c)<=F(1,8)
    assert counts=={k:data["cover"]["counts"][k] for k in counts}
    assert counts=={"matrix":2056,"L_ball":660,"gamma":1}
    polygons=cover_slice(data)
    return {
        "status":"PASS_FIGURE_DATA_AND_EXACT_COMPARISONS",
        "scope":"Figure extraction, coordinate transforms, exact scalar comparisons and slice-area audit; not a new full matrix replay.",
        "data_sha256":digest(HERE/"spectral_data.json"),
        "minimum_center_interval_gap":str(margin),
        "center_gap_strictly_above":"33/1000000000",
        "outside_minus_selected_upper":str(F(s["outside_lower"])-selected[1]),
        "outside_minus_named_selected_upper":str(F(s["outside_lower"])-F(s["selected_center_upper"])),
        "outside_gap_strictly_above":"1/500000",
        "quadratic_coefficient_strictly_above":"1/600",
        "all_local_boxes_wholly_inside_radius":"1/20",
        "slice_polygon_counts":{k:len(v) for k,v in polygons.items()},
        "canonical_slice_total_area":"5/16",
        "source_classification_counts":counts,
    },polygons


def title(ax,text):
    ax.set_title(text,loc="left",fontsize=9.5,fontweight="bold",pad=9)


def clean(ax):
    ax.spines[["top","right"]].set_visible(False)
    ax.tick_params(length=3,color=GREY)


def save(fig,name):
    # Preserve the 160 mm media width: no tight-bbox rescaling on inclusion.
    fig.savefig(HERE/(name+".pdf"),metadata={"CreationDate":None,"ModDate":None})
    fig.savefig(HERE/(name+".png"),dpi=240)
    plt.close(fig)


def setting(data):
    fig=plt.figure(figsize=(160/25.4,5.55))
    ax=fig.add_axes([.09,.525,.32,.365]);title(ax,"a  Exact scalar background")
    cells=np.array([[float(F(v)) for v in row] for row in data["material"]["slice_epsilon_exact"]])
    im=ax.imshow(cells,origin="lower",extent=(0,20,0,20),cmap="YlGnBu",vmin=1,vmax=12.001,interpolation="none")
    ax.set_xticks([0,10,20]);ax.set_yticks([0,10,20])
    ax.set_xlabel("Cell coordinate $r_1$ (unit cells)");ax.set_ylabel("Cell coordinate $r_2$")
    ax.text(.02,.98,"$r_3=4$ cell layer",transform=ax.transAxes,va="top",fontsize=8,
            bbox={"facecolor":"white","edgecolor":"none","alpha":.92,"pad":3})
    cb=fig.colorbar(im,cax=fig.add_axes([.10,.405,.30,.023]),orientation="horizontal")
    cb.set_ticks([1,12]);cb.set_label(r"$\varepsilon_0(c)+p_c/2^{21}$, $\varepsilon_0(c)\in\{1,12\}$",fontsize=8)

    ax=fig.add_axes([.62,.525,.35,.365]);title(ax,"b  Certified positive doublets")
    s=data["spectral"];ref=F(s["display_energy_reference"])
    for y,label in enumerate(LABELS):
        for band,color in ((0,BLUE),(1,ORANGE)):
            lo,hi=map(F,s["point_intervals"][label][band])
            center=float(((lo+hi)/2-ref)*10**9)
            err=float((hi-lo)/2*10**9)
            ax.errorbar(center,y,xerr=err,fmt="|",markersize=13,markeredgewidth=1.6,
                        capsize=4,color=color,zorder=4)
    ax.set_yticks(range(4),[TEX_LABEL[k] for k in LABELS]);ax.invert_yaxis()
    ax.set_xlim(-2,207);ax.set_ylim(3.7,-.55)
    ax.set_xticks([0,100,200])
    ax.set_xlabel(r"$10^9(\lambda-0.00956519)$",fontsize=8.5)
    ax.text(.03,.03,"Interval radii ≤ $2^{-47}$",transform=ax.transAxes,fontsize=7.5,color=GREY)
    ax.plot([],[],"|",color=BLUE,markersize=11,label="Lower positive band")
    ax.plot([],[],"|",color=ORANGE,markersize=11,label="Second positive band")
    ax.legend(loc="upper left",bbox_to_anchor=(0,-.22),frameon=False,fontsize=8,handlelength=1)
    ax.grid(axis="x",alpha=.14);clean(ax)

    ax=fig.add_axes([.07,.035,.9,.215]);title(ax,"c  Terminal–mediator mechanism (schematic)")
    ax.set_xlim(0,1);ax.set_ylim(0,1);ax.axis("off")
    for x,label,color in ((.075,"Terminal",BLUE),(.27,"Mediator",ORANGE),(.465,"Terminal",BLUE)):
        ax.add_patch(Ellipse((x,.59),.063,.29,facecolor="white",edgecolor=color,lw=1.5,hatch="///"))
        ax.text(x,.30,label,ha="center",fontsize=8)
    for left,right in ((.112,.232),(.308,.428)):
        ax.annotate("",xy=(right,.59),xytext=(left,.59),arrowprops={"arrowstyle":"<->","color":BLUE,"lw":1.4})
        ax.text((left+right)/2,.68,r"$\beta_j$",ha="center",fontsize=9)
    ax.text(.27,.06,r"$\Theta_{ee}=-\beta_j^2/\alpha$",ha="center",fontsize=9)
    ax.add_patch(FancyArrowPatch((.075,.75),(.465,.75),connectionstyle="arc3,rad=-.16",arrowstyle="-",linestyle="--",color=GREY,lw=1))
    ax.text(.27,.96,"unwanted direct interaction",ha="center",fontsize=7.5,color=GREY)
    ax.text(.77,.82,r"$-\beta_j^2/\Theta_{ee}=\alpha$",ha="center",fontsize=10,color=BLUE)
    ax.text(.77,.48,r"$|u^T G(dBe_j)u|\geq c_{\rm d} a_{\rm d}^d$, $d\geq d_0$",ha="center",fontsize=8.5)
    ax.text(.77,.18,r"$\|G(B\nu)\|\leq C_{\rm d}r_{\rm d}^{\|\nu\|_1}$,  $r_{\rm d}^2<a_{\rm d}$",ha="center",fontsize=8.5)
    save(fig,"spectral_setting")


def draw_cover(ax,polygons):
    for group,color in (("matrix",PALE_BLUE),("gamma",PALE_GREEN),("L_ball",PALE_ORANGE)):
        p=[[(float(x),float(y)) for x,y in poly] for poly in polygons[group]]
        ax.add_collection(PolyCollection(p,facecolors=color,edgecolors="white",linewidths=.28))
    boundary=np.array([[0,0],[1,0],[1,.25],[.5,.5],[0,0]])
    ax.plot(boundary[:,0],boundary[:,1],color=INK,lw=.85)
    # |q|^2=(x-1/2)^2+2(u-1/2)^2 on this Cartesian-coordinate slice.
    ax.add_patch(Ellipse((.5,.5),.1,.1/np.sqrt(2),fill=False,edgecolor=ORANGE,linestyle="--",lw=1))
    clean(ax)


def certification(data,polygons):
    fig=plt.figure(figsize=(160/25.4,6.05))
    ax=fig.add_axes([.10,.60,.36,.31]);title(ax,"a  Reciprocal-domain cover")
    draw_cover(ax,polygons)
    ax.set_xlim(-.02,1.02);ax.set_ylim(-.01,.58)
    ax.set_xlabel(r"$\tilde k_x$");ax.set_ylabel(r"$s^\prime=\tilde k_y=\tilde k_z$")
    ax.set_xticks([0,.5,1]);ax.set_yticks([0,.25,.5])
    ax.text(.083,.028,r"$\mathrm{\Gamma}$",fontsize=10,color=GREEN)
    ax.plot([.5],[.5],"o",ms=3,color=ORANGE)
    ax.text(.33,.53,r"$\mathrm{L}_{+++}$",fontsize=8,color=ORANGE)
    inset=ax.inset_axes([.60,.54,.39,.40]);draw_cover(inset,polygons)
    inset.set_xlim(.46,.55);inset.set_ylim(.455,.513)
    inset.set_xticks([.475,.525]);inset.set_yticks([]);inset.tick_params(labelsize=7.5,length=2)
    inset.set_title(r"$\mathrm{L}$ detail",fontsize=7.5,pad=3)
    handles=[Patch(facecolor=PALE_BLUE,label="2056 global matrix boxes"),Patch(facecolor=PALE_ORANGE,label="660 local-ball leaves"),Patch(facecolor=PALE_GREEN,label=r"1 analytic $\mathrm{\Gamma}$ leaf")]
    ax.legend(handles=handles,loc="upper center",bbox_to_anchor=(.5,-.23),ncol=1,frameon=False,fontsize=7.5,handlelength=1.2)

    ax=fig.add_axes([.64,.60,.32,.31]);title(ax,"b  Quadratic lower bound")
    r=np.linspace(0,.05,250)
    bound=r*r/600*10**6
    ax.fill_between(r,bound,5.4,color=PALE_BLUE,alpha=.6)
    ax.plot(r,bound,color=BLUE,lw=1.9)
    ax.plot([0],[0],"o",color="white",markeredgecolor=BLUE,ms=5)
    ax.set_xlim(0,.05);ax.set_ylim(0,5.4)
    ax.set_xticks([0,.025,.05],["0","0.025","0.05"]);ax.set_yticks([0,2,4])
    ax.set_xlabel(r"$\|q\|_2$ (Cartesian $\tilde k$)")
    ax.set_ylabel(r"$10^6[\lambda_{\rm low}(L+q)-E_{\rm L}]$")
    ax.text(.002,4.8,r"All four $L$ neighborhoods",fontsize=8.5,color=BLUE)
    ax.text(.002,3.75,r"Rise $>\|q\|_2^2/600$"+"\n"+r"for $0<\|q\|_2\leq1/20$",fontsize=8.5)
    ax.grid(alpha=.15);clean(ax)

    s=data["spectral"];ref=F(s["display_energy_reference"])
    ax=fig.add_axes([.10,.12,.36,.27]);title(ax,"c  Strict center comparison")
    for y,label in enumerate(LABELS):
        lo,hi=map(F,s["point_intervals"][label][0])
        center=float(((lo+hi)/2-ref)*10**9);err=float((hi-lo)/2*10**9)
        color=ORANGE if label=="L++-" else BLUE
        ax.errorbar(center,y,xerr=err,fmt="|",markersize=14,markeredgewidth=2,capsize=4,color=color)
    ax.set_yticks(range(4),[TEX_LABEL[k] for k in LABELS]);ax.set_ylim(3.65,-.7);ax.set_xlim(0,98)
    ax.set_xticks([0,30,60,90])
    ax.set_xlabel(r"$10^9(\lambda-E_{\rm ref})$")
    ax.text(.02,.97,r"Center gap $>33\times10^{-9}$",transform=ax.transAxes,va="top",fontsize=8)
    ax.text(.02,.025,"Interval radii ≤ $2^{-47}$",transform=ax.transAxes,fontsize=7.5,color=GREY)
    ax.grid(axis="x",alpha=.15);clean(ax)

    ax=fig.add_axes([.64,.12,.32,.27]);title(ax,"d  Outside the local balls")
    selected=tuple(map(F,s["point_intervals"]["L++-"][0]))
    center=float(((selected[0]+selected[1])/2-ref)*10**6)
    outside=float((F(s["outside_lower"])-ref)*10**6)
    ax.axvspan(outside,3.2,color=PALE_BLUE,alpha=.8)
    ax.axvline(outside,color=BLUE,lw=1.7)
    ax.plot([center],[.26],marker="|",markersize=17,markeredgewidth=2,color=ORANGE)
    ax.text(center+.09,.26,r"$E_{\mathrm{L}_{++-}}$",va="center",fontsize=9,color=ORANGE)
    ax.text(.06,.80,r"$\lambda_{\rm positive}\geq642053/2^{26}$",fontsize=8.5,color=BLUE)
    ax.annotate("",xy=(outside,.51),xytext=(center,.51),arrowprops={"arrowstyle":"<->","color":INK,"lw":1.2})
    ax.text((center+outside)/2,.56,r"gap $>1/500000$",ha="center",fontsize=8.5)
    ax.set_xlim(-.08,3.2);ax.set_ylim(0,1);ax.set_yticks([])
    ax.set_xticks([0,1,2,3])
    ax.set_xlabel(r"$10^6(\lambda-E_{\rm ref})$")
    ax.spines[["top","right","left"]].set_visible(False)
    ax.text(.02,.05,r"Includes analytic $\mathrm{\Gamma}$",transform=ax.transAxes,fontsize=7.5,color=GREY)
    fig.text(.54,.025,r"$E_{\rm ref}=0.00956519$; panels c and d use different energy scales.",ha="center",fontsize=8)
    save(fig,"spectral_certification")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh-from",type=Path)
    args=parser.parse_args()
    if not __debug__:
        raise RuntimeError("Exact checks require assertions; do not use optimized Python.")
    if args.refresh_from:
        data=extract(args.refresh_from.resolve())
        (HERE/"spectral_data.json").write_text(json.dumps(data,indent=2)+"\n")
    else:
        data=json.loads((HERE/"spectral_data.json").read_text())
    checks,polygons=verify(data)
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":8.5,"axes.labelcolor":INK,
                         "text.color":INK,"axes.edgecolor":GREY,"xtick.color":GREY,
                         "ytick.color":GREY,"pdf.fonttype":42,"svg.fonttype":"none"})
    setting(data)
    certification(data,polygons)
    checks["rendering"]={"matplotlib":matplotlib.__version__,"numpy":np.__version__,"threads":1,
                         "native_width_mm":160,"minimum_font_points":7.5,
                         "setting_height_mm":5.55*25.4,"certification_height_mm":6.05*25.4}
    checks["output_sha256"]={name:digest(HERE/name) for name in ("spectral_setting.pdf","spectral_setting.png","spectral_certification.pdf","spectral_certification.png")}
    (HERE/"spectral_checks.json").write_text(json.dumps(checks,indent=2)+"\n")
    print(json.dumps({k:v for k,v in checks.items() if k not in ("output_sha256",)},indent=2))


if __name__ == "__main__":
    main()
