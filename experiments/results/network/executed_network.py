#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Six-defect, three-terminal full-vector Maxwell matrix programming experiment."""
import argparse
from dataclasses import replace
from hashlib import sha256
import json
from pathlib import Path
import time

import numpy as np
from scipy.linalg import eigh, solve
from scipy.optimize import least_squares
from threadpoolctl import threadpool_limits

from device import frozen_probes, verify_device
from maxwell import Config, Experiment, solve_system, write_json


def prepare(spec, output):
    start = time.perf_counter()
    ex = Experiment(Config(**spec["config"]), output)
    a, _, _, upper = ex.operator(np.zeros(len(ex.centers)))
    indices = [np.flatnonzero(w > 0) for w in ex.edge_wells]
    offsets = np.r_[0, np.cumsum([len(i) for i in indices])]
    all_indices = np.concatenate(indices)
    q = np.sqrt(np.concatenate([w[i] for w,i in zip(ex.edge_wells, indices)]))
    rhs = np.zeros((ex.grid.size, len(q)), order="F")
    rhs[all_indices, np.arange(len(q))] = q
    fields, info = solve_system(a, rhs, ex.config.solver)
    residual = np.linalg.norm(a@fields-rhs)/np.linalg.norm(rhs)
    s = q[:,None]*fields[all_indices]
    symmetry = np.linalg.norm(s-s.T)/np.linalg.norm(s)
    if max(residual, symmetry) > 1e-8:
        raise RuntimeError("Background compressed resolvent failed its independent residual check")
    s = (s+s.T)/2
    minimum_inverse = 1/((25-upper)*np.e)
    u = np.zeros((len(q), len(ex.centers)))
    eigenvalues = []
    for site in range(len(ex.centers)):
        lo,hi = offsets[site:site+2]
        vals, vecs = eigh(s[lo:hi,lo:hi])
        admissible = np.flatnonzero(vals > minimum_inverse)
        if not len(admissible):
            raise RuntimeError(f"No admissible local mode at site {site}")
        overlaps = vecs[:,admissible].T@ex.b[indices[site],site]
        selected = int(np.argmax(abs(overlaps)))
        u[lo:hi,site] = vecs[:,admissible[selected]]*np.sign(overlaps[selected])
        eigenvalues.append(vals[admissible[selected]])
    probes = rhs@u
    background_modes = fields@u
    np.savez(output/"background.npz", compressed=s, modes=u, offsets=offsets, indices=all_indices,
             eigenvalues=eigenvalues, background_modes=background_modes, probes=probes)
    summary = {"background_relative_solve_residual": float(residual), "symmetry_error": float(symmetry),
               "minimum_inverse_strength": float(minimum_inverse), "eigenvalues": eigenvalues,
               "projected_background": (u.T@s@u).tolist(), "compressed_dimension": len(q),
               "wall_seconds": time.perf_counter()-start, **info}
    write_json(output/"background.json", summary)
    print(json.dumps({"stage": "background", **summary}), flush=True)


def calibrate(spec, model, background, target, destination):
    destination.mkdir(parents=True, exist_ok=False)
    s, u, offsets = model["compressed"], model["modes"], model["offsets"]
    gamma = np.asarray(target["matrix"], float)
    terminals = spec["terminals"]
    ut = u[:,terminals]
    projected = u.T@s@u
    lower = background["minimum_inverse_strength"]*(1+1e-8)
    useful = []
    for i,j,k in spec["edges"]:
        useful.append(abs(projected[i,k]*projected[j,k]/gamma[i,j])/(projected[k,k]-lower))
    alpha = 2*max(useful)
    initial = np.diag(projected).copy()
    initial[terminals] += alpha*np.diag(gamma)
    for i,j,k in spec["edges"]:
        diagonal = -projected[i,k]*projected[j,k]/(alpha*gamma[i,j])
        initial[k] += diagonal
        initial[i] += projected[i,k]**2/diagonal
        initial[j] += projected[j,k]**2/diagonal
    # Material constraints apply to the full continuous coefficient, not samples.
    initial = np.maximum(initial, lower+.001)
    row, col = np.triu_indices(len(gamma))
    weights = np.where(row==col, 1., np.sqrt(2.))
    history=[]
    cache={}
    start=time.perf_counter()

    def evaluate(p):
        if "p" in cache and np.array_equal(p,cache["p"]):
            return cache["residual"], cache["jacobian"]
        t=-s.copy()
        t.flat[::len(t)+1] += np.repeat(p,np.diff(offsets))
        response=solve(t,ut,assume_a="sym",check_finite=False,overwrite_a=True)
        k=np.linalg.inv(ut.T@response)
        discrepancy=k/alpha-gamma
        residual=weights*discrepancy[row,col]
        jac=np.empty((len(row),len(p)))
        for site in range(len(p)):
            lo,hi=offsets[site:site+2]
            derivative=k@(response[lo:hi].T@response[lo:hi])@k/alpha
            jac[:,site]=weights*derivative[row,col]
        history.append({"evaluation":len(history),"inverse_strengths":p.tolist(),
                        "relative_matrix_error":float(np.linalg.norm(discrepancy)/np.linalg.norm(gamma))})
        if len(history)%5==1:
            print(json.dumps({"target":target["name"],**history[-1]}),flush=True)
        cache.update(p=p.copy(),residual=residual,jacobian=jac)
        return residual,jac

    fit=least_squares(lambda p:evaluate(p)[0],initial,jac=lambda p:evaluate(p)[1],
                      bounds=(lower,np.inf),x_scale="jac",ftol=1e-11,xtol=1e-11,
                      gtol=1e-10,max_nfev=60)
    residual,_=evaluate(fit.x)
    relative=float(np.linalg.norm(residual)/np.linalg.norm(gamma))
    result={"target":gamma.tolist(),"name":target["name"],"alpha":float(alpha),
            "target_condition":float(np.linalg.cond(gamma)),"strengths":(1/fit.x).tolist(),
            "relative_calibration_matrix_error":relative,"accepted":relative<1e-7,
            "optimizer_message":fit.message,"history":history,"wall_seconds":time.perf_counter()-start,
            "calibration_scope":"Full-support finite-cavity inverse design. Every defect coordinate and every pair interaction retained. Same background calibration reused for each predeclared target."}
    write_json(destination/"calibration.json",result)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--spec",type=Path,default=Path(__file__).with_name("network_targets.json"))
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--background",type=Path,help="Reuse an already computed background directory")
    parser.add_argument("--targets",nargs="+")
    args=parser.parse_args()
    spec=json.loads(args.spec.read_text())
    args.output.mkdir(parents=True,exist_ok=False)
    (args.output/"spec.json").write_bytes(args.spec.read_bytes())
    hashes={}
    for source in (Path(__file__),Path(__file__).with_name("maxwell.py"),Path(__file__).with_name("device.py")):
        contents=source.read_bytes()
        (args.output/f"executed_{source.name}").write_bytes(contents)
        hashes[source.name]=sha256(contents).hexdigest()
    write_json(args.output/"source_sha256.json",hashes)
    with threadpool_limits(2):
        background_path=args.background or args.output/"background"
        if args.background is None:
            prepare(spec,background_path)
        model=np.load(background_path/"background.npz")
        background=json.loads((background_path/"background.json").read_text())
        source_config=Config(**json.loads((background_path/"metadata.json").read_text())["config"])
        if source_config!=Config(**spec["config"]):
            raise ValueError("Reused background must match the fixed experiment configuration")
        reference=Experiment(source_config,args.output/"source_reference")
        rows=[]
        for target in spec["targets"]:
            if args.targets and target["name"] not in args.targets:
                continue
            result=calibrate(spec,model,background,target,args.output/target["name"])
            rows.append(result)
            write_json(args.output/"summary.json",rows)
            if not result["accepted"]:
                print(json.dumps({"stage":"calibration_failed","target":target["name"],
                                  "relative_error":result["relative_calibration_matrix_error"]}),flush=True)
                continue
            checks=[]
            for h in [source_config.h,*spec["verification_h"]]:
                ex=Experiment(replace(source_config,h=h),args.output/target["name"]/f"h{h:.8g}")
                probes=frozen_probes(ex,reference,model["background_modes"],model["eigenvalues"])
                measured=verify_device(ex,probes,np.array(result["strengths"]),result["alpha"],
                                       np.array(target["matrix"]),spec["terminals"])
                checks.append(measured)
                print(json.dumps({"stage":"verification","target":target["name"],**measured}),flush=True)
            result["verification"]=checks
            write_json(args.output/"summary.json",rows)


if __name__=="__main__":
    main()
