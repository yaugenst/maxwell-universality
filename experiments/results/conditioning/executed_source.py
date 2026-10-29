#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Numerical full-operator spectral conditioning, independently of terminal response."""
import argparse
import json
from pathlib import Path
import time

import numpy as np
from scipy.sparse.linalg import LinearOperator, eigsh
from threadpoolctl import threadpool_limits

from maxwell import Config, Experiment, write_json


def measure(case, output):
    from nvmath.sparse.advanced import DirectSolver
    start=time.perf_counter()
    original=json.loads((case/"verification.json").read_text())
    metadata=json.loads((case/"metadata.json").read_text())
    ex=Experiment(Config(**metadata["config"]),output)
    a,_,_,_=ex.operator(original["strengths"])
    if ex.config.absorption:
        raise ValueError("This symmetric eigenvalue diagnostic requires a real lossless material")
    rng=np.random.default_rng(20261029)
    top,top_vector=eigsh(a,k=1,which="LA",tol=1e-5,maxiter=1000,ncv=40,
                         v0=rng.standard_normal(len(a.indptr)-1))
    largest=float(top[0])
    largest_residual=float(np.linalg.norm(a@top_vector[:,0]-largest*top_vector[:,0]))
    solve_residuals=[]
    with DirectSolver(a.tocsr(),np.zeros((a.shape[0],1),order="F")) as solver:
        solver.plan()
        factor_info=solver.factorize()
        solver.solution_config.ir_num_steps=5
        def inverse(v):
            rhs=np.asfortranarray(np.asarray(v).reshape(-1,1))
            solver.reset_operands(b=rhs)
            field=solver.solve()[:,0]
            solve_residuals.append(float(np.linalg.norm(a@field-v)/np.linalg.norm(v)))
            return field
        op=LinearOperator(a.shape,matvec=inverse,rmatvec=inverse,dtype=float)
        inverse_values,vectors=eigsh(op,k=6,which="LM",tol=1e-8,ncv=24,maxiter=1000,
                                    v0=rng.standard_normal(a.shape[0]))
    applied=a@vectors
    values=np.sum(vectors*applied,axis=0)
    residuals=np.linalg.norm(applied-vectors*values,axis=0)
    saved=np.load(case/"verification_fields.npz")
    sources=saved["sources"]
    coupling=np.linalg.norm(sources.T@vectors,axis=0)/np.linalg.norm(sources,2)
    order=np.argsort(abs(values))
    rows=[{"rayleigh_eigenvalue":float(values[i]),"inverse_ritz_eigenvalue":float(1/inverse_values[i]),
           "absolute_eigen_residual":float(residuals[i]),"normalized_source_overlap":float(coupling[i])}
          for i in order]
    result={"case":str(case),"h":ex.config.h,"unknowns":ex.grid.size,
            "scope":"Uncertified finite-matrix spectral estimate using shift-invert Lanczos over the full electric space. Rayleigh quotients and absolute eigen-residuals are independently evaluated with the assembled Maxwell matrix. It is not a continuum or asymptotic condition bound.",
            "largest_eigenvalue":largest,"largest_eigen_residual":largest_residual,
            "nearest_eigenpairs":rows,"estimated_spectral_condition":largest/abs(values[order[0]]),
            "inverse_applications":len(solve_residuals),"maximum_inverse_solve_relative_residual":max(solve_residuals),
            "factor_nnz":int(factor_info.lu_nnz),"wall_seconds":time.perf_counter()-start}
    write_json(output/"conditioning.json",result)
    np.savez_compressed(output/"nearest_eigenvectors.npz",values=values,vectors=vectors,residuals=residuals)
    print(json.dumps(result),flush=True)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case",type=Path,nargs="+",required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    (args.output/"executed_source.py").write_bytes(Path(__file__).read_bytes())
    rows=[]
    with threadpool_limits(2):
        for index,case in enumerate(args.case):
            rows.append(measure(case,args.output/f"case_{index}"))
            write_json(args.output/"conditioning.json",rows)


if __name__=="__main__":
    main()
