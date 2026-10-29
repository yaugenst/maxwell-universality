#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Independently reconstruct source, decoder and curl-form residuals from raw fields."""
import argparse
from hashlib import sha256
import json
from pathlib import Path

import numpy as np
from threadpoolctl import threadpool_limits

from maxwell import Grid, bump, write_json


def audit(case):
    m=json.loads((case/"metadata.json").read_text())
    r=json.loads((case/"verification.json").read_text())
    saved=np.load(case/"verification_fields.npz")
    fields,probes,sources=saved["fields"],saved["probes"],saved["sources"]
    v=np.array(r["nominal_source_decoder_strengths"])
    alpha=r["alpha"]
    target=np.array(r["target"])
    source_error=float(np.linalg.norm(sources-alpha*probes*v)/np.linalg.norm(sources))
    decoded=alpha*np.diag(v)+v[:,None]*(probes.T@fields)
    expected=np.array(r["decoded_response_real"])+1j*np.array(r["decoded_response_imag"])
    decoder_error=float(np.linalg.norm(decoded-expected))
    equation_error=float(np.linalg.norm(target@decoded-np.eye(len(v)),2))
    cfg=m["config"]
    grid=Grid(cfg["lengths"],cfg["h"],cfg["order"],max_unknowns=400_000)
    ec=m["bloch_probe"]["ec"]
    eps=grid.flatten([7+ec-cfg["detuning"]+cfg["rho"]*sum(2**j*np.cos(np.pi*x) for j,x in enumerate(xyz))
                      +sum(strength*bump(xyz,center,cfg["radius"]) for strength,center in zip(r["strengths"],m["centers"]))
                      for xyz in grid.xyz])
    # Apply the two curls directly, rather than the factorized/assembled matrix
    # used by cuDSS and the original verification code.
    residual=grid.curl.T@(grid.curl@fields)-eps[:,None]*fields-sources
    relative=np.linalg.norm(residual,axis=0)/np.linalg.norm(sources,axis=0)
    lower=7+ec-cfg["detuning"]-7*cfg["rho"]
    upper=7+ec-cfg["detuning"]+7*cfg["rho"]+max(r["strengths"])/np.e
    assert source_error<1e-12
    assert decoder_error<1e-10
    assert abs(equation_error-r["worst_relative_equation_residual"])<1e-10
    assert max(relative)<1e-8
    assert lower>=1 and upper<=25
    return {"case":str(case),"unknowns":grid.size,"source_reconstruction_error":source_error,
            "decoder_reconstruction_error":decoder_error,"raw_equation_operator_residual":equation_error,
            "independent_two_curl_relative_residuals":relative.tolist(),
            "continuous_material_enclosure":[lower,upper]}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--results",type=Path,default=Path("results"))
    p.add_argument("--groups",nargs="+",default=["direct_refinement_a","direct_refinement_b","spectral_refinement","order12_refinement"])
    p.add_argument("--output",type=Path,default=Path("report/full_field_audit.json"))
    args=p.parse_args()
    rows=[]
    with threadpool_limits(2):
        for group in args.groups:
            for design in json.loads((args.results/group/"summary.json").read_text()):
                h=design["verification"][-1]["h"]
                rows.append(audit(args.results/group/design["name"]/f"h{h:.8g}"))
                print(json.dumps(rows[-1]),flush=True)
    snapshots=0
    for meta in args.results.rglob("metadata.json"):
        data=json.loads(meta.read_text())
        source=meta.with_name("executed_source.py")
        if source.exists():
            assert sha256(source.read_bytes()).hexdigest()==data["code_sha256"],str(meta)
            snapshots+=1
    write_json(args.output,{"audited_finest_fields":rows,"source_snapshot_hashes_checked":snapshots,
                            "scope":"Independent replay of raw-field algebra and two-curl residuals at finite grids. No continuum error certificate or theorem verification."})


if __name__=="__main__":
    main()
