#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["matplotlib==3.10.8", "numpy==2.4.2"]
# ///
"""Build and plot one exact logical example (SI Fig. S1).

Copy of maxwell_paper_draft/figures/logical_translation.py for the arXiv SI:
in-figure disclaimers removed (the caption carries the qualification); side
data files are written to $FIGS1_DATA_DIR (default: a temporary directory).

From the companion repository's paper directory:
uv run --script figures/si/logical_translation.py --certificate-root ../certificates/yee
The certificate root contains results/logical/verify_logical.py.
The only reference solve is the displayed two-variable rational input.  The
actual decoder below only selects, rounds, and scales coordinates.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as F
import gzip
import hashlib
import importlib.util
import json
from math import lcm, prod
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import FancyArrowPatch, Rectangle
import numpy as np

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--certificate-root", type=Path,
                    default=HERE.parents[2] / "certificates/yee",
                    help="Directory containing results/logical/verify_logical.py")
args = parser.parse_args()
CERTIFICATES = args.certificate_root.resolve()
import os, tempfile
DATA = Path(os.environ.get("FIGS1_DATA_DIR") or tempfile.mkdtemp())
CHECKER = CERTIFICATES / "results/logical/verify_logical.py"
spec = importlib.util.spec_from_file_location("logical_checker", CHECKER)
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)

NAVY = "#203b5b"
BLUE = "#257d9b"
ORANGE = "#c97230"
GREY = "#647180"
LIGHT = "#eaf0f4"
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                     "pdf.fonttype": 42, "ps.fonttype": 42,
                     "axes.spines.top": False, "axes.spines.right": False})


def encode_rows(rows):
    return [[[j, str(x)] for j, x in sorted(row.items()) if x] for row in rows]


def sparse_action(rows, vector):
    return [sum((x * vector[j] for j, x in row.items()), F(0)) for row in rows]


def path_inverse(rhs):
    """Exact T_(4j)^-1 rhs by the source proof's two recurrences."""
    n = len(rhs)
    assert n > 0 and n % 4 == 0
    x = [0] * (n + 2)
    for j in range(1, n, 2):
        x[j + 1] = int(rhs[j - 1]) - x[j - 1]
    for j in range(n, 1, -2):
        x[j - 1] = int(rhs[j - 1]) - x[j + 1]
    out = x[1:n + 1]
    assert all((out[j - 1] if j else 0) +
               (out[j + 1] if j + 1 < n else 0) == int(rhs[j])
               for j in range(n))
    return out


def corners(path):
    out = [path[0]]
    previous = tuple(b-a for a, b in zip(path[0], path[1]))
    for i in range(1, len(path)-1):
        direction = tuple(b-a for a, b in zip(path[i], path[i+1]))
        if direction != previous:
            out.append(path[i])
            previous = direction
    out.append(path[-1])
    assert verify.expand(out) == path
    return out


def build_example():
    matrix = [[F(2), F(-1)], [F(1), F(2)]]
    b = [F(1), F(0)]
    m, lam, beta, eta = 4, F(8), F(1), F(1, 4)
    normalized = [[x / lam for x in row] for row in matrix]
    g = [x / beta for x in b]
    # Every coefficient is already exactly dyadic.  Zero high-precision
    # Horner prefixes can be omitted without changing any represented entry.
    bits = 3
    K, L = 1, 4**2
    full_bits = 1
    while F(1, 2**full_bits) > eta/(64*m*L):
        full_bits += 1
    assert all((x * 2**full_bits).denominator == 1 for row in normalized for x in row)
    checked = verify.check_circuit(normalized, bits)
    gates, outputs, hrows = verify.circuit(normalized, bits)
    S = len(hrows)
    h = g + [F(0)] * len(gates)
    g0rows = [dict() for _ in range(2*S)]
    old_edges = []
    for i, row in enumerate(hrows):
        for j, weight in sorted(row.items()):
            g0rows[i][S+j] = weight
            g0rows[S+j][i] = weight
            old_edges.append((i, S+j, weight))
    U = 2*S+len(old_edges)
    gp = [dict() for _ in range(U)]
    positive_edges = []
    for e, (v, w, weight) in enumerate(old_edges):
        med = 2*S+e
        gp[med][med] = -1/weight
        for endpoint in (v, w):
            gp[endpoint][endpoint] = gp[endpoint].get(endpoint, F(0)) - weight
            gp[endpoint][med] = gp[med][endpoint] = F(1)
            positive_edges.append((endpoint, med))
    degrees = [sum(j != i for j in row) for i, row in enumerate(gp)]
    assert max(degrees) <= 3
    assert all(abs(row.get(i, 0)) <= 3 for i, row in enumerate(gp))
    assert all(x == 1 for i, row in enumerate(gp) for j, x in row.items() if j != i)
    # Exact Schur complement, including every diagonal cancellation.
    schur = [defaultdict(F, {i: gp[i].get(i, F(0))}) for i in range(2*S)]
    for e, (v, w, weight) in enumerate(old_edges):
        for a in (v, w):
            for c in (v, w):
                schur[a][c] += weight
    assert encode_rows(schur) == encode_rows(g0rows)

    x_reference = [F(2, 5), F(-1, 5)]
    assert sparse_action([{j: x for j, x in enumerate(row)} for row in matrix], x_reference) == b
    circuit_solution = [x * lam / beta for x in x_reference]
    for terms in gates:
        circuit_solution.append(sum((w * circuit_solution[i] for i, w in terms), F(0)))
    assert sparse_action(hrows, circuit_solution) == h
    old_solution = [F(0)] * S + circuit_solution
    gp_solution = old_solution + [w * (old_solution[v]+old_solution[t])
                                  for v, t, w in old_edges]
    gp_source = h + [F(0)] * (U-S)
    assert sparse_action(gp, gp_solution) == gp_source

    vertices, paths, q = verify.graph_paths([0]*(2*S) + [1]*len(old_edges), positive_edges)
    occupied = set(vertices.values())
    coords = [vertices[i] for i in range(U)]
    # All solution coordinates share this small denominator.  Path recurrences
    # only change signs, so no floating-point solve is needed at any stage.
    base_den = lcm(*(x.denominator for x in gp_solution))
    base_numer = [int(x*base_den) for x in gp_solution]
    edges = []
    route_records = []
    for e, path in paths.items():
        v, w = positive_edges[e]
        assert path[0] == vertices[v] and path[-1] == vertices[w]
        assert (len(path)-1) % 4 == 1 and len(path)-1 <= 1024*q
        assert len(path) == len(set(path))
        assert all(sum(abs(a-b) for a,b in zip(p,r)) == 1 for p,r in zip(path,path[1:]))
        start = len(coords)
        for k, point in enumerate(path[1:-1], 1):
            assert point not in occupied
            occupied.add(point)
            coords.append(point)
            base_numer.append((base_numer[w], -base_numer[v],
                               -base_numer[w], base_numer[v])[(k-1)%4])
        stop = len(coords)
        ids = [v] + list(range(start, stop)) + [w]
        edges.extend(zip(ids, ids[1:]))
        route_records.append({"edge": e, "endpoints": [v,w],
                              "internal_node_range": [start,stop],
                              "length": len(path)-1, "corners": corners(path)})
    coordinates = np.asarray(coords, dtype=np.int32)
    adjacency = np.asarray(edges, dtype=np.int32)
    diag2 = np.zeros(len(coords), dtype=np.int64)
    for i, row in enumerate(gp):
        diag2[i] = int(2*row.get(i, 0))
    gamma_degree = np.bincount(adjacency.ravel(), minlength=len(coords))
    assert gamma_degree.max() <= 3
    assert np.all(np.abs(coordinates[adjacency[:,0]]-coordinates[adjacency[:,1]]).sum(axis=1)==1)
    source = np.zeros(len(coords), dtype=np.int64)
    for i, value in enumerate(gp_source):
        assert value.denominator == 1
        source[i] = int(value)

    def action2(numer):
        assert int(np.max(np.abs(numer))) * 12 < 2**63
        result = diag2 * numer
        np.add.at(result, adjacency[:,0], 2*numer[adjacency[:,1]])
        np.add.at(result, adjacency[:,1], 2*numer[adjacency[:,0]])
        return result

    base_numer = np.asarray(base_numer, dtype=np.int64)
    assert np.array_equal(action2(base_numer), 2*base_den*source)
    # Perturb EVERY coordinate, including wire, mediator, and gate variables.
    # Common-denominator integer arithmetic makes the full residual exact.
    perturb_scale = 2**52
    denominator = base_den*perturb_scale
    indices = np.arange(len(coords),dtype=np.int64)
    perturbation = (indices%6+1)*np.where(indices%2==0,1,-1)
    assert np.all(perturbation != 0)
    perturbed = base_numer*perturb_scale + perturbation
    residual2 = action2(perturbed) - 2*denominator*source
    residual_norm2 = sum(int(x)**2 for x in residual2)
    ell = 1024*q
    t_res = 4*len(b)*((S+1)**2+1)*(1+2*ell)
    rho = eta/(16*t_res)
    assert F(residual_norm2, (2*denominator)**2) <= rho*rho
    # Eliminate arbitrary wire residuals, then mediators, then circuit gates.
    gp_residual2 = [int(x) for x in residual2[:U]]
    for route in route_records:
        start, stop = route["internal_node_range"]
        v, w = route["endpoints"]
        eliminated = path_inverse(residual2[start:stop])
        gp_residual2[v] -= eliminated[0]
        gp_residual2[w] -= eliminated[-1]
    rational_terminal = [F(int(x),denominator) for x in perturbed[:U]]
    expected_gp = [a-b for a,b in zip(sparse_action(gp,rational_terminal), gp_source)]
    assert all(F(r,2*denominator)==expected for r,expected in zip(gp_residual2,expected_gp))
    old_residual = [F(x,2*denominator) for x in gp_residual2[:2*S]]
    for e,(v,w,weight) in enumerate(old_edges):
        error=weight*F(gp_residual2[2*S+e],2*denominator)
        old_residual[v]+=error
        old_residual[w]+=error
    expected_old = sparse_action(g0rows,rational_terminal[:2*S])
    old_source = h+[F(0)]*S
    assert old_residual == [a-b for a,b in zip(expected_old,old_source)]
    propagated=[F(0)]*2
    for k,terms in enumerate(gates):
        propagated.append(old_residual[2+k]+sum((w*propagated[i] for i,w in terms),F(0)))
    transferred=[old_residual[i]-propagated[out] for i,out in enumerate(outputs)]
    selected = rational_terminal[S:S+2]
    normalized_residual=[sum((a*z for a,z in zip(row,selected)),F(0))-rhs
                         for row,rhs in zip(normalized,g)]
    assert transferred == normalized_residual
    assert sum(x*x for x in normalized_residual) <= t_res*t_res*F(residual_norm2,(2*denominator)**2)
    # The decoder proper: coordinate restriction, rounding, scalar rescaling.
    step=eta/(16*m)
    rounded=[((z/step+F(1,2)).numerator//(z/step+F(1,2)).denominator)*step for z in selected]
    decoded=[beta/lam*z for z in rounded]
    original_residual=[sum((a*x for a,x in zip(row,decoded)),F(0))-rhs
                       for row,rhs in zip(matrix,b)]
    assert sum(x*x for x in original_residual) <= eta*eta*sum(x*x for x in b)
    lo=coordinates.min(axis=0)
    hi=coordinates.max(axis=0)
    sites=hi-lo+1
    volume=prod(map(int,sites))
    labels=[]
    for i in range(U):
        if i<S:
            kind="output_equation" if i<2 else "gate_equation"
            label=f"output equation {i+1}" if i<2 else f"gate equation {i-1}"
        elif i<2*S:
            j=i-S
            kind="input_variable" if j<2 else "gate_variable"
            label=f"u{j+1}" if j<2 else f"w{j-1}"
        else:
            kind="sign_mediator"
            label=f"mediator {i-2*S}"
        labels.append({"id":i,"label":label,"kind":kind,"coordinate":list(vertices[i]),
                       "diagonal":str(gp[i].get(i,F(0))),"source":str(gp_source[i])})
    data={
        "schema":"one-exact-logical-compiler-example-v1",
        "checker_path":str(CHECKER.relative_to(CERTIFICATES)),
        "checker_sha256":hashlib.sha256(CHECKER.read_bytes()).hexdigest(),
        "matrix":[[str(x) for x in row] for row in matrix],"source":[str(x) for x in b],
        "normalized_matrix":[[str(x) for x in row] for row in normalized],
        "normalization":{"lambda":str(lam),"beta":str(beta),"m":m,"L":L,"eta":str(eta)},
        "dyadic_bits":bits,"full_precision_bits_sufficient_for_theorem":full_bits,
        "rounding_error":"0",
        "zero_prefix_note":"Exact coefficients use their shortest common dyadic representation; extra all-zero Horner prefixes are omitted. This is an exact finite example, not a timing implementation of the all-input theorem.",
        "H":encode_rows(hrows),"G0":encode_rows(g0rows),"Gplus":encode_rows(gp),
        "circuit_gates":[[[i,str(w)] for i,w in terms] for terms in gates],
        "circuit_outputs":outputs,"labels":labels,
        "wire_label_rule":"wire{edge}:{offset}, with offset 1 through path length minus 1; global index is route.internal_node_range[0]+offset-1",
        "Gplus_edges":[list(edge) for edge in positive_edges],
        "counts":{"S":S,"gate_count":len(gates),"H_nonzeros":checked["nonzeros"],
                  "Gplus_vertices":U,"Gplus_edges":len(positive_edges),"q":q,
                  "Gamma_vertices":len(coords),"Gamma_edges":len(edges),
                  "max_graph_degree":int(gamma_degree.max()),"min_path_length":min(len(p)-1 for p in paths.values()),
                  "max_path_length":max(len(p)-1 for p in paths.values()),
                  "lattice_min":lo.tolist(),"lattice_max":hi.tolist(),"box_sites":sites.tolist(),
                  "whole_box_lattice_sites":volume,"empty_lattice_sites":volume-len(coords)},
        "residual_check":{"method":"exact common-denominator integer sparse multiplication, exact path/gate elimination, and Fraction rounding",
                          "all_coordinates_perturbed":True,"perturbation_numerator_rule":"((global index mod 6)+1)*(-1)^(global index)",
                          "common_denominator":denominator,"residual_twice_denominator_squared_numerator":residual_norm2,
                          "logical_relative_residual_squared":str(F(residual_norm2,(2*denominator)**2)),
                          "rho":str(rho),"T_res":t_res,"ell":ell,
                          "exact_solution_substitution":"PASS", "all_residual_eliminations":"PASS",
                          "reference_solution":[str(x) for x in x_reference],
                          "decoder_grid":str(step),"decoded_solution":[str(x) for x in decoded],
                          "decoded_residual":[str(x) for x in original_residual],
                          "decoded_relative_residual_squared":str(sum(x*x for x in original_residual))},
        "physical_panel":{"status":"schematic only; fixed defect and coupling parameter search unexecuted",
                          "numerical_physical_cell_count":None,"whole_box_count":"Nx Ny Nz cells including buffers and empty cells"}}
    (DATA/"logical_translation_data.json").write_text(json.dumps(data,indent=2)+"\n")
    route_payload=json.dumps({"coordinate_convention":"unit cubic lattice; expand each axis-aligned corner segment into all unit steps",
                              "routes":route_records},separators=(",",":")).encode()
    (DATA/"logical_translation_routes.json.gz").write_bytes(gzip.compress(route_payload,mtime=0))
    np.savez_compressed(DATA/"logical_translation_network.npz",coordinates=coordinates,
                        undirected_unit_edges=adjacency,diagonal_twice=diag2,
                        source=source,exact_solution_numerator=base_numer,
                        exact_solution_denominator=np.array(base_den),
                        positive_graph_vertex_count=np.array(U))
    return data,positive_edges


def force_layout(n,edges):
    rng=np.random.default_rng(20261028)
    p=rng.normal(size=(n,2))
    for iteration in range(350):
        d=p[:,None,:]-p[None,:,:]
        sq=np.maximum((d*d).sum(axis=2),.02)
        force=(d/sq[:,:,None]).sum(axis=1)*.028
        for a,b in edges:
            delta=p[b]-p[a]
            pull=delta*np.linalg.norm(delta)*.35
            force[a]+=pull
            force[b]-=pull
        force-=.05*p
        norms=np.maximum(np.linalg.norm(force,axis=1),1e-10)
        cap=.1*(1-iteration/400)
        p+=force*np.minimum(.03,cap/norms)[:,None]
    p-=p.mean(axis=0)
    p/=np.max(np.abs(p),axis=0)
    return p


def box3d(ax,origin,size,color,style="-",alpha=1,width=1):
    o=np.asarray(origin)
    s=np.asarray(size)
    corners3=[o+s*np.array([i,j,k]) for i in (0,1) for j in (0,1) for k in (0,1)]
    for i,a in enumerate(corners3):
        for b in corners3[i+1:]:
            if np.count_nonzero(a!=b)==1:
                ax.plot(*zip(a,b),color=color,linestyle=style,alpha=alpha,lw=width)


def draw(data,edges):
    fig=plt.figure(figsize=(7.2,7.0),facecolor="white")
    grid=fig.add_gridspec(2,2,left=.055,right=.98,top=.85,bottom=.14,hspace=.31,wspace=.16)
    axa=fig.add_subplot(grid[0,0]); axb=fig.add_subplot(grid[0,1])
    axc=fig.add_subplot(grid[1,0],projection="3d"); axd=fig.add_subplot(grid[1,1])
    for ax in (axa,axb,axd):
        ax.set_axis_off(); ax.set_xlim(0,1); ax.set_ylim(0,1)
    fig.suptitle("Sparse algebra to local field readout",x=.055,ha="left",fontsize=14,color=NAVY,fontweight="bold")
    fig.text(.055,.925,"Exact two-variable example",color=GREY,fontsize=9)
    axa.text(0,1.05,"a  Signed rational input",color=NAVY,fontweight="bold",fontsize=10)
    axa.text(.02,.87,r"$Mx=b$",fontsize=19,color=NAVY)
    axa.text(.02,.60,"M =",fontsize=14,color=NAVY)
    axa.text(.28,.70," 2  −1",fontsize=16,fontfamily="DejaVu Sans Mono",color=NAVY)
    axa.text(.28,.48," 1   2",fontsize=16,fontfamily="DejaVu Sans Mono",color=NAVY)
    axa.plot([.29,.265,.265,.29],[.81,.81,.43,.43],color=NAVY,lw=1.1)
    axa.plot([.62,.645,.645,.62],[.81,.81,.43,.43],color=NAVY,lw=1.1)
    axa.text(.02,.29,r"$b=(1,0)^\mathsf{T},\quad F=M/8$",fontsize=12,color=BLUE)
    axa.text(.02,.14,"m = 4; exact 3-bit dyadic coefficients",fontsize=8.4,color=GREY)
    axa.text(.02,.005,r"$\eta=1/4,\quad x_*=(2/5,-1/5)^\mathsf{T}$",fontsize=10.5,color=NAVY)
    axb.text(0,1.05,"b  Positive-edge logical graph",color=NAVY,fontweight="bold",fontsize=10)
    S=data["counts"]["S"]; U=data["counts"]["Gplus_vertices"]
    pos=force_layout(U,edges)
    pos=pos*np.array([.43,.29])+np.array([.5,.62])
    for v,w in edges:
        axb.plot(*zip(pos[v],pos[w]),color="#aebbc4",lw=.5,zorder=1)
    axb.scatter(pos[:S,0],pos[:S,1],s=10,c=NAVY,marker="s",zorder=3)
    axb.scatter(pos[S:2*S,0],pos[S:2*S,1],s=11,c=BLUE,zorder=3)
    axb.scatter(pos[2*S:,0],pos[2*S:,1],s=11,c=ORANGE,marker="D",zorder=3)
    for node,label,offset in [(0,"source",(-10,11)),(S,"u₁",(-19,-16)),(S+1,"u₂",(7,14))]:
        axb.scatter(*pos[node],s=38,facecolors="none",edgecolors=NAVY,lw=.8,zorder=4)
        axb.annotate(label,pos[node],xytext=offset,textcoords="offset points",fontsize=7.5,
                     color=NAVY,bbox={"facecolor":"white","edgecolor":"none","pad":.8},
                     arrowprops={"arrowstyle":"-","color":GREY,"lw":.6},zorder=5)
    handles=[Line2D([],[],marker="s",ls="",markersize=4,color=NAVY,label="equation"),
             Line2D([],[],marker="o",ls="",markersize=4,color=BLUE,label="variable"),
             Line2D([],[],marker="D",ls="",markersize=4,color=ORANGE,label="mediator")]
    axb.legend(handles=handles,loc="lower center",bbox_to_anchor=(.5,.17),ncol=3,frameon=False,fontsize=7.3,
               handletextpad=.15,columnspacing=.6)
    axb.text(.02,.09,"S = 24; Γ₊: 96 vertices, 96 edges",fontsize=8.5,color=NAVY)
    axb.text(.02,-.015,"Degree ≤ 3. Unit edges; exact routes saved.",fontsize=8,color=GREY)
    # Put the physical title in figure coordinates because 3D axes preserve
    # a square drawing box, unlike the adjacent two-dimensional text panel.
    fig.text(.055,.471,"c  Finite physical domain",color=NAVY,fontweight="bold",fontsize=10)
    box3d(axc,(0,0,0),(1,.7,.6),NAVY,width=1)
    box3d(axc,(.18,.12,.1),(.64,.46,.4),GREY,"--",.55,.7)
    positions=np.array([[.28,.25,.22],[.45,.22,.21],[.66,.24,.2],[.72,.43,.23],
                        [.6,.45,.4],[.42,.43,.38],[.28,.44,.35],[.48,.33,.34]])
    axc.scatter(*positions.T,s=40,c=[BLUE,ORANGE,ORANGE,BLUE,ORANGE,ORANGE,BLUE,ORANGE],
                edgecolors="white",lw=.4,depthshade=False)
    axc.quiver(.08,.24,.22,.17,0,0,color=BLUE,lw=1.5,arrow_length_ratio=.25)
    axc.quiver(.74,.42,.24,.23,0,0,color=BLUE,lw=1.5,arrow_length_ratio=.25)
    axc.text(-.09,.16,.22,"source",fontsize=7.5,color=BLUE)
    axc.text(.86,.43,.22,"readout",fontsize=7.5,color=BLUE)
    axc.text(.78,.05,.62,"PEC",fontsize=7.5,color=NAVY)
    axc.text2D(.03,.20,"buffer",transform=axc.transAxes,fontsize=7.5,color=GREY)
    axc.set_xlim(-.07,1.05);axc.set_ylim(-.03,.78);axc.set_zlim(-.04,.66)
    axc.set_box_aspect((1,.7,.6));axc.view_init(elev=22,azim=-58);axc.set_axis_off()
    axc.text2D(-.025,-.12,r"Whole box: $N_xN_yN_z$ cells",transform=axc.transAxes,color=GREY,fontsize=8.5)
    axd.text(0,1.05,"d  Local readout and decoding",color=NAVY,fontweight="bold",fontsize=10)
    axd.text(.02,.84,r"$E\ \longmapsto\ \mathcal{D}E\ \longmapsto\ \widehat{x}$",fontsize=20,color=NAVY)
    axd.text(.02,.69,"Select coordinates, round, and rescale.",fontsize=8.3,color=GREY)
    axd.add_patch(Rectangle((.01,.18),.99,.38,facecolor=LIGHT,edgecolor="none"))
    axd.text(.035,.48,"Exact logical residual test",fontsize=8.4,color=NAVY,fontweight="bold")
    axd.text(.035,.34,r"$\widehat{x}=(819,-410)^\mathsf{T}/2048$",fontsize=12,color=BLUE)
    axd.text(.035,.22,"Relative residual = 1/2048 < η",fontsize=10,color=NAVY)
    axd.text(.02,.05,"Every coordinate perturbed; exact\nresidual transfer and decoder checked.",fontsize=8.2,color=GREY,linespacing=1.5)
    fig.text(.055,.055,r"Theorem-wide costs:  $S=O(m\log m)$,  $N=\widetilde O(m^{3/2})$.",fontsize=10,color=NAVY)
    fig.text(.055,.025,"All auxiliary variables, empty cells, buffers, source, and readout are counted.",fontsize=8.5,color=GREY)
    # At the manuscript width of 160 mm, 8.6 pt here is 7.52 pt.
    for text_object in fig.findobj(matplotlib.text.Text):
        if text_object.get_fontsize() < 8.6:
            text_object.set_fontsize(8.6)
    fig.savefig(HERE/"logical_translation.pdf",metadata={"Title":"Exact logical translation example","CreationDate":None})
    fig.savefig(DATA/"logical_translation.png",dpi=180)
    plt.close(fig)


if __name__ == "__main__":
    data,edges=build_example()
    draw(data,edges)
    print(json.dumps({"status":"PASS: exact finite logical example; physical panel schematic",
                      "counts":data["counts"],"residual_check":data["residual_check"]},indent=2))
