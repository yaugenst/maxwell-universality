# What the artifacts establish

The manuscript's continuum theorem, its discrete companion construction, the
Lean development, and the numerical demonstrations have distinct roles.

| Artifact | What it checks or illustrates |
| --- | --- |
| `paper/si/part2_continuum.tex` | The continuum proof for the bounded scalar-dielectric construction. The local Bloch minimum is not assumed to be a full spectral gap. |
| `certificates/continuum/` | Finite corner-cluster algebra, Hessian and placement calculations, and exact rational inequalities used in that proof. |
| `certificates/yee/` | Exact and interval computations for the discrete construction, including local inertia and the complete outside-L cover. The replay controller reports computational premises separately from analytic proofs. |
| `lean/` | The available formal development, its generated witnesses, and scoped audit entry points. Source inclusion and a successful default build do not mean that the entire reduction has been formally verified. |
| Periodic cavity experiment | A fixed, globally calibrated three-variable response, checked by full-vector Maxwell solves and mesh refinement. |
| Waveguide experiment | Reuse of one isolated-component calibration across five chain targets, including a mediator and an indefinite example. Full-vector Maxwell verification uses all three field components. |
| Precision and spacing study | The cost of weaker coupling and material rounding in the exact TE10 channel, with the source and decoder held fixed. Its one-dimensional solves are identified separately from the three-dimensional checks. |

The waveguide's transverse symmetry is useful structure. The successful chain
examples demonstrate component reuse on that platform; they do not implement
the general sparse-graph compiler or establish a computational speedup. The
compact periodic local-compilation failures are retained because they identify
the practical difficulty that the successful waveguide control avoids.

The stored reports describe recorded runs. Fresh verification commands generate
new receipts, and the Lean guide identifies the scope of each audit. The package
checksums establish which files were shipped. None of these three kinds of
record substitutes for the other two.

The device plots show prescribed scalar material, mathematical volume sources,
and signed volume-overlap readout. Fabricated launchers, detectors, material
dispersion, loss, and manufacturing tolerances are not modeled by these
demonstrations.
