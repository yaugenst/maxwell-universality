import Maxwell.Cost.RealSimulation.VerifiedAt
import Maxwell.Cost.RealSimulation.WidthVerified

/-!
Actual finite BitRAM-to-RealRAM compilation.

`machine_run_at` gives a linear charged runtime simulation, with exact buffers
and the unused random-tape suffix. `width_machine_run` additionally proves an
index-word bound at every target instruction. The latter explicitly requires
the source prefix-address bound; no source-specific encoder/decoder bound is
inferred from total runtime.
-/
