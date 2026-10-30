import Maxwell.Continuum.CutoffMonomialPassMachine

/-! The fixed cached traversal protects its outer-loop control words and
the separate profile table header. These are checked program footprints. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

def monomialProtectedPorts : List ℕ := [206,207,208,209,216,230,232,233,234,235]

theorem monomialPass_protects_auxiliary :
    monomialProtectedPorts.all (fun i => monomialPassCode.protectsTape i)=true := by decide

theorem monomialPass_auxiliary_frame {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (h : Executes input tape monomialPassCode cost s t) (i : ℕ) (hi : i∈monomialProtectedPorts) :
    t.val.tapes i=s.val.tapes i :=
  h.protectsTape i (List.all_eq_true.mp monomialPass_protects_auxiliary i hi)

#print axioms monomialPass_protects_auxiliary
end Maxwell.Continuum.Calibration.RawCutoff
