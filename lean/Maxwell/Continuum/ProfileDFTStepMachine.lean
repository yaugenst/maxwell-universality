import Maxwell.Continuum.ProfileDFTStepData
import Maxwell.Continuum.ProfileScalarExternal

/-! Execution of a literal DFT sample, with its cached sum and every
metadata load included in the charged fixed program. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

structure DFTParameters (D P : ℕ) (s : Store) : Prop where
  precision : Word s.val 663 P
  one : Word s.val 667 1
  guard : Word s.val 668 (P+4)
  range : Word s.val 669 (D+1)
  phaseRange : Word s.val 652 (D+1)
  phasePrecision : Word s.val 653 P
  gluePrecision : Word s.val 640 (P+4)

theorem dft_step_executes (S : Finset ℕ) (hS : Finset.range 10⊆S)
    (D P U B W : ℕ) (v : ℕ→Parts) (hw : WidthBank S W v)
    (hx : (v 0).Width (U+1)) (hk : (v 5).Width (U+1)) (hv : (v 0).Valid)
    (hacc : (v 9).Width B) (hD : D≤U) (hP : P≤U)
    (hscratch : dftScratchWidth U≤W) (hB : B+dftTermWidth U+1≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready S v s)
    (hp : Phase.Runtime.Clean s.val) (hg : Glue.Clean s.val) (hm : DFTParameters D P s) :
    ∃cost t,Executes input tape dftStepCode cost s t ∧ cost≤dftStepCost D P W ∧
      Ready S (dftStepValues D P v) t ∧ Phase.Runtime.Clean t.val ∧ Glue.Clean t.val ∧
      DFTParameters D P t ∧ BinaryPrecision.Frame (angularWorkspace S) s.val t.val := by
  have mem (i : ℕ) (hi : i<10) : i∈S := hS (Finset.mem_range.mpr hi)
  have small : ({0,1,2,3,4}:Finset ℕ)⊆S := by
    intro i hi
    apply mem i
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have hW : 10≤W := by unfold dftScratchWidth at hscratch;omega
  have hpbits : (P+4).bits.length≤W := (bits_le_of_le (Nat.add_le_add_right hP 4)).trans
    (by unfold dftScratchWidth at hscratch;omega)
  have hnbits : P.bits.length≤W := (bits_le_of_le hP).trans
    (by unfold dftScratchWidth at hscratch;omega)
  have hqbits : (D+1).bits.length≤W := (bits_le_of_le (Nat.add_le_add_right hD 1)).trans
    (by unfold dftScratchWidth at hscratch;omega)
  obtain ⟨c0,s0,e0,h0,r0,zp0,zg0,q0,n0,g0,f0⟩ := angular_loaded_executes S small
    P (D+1) P (P+4) W v hw hW hpbits hqbits hnbits hpbits hv input tape s hr hp hg
    hm.phaseRange hm.phasePrecision hm.gluePrecision hm.one hm.guard
  have hw0 := angularValues_width S P U W v hw hx hP (by unfold dftScratchWidth at hscratch;omega)
  have htrace1 := dftPreparation_width S P U W v hw0 hx hk (by unfold dftScratchWidth at hscratch;omega)
  obtain ⟨c1,s1,e1,h1,r1,f1⟩ := program_executes S dftPreparation (dftPreparation_valid S hS)
    (angularValues P v) W htrace1 input tape s0 r0
  change Ready S (dftAfterPreparation P v) s1 at r1
  have zp1 := phaseClean_arithmetic zp0 r1 f1
  have zg1 := glueClean_arithmetic zg0 r1 f1
  have f01 := f0.trans (f1.mono (arithmetic_sub_scalar S))
  have keep1 (i : ℕ) (hi : 107 ≤ i ∧ i < 1000) : s1.val.tapes i=s0.val.tapes i :=
    f1.tapes i (RationalDataflow.outside_workspace S i (Or.inr hi))
  have q1 := word_of_eq (keep1 652 (by decide)) q0
  have n1 := word_of_eq (keep1 653 (by decide)) n0
  have g1 := word_of_eq (keep1 640 (by decide)) g0
  have pm1 := word_of_eq (f01.tapes 663 (scalar_external S 663 (by decide))) hm.precision
  have qm1 := word_of_eq (f01.tapes 669 (scalar_external S 669 (by decide))) hm.range
  have hw1 : WidthBank S W (dftAfterPreparation P v) := htrace1.2.2
  obtain ⟨c2,s2,e2,h2,r2,zp2,q2,n2,f2⟩ := Phase.Runtime.loaded_executes S RationalTaylor.Runtime.cosineCycle
    (D+1) P 1 (P+4) 7 6 669 663 W (mem 7 (by decide)) (mem 6 (by decide))
    (by decide) (by decide) (dftAfterPreparation P v) hw1 hqbits hnbits
    (by simpa only [Nat.one_bits,List.length_singleton] using (show 1≤W by omega)) hpbits hW
    input tape s1 r1 zp1 q1 n1 qm1 pm1
  rw [RationalTaylor.Runtime.cosineCycle_signs] at r2
  change Ready S (dftAfterPhase D P v) s2 at r2
  have zg2 := glueClean_after_phase zg1 zp2 r2 f2
  have g2 := phase_preserves_glue_precision S s1 s2 f2 (P+4) g1
  have hw2 := dftAfterPhase_width S D P U W v hw1 hx hk hD hP
    (by unfold dftScratchWidth at hscratch;omega)
  obtain ⟨c3,t,e3,h3,r3,f3⟩ := program_executes S dftFinish (dftFinish_valid S hS)
    (dftAfterPhase D P v) W (dftFinish_width S D P U B W v hw2 hx hk hacc hD hP hB)
    input tape s2 r2
  change Ready S (dftStepValues D P v) t at r3
  have zp3 := phaseClean_arithmetic zp2 r3 f3
  have zg3 := glueClean_arithmetic zg2 r3 f3
  have ff := f01.trans ((f2.mono Finset.subset_union_left).trans (f3.mono (arithmetic_sub_scalar S)))
  have keep3 (i : ℕ) (hi : 107 ≤ i ∧ i < 1000) : t.val.tapes i=s2.val.tapes i :=
    f3.tapes i (RationalDataflow.outside_workspace S i (Or.inr hi))
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,r3,zp3,zg3,?_,ff⟩
  · simp only [show dftPreparation.length=1 by rfl,Nat.one_mul] at h1
    simp only [show dftFinish.length=2 by rfl] at h3
    unfold dftStepCost
    omega
  · exact ⟨word_of_eq (ff.tapes 663 (scalar_external S 663 (by decide))) hm.precision,
      word_of_eq (ff.tapes 667 (scalar_external S 667 (by decide))) hm.one,
      word_of_eq (ff.tapes 668 (scalar_external S 668 (by decide))) hm.guard,
      word_of_eq (ff.tapes 669 (scalar_external S 669 (by decide))) hm.range,
      word_of_eq (keep3 652 (by decide)) q2,word_of_eq (keep3 653 (by decide)) n2,
      word_of_eq (keep3 640 (by decide)) g2⟩

#print axioms dft_step_executes
end Maxwell.Continuum.Profile.Runtime
