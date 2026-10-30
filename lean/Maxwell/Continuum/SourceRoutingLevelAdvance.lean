import Maxwell.Continuum.SourceRoutingTreeArithmetic

/-! The next-level controller halves the token count, shortens the word
width, doubles the node count and advances the first-node address. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level.Advance
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def divided (v : ℕ→ℕ) : ℕ→ℕ := Function.update (Function.update v 811 (v 811/v 819)) 816 (v 811%v 819)
def decreased (v : ℕ→ℕ) : ℕ→ℕ := Function.update (divided v) 812 (v 812-1)
def instructions : List NatAssign.Instruction :=
  [.multiply 819 813,.multiply 819 814,.add 819 814,.literal 815 0]
def output (v : ℕ→ℕ) : ℕ→ℕ := NatAssign.values instructions (decreased v)
def code : Code := .seq (Division.code 811 819 811 816)
  (.seq (PhysicalMaterial.FixedSubtract.code 812 1) (NatAssign.code instructions))

theorem decreased_width (v : ℕ→ℕ) (B : ℕ) (hw : ∀j∈Division.ids,(v j).bits.length ≤ B) :
    ∀j∈Division.ids,(decreased v j).bits.length ≤ B := by
  intro j hj
  by_cases h812 : j=812
  · subst j
    exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.sub_le (v 812) 1)).trans (hw 812 (by decide))
  · by_cases h816 : j=816
    · subst j
      exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.mod_le (v 811) (v 819))).trans (hw 811 (by decide))
    · by_cases h811 : j=811
      · subst j
        exact (Maxwell.Continuum.RationalWords.bits_mono (Nat.div_le_self (v 811) (v 819))).trans (hw 811 (by decide))
      · simpa only [decreased,divided,Function.update_of_ne h812,Function.update_of_ne h816,
          Function.update_of_ne h811] using hw j hj

theorem executes (v : ℕ→ℕ) (B : ℕ)
    (hz : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0)
    (htwo : v 819=2) (hwidth : 0<v 812) (hw : ∀j∈Division.ids,(v j).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank Division.ids v s.val) (hc : PrivateVisit.Clean s) (h839 : Blank s.val 839) :
    ∃steps t, Executes input tape code steps s t ∧ steps ≤ 2^110*(B+2)^2 ∧
      NatAssign.Bank Division.ids (output v) t.val ∧ PrivateVisit.Clean t ∧ Blank t.val 839 ∧
      BinaryPrecision.Frame Division.work s.val t.val := by
  obtain ⟨c0,a,e0,h0,b0,z0,a839,f0⟩:=Division.executes 811 819 811 816
    (by decide) (by decide) (by decide) (by decide) (by omega) v hz (by omega) B hw input tape s hs hc h839
  obtain ⟨c1,b,e1,h1,b1,z1,f1⟩:=Arithmetic.decrement 812 (by decide) (divided v)
    (by simpa only [divided,Function.update_of_ne (by decide : (812 : ℕ)≠816),
      Function.update_of_ne (by decide : (812 : ℕ)≠811)] using hwidth) input tape a b0 z0
  have vi : ∀a∈instructions,a.Valid Division.ids := by
    simp [instructions,NatAssign.Instruction.Valid,Division.ids,Division.controls]
  have li : ∀a∈instructions,a.literalWidth ≤ B := by
    simp [instructions,NatAssign.Instruction.literalWidth]
  obtain ⟨c2,t,e2,h2,b2,z2,f2⟩:=Arithmetic.stage instructions vi (decreased v) B
    (decreased_width v B hw) li input tape b b1 z1
  have f1' : BinaryPrecision.Frame Division.work a.val b.val := f1.mono (by decide)
  have f2' : BinaryPrecision.Frame Division.work b.val t.val := f2.mono Arithmetic.work_subset
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2,z2,
    RationalAccumulator.blank_of_eq (f2.tapes 839 (by decide))
      (RationalAccumulator.blank_of_eq (f1.tapes 839 (by decide)) a839),f0.trans (f1'.trans f2')⟩
  · change c1 ≤ 29*(v 812).bits.length+31 at h1
    change c2 ≤ 3000*8^4*(B+2)^2 at h2
    have hh:=hw 812 (by decide)
    have linear : 29*B+32 ≤ 32*(B+2)^2 := by nlinarith
    nlinarith only [h0,h1,h2,hh,linear]

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level.Advance
