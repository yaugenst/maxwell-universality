import Maxwell.Continuum.ParameterOuterTauData
import Maxwell.Cost.SelectedParameters.GeometricAdapterBounds
import Maxwell.Cost.Structured.NatAssign.BinaryPower

/-! Compute the exact detuning dyadic from the stored integer budget
using an executed least-geometric search followed by binary exponentiation. -/
namespace Maxwell.Continuum.Parameters.OuterTau
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def extra : Finset ℕ := Finset.Icc 2230 2238
def ids : Finset ℕ := GeometricAdapter.ids extra
def code : Code := .seq (GeometricAdapter.code 1 2 2234 2233 2235 2236)
  (RoutingPorts.powerCode 2235 2238 2237)
def searched (v : ℕ→ℕ) (N : ℕ) : ℕ→ℕ := Rational.after v 2235 2236 (N,1)
def result (v : ℕ→ℕ) (N : ℕ) : ℕ→ℕ := Function.update (searched v N) 2237 (2^N)
def workspace : Finset ℕ := ids∪{0,1,2,3}
def width (N B : ℕ) : ℕ := max (Geometric.width N 2 (GeometricAdapter.inputWidth 2 B)) (N+1)
def costBound (N B : ℕ) : ℕ := GeometricAdapter.costBound N 2 B+
  ((N+1)*(13*N.bits.length+25)+21*N.bits.length+27)

theorem extra_ge : ∀i∈extra,540 ≤ i := by intro i hi;simp only [extra,Finset.mem_Icc] at hi;omega

theorem searched_geo (v : ℕ→ℕ) (N i : ℕ) (hi : i∈Geometric.extra) : searched v N i=v i := by
  apply Rational.after_other
  all_goals simp only [Geometric.extra,Rational.common,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
  all_goals omega

theorem executes (v : ℕ→ℕ) (L d B : ℕ) (hL : 0<L)
    (hden : v 2233=budgetDen L d) (hone : v 2234=1) (hcounter : v 2238=0) (houtput : v 2237=0)
    (hgeo : ∀i∈Geometric.extra,v i=0) (hw : ∀i∈ids,(v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→Blank s.val i) :
    let N := Nat.clog 2 (budgetDen L d)
    ∃cost t,Executes input tape code cost s t ∧ cost ≤ costBound N B ∧
      NatAssign.Bank ids (result v N) t.val ∧ (∀i,i<5→Blank t.val i) ∧
      (∀i∈ids,(result v N i).bits.length ≤ width N B) ∧
      Word t.val 2237 (2^N) ∧ (1:ℚ)/(2^N)=tau L d hL ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  dsimp only
  let N := Nat.clog 2 (budgetDen L d)
  have rb : NatAssign.Bank (Rational.ids extra) v s.val := fun i hi=>hb i (Finset.mem_union_left _ hi)
  have rwid : ∀i∈Rational.ids extra,(v i).bits.length ≤ B := fun i hi=>hw i (Finset.mem_union_left _ hi)
  have gz : ∀i∈Geometric.extra,Blank s.val i := by
    intro i hi
    exact (RationalAccumulator.zero_word_iff_blank _ _).mp (by
      simpa only [hgeo i hi] using hb i (Finset.mem_union_right _ hi))
  have eg := GeometricAdapter.executes extra extra_ge 1 2 2234 2233 2235 2236
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) v 2 B (by decide) (by decide)
    (by rw [hone];decide) (by rw [hden];exact budgetDen_pos L d hL) rwid input tape s rb
    (fun i hi=>hs i (by omega)) gz
  simp only [hone,hden,Geometric.exponent_eq_clog] at eg
  obtain ⟨cg,g,eg,pg,bg,sg,zg,wg,fg⟩ := eg
  change NatAssign.Bank (Rational.ids extra) (searched v N) g.val at bg
  change ∀i∈Rational.ids extra,(searched v N i).bits.length ≤
    Geometric.width N 2 (GeometricAdapter.inputWidth 2 B) at wg
  have gb : NatAssign.Bank ids (searched v N) g.val := by
    intro i hi
    rcases Finset.mem_union.mp hi with hr|he
    · exact bg i hr
    · rw [searched_geo v N i he,hgeo i he]
      exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (zg i (Finset.mem_union_left _ he))
  have gs : ∀i,i<5→Blank g.val i := by
    intro i hi
    by_cases h4 : i<4
    · exact sg i h4
    · have hi4 : i=4 := by omega
      subst i
      exact RationalAccumulator.blank_of_eq (fg.tapes 4 (by decide +kernel)) (hs 4 (by decide))
  have g5 : searched v N 2235=N := by simp [searched]
  have g7 : searched v N 2237=0 := by simpa [searched,Rational.after,Rational.common] using houtput
  have g8 : searched v N 2238=0 := by simpa [searched,Rational.after,Rational.common] using hcounter
  obtain ⟨cp,t,ep,pp,bt,ft⟩ := NatAssign.binaryPower ids 2235 2238 2237
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide)
    (searched v N) g8 g7 input tape g gb
  rw [g5] at pp bt
  have frame : BinaryPrecision.Frame workspace s.val t.val :=
    (fg.mono (by decide +kernel)).trans (ft.mono (by decide +kernel))
  refine ⟨cg+cp,t,eg.seq ep,Nat.add_le_add pg pp,bt,?_,?_,?_,(tau_eq L d hL).symm,frame⟩
  · intro i hi
    exact RationalAccumulator.blank_of_eq (ft.tapes i (by simp;omega)) (gs i hi)
  · intro i hi
    by_cases ho : i=2237
    · subst i
      simp only [result,Function.update_self,Nat.size_eq_bits_len,Nat.size_pow]
      exact le_max_right _ _
    · simp only [result,Function.update_of_ne ho]
      rcases Finset.mem_union.mp hi with hr|he
      · exact (wg i hr).trans (le_max_left _ _)
      · rw [searched_geo v N i he,hgeo i he]
        exact Nat.zero_le _
  · simpa only [Function.update_self] using bt 2237 (by decide +kernel)

#print axioms executes
end Maxwell.Continuum.Parameters.OuterTau
