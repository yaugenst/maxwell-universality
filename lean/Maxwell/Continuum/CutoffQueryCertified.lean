import Maxwell.Continuum.CutoffQueryMachine

/-! The executed cutoff program encloses the literal smooth Bloch cutoff.
The input coordinates and the stored finite table are explicit runtime words. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 4096
attribute [local irreducible] chiCenter Well.chi

theorem cutoffQuery_computes_enclosure (N : ℕ) (a : Table (Profile.profileDegree N))
    (hdata : ∀ i, a.get i=antiderivativeCoefficient N i)
    (W : ℕ) (hW : 3≤W) (hcoeffWidth : 2^65*(N+1)^4≤W) (hmeta : a.MetadataWidth W)
    (v : ℕ→Parts) (hw : WidthBank querySlots W v) (hg : Good querySlots v)
    (q₀ : ℝ) (x : Space)
    (hx : ∀ i : Fin 3, |x i/q₀-((v (10+i.val)).value : ℝ)|≤(1/2 : ℝ)^(N+12))
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=Profile.profileDegree N)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin) (hblank : Blank s.val 206)
    (hs : Ready querySlots v s) (ha : a.Ready s) :
    ∃ t output,
      (runPriced (cutoffQueryCode.compile.next input tape)
        (cutoffQueryCost (Profile.profileDegree N) W xs.length+1) s.val).finished=
          some (t.place cutoffQueryCode.size) ∧
      (runPriced (cutoffQueryCode.compile.next input tape)
        (cutoffQueryCost (Profile.profileDegree N) W xs.length+1) s.val).instructions≤
          cutoffQueryCost (Profile.profileDegree N) W xs.length ∧
      Ready querySlots output t ∧ Good querySlots output ∧ a.Ready t ∧
      WidthBank querySlots (polynomialPlanWidth (Profile.profileDegree N) W 42) output ∧
      |Well.chi q₀ x-((output 16).value : ℝ)|≤(1/2 : ℝ)^N := by
  obtain ⟨t,output,hrun,hcost,hready,hgood,harray,hwidth,hvalue⟩ :=
    cutoffQuery_computes N a hdata W hW hcoeffWidth hmeta v hw hg input tape xs origin
      hlen s hn hcount hblank hs ha
  refine ⟨t,output,hrun,hcost,hready,hgood,harray,hwidth,?_⟩
  rw [hvalue]
  have he := chiApprox_contains (fun i : Fin 3 => (v (10+i.val)).value) N q₀ x hx
  change |Well.chi q₀ x-(chiCenter (fun i : Fin 3 => (v (10+i.val)).value) N : ℝ)|≤
    (((1/2:ℚ)^N : ℚ) : ℝ) at he
  simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using he

def cutoffInputWidth (N U : ℕ) : ℕ := 2^66*(N+1)^4*(U+1)

theorem cutoffInputWidth_bounds (N U : ℕ) :
    3≤cutoffInputWidth N U ∧ U≤cutoffInputWidth N U ∧
      2^65*(N+1)^4≤cutoffInputWidth N U := by
  have hn : 1≤(N+1)^4 := one_le_pow₀ (by omega)
  have hmul : 2^66*(N+1)^4≤cutoffInputWidth N U := by
    unfold cutoffInputWidth
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hu : U+1≤cutoffInputWidth N U := by
    unfold cutoffInputWidth
    exact Nat.le_mul_of_pos_left _ (by positivity)
  constructor
  · have : 3≤2^66*(N+1)^4 := by nlinarith only [hn]
    exact this.trans hmul
  exact ⟨by omega,(Nat.mul_le_mul_right _ (by norm_num : (2:ℕ)^65≤2^66)).trans hmul⟩

theorem cutoffQueryCost_input_precision (N U wordLength : ℕ)
    (hlen : wordLength≤cutoffInputWidth N U) :
    cutoffQueryCost (Profile.profileDegree N) (cutoffInputWidth N U) wordLength≤
      2^3840*(N+1)^182*(U+2)^2 := by
  have hmain := cutoffQueryCost_precision N (cutoffInputWidth N U) wordLength hlen
  have hn : 1≤(N+1)^4 := one_le_pow₀ (by omega)
  have hw : cutoffInputWidth N U+2≤2^67*(N+1)^4*(U+2) := by
    unfold cutoffInputWidth
    nlinarith
  have hp := Nat.pow_le_pow_left hw 2
  have hm := Nat.mul_le_mul_left (2^3700*(N+1)^174) hp
  have he : 2^3700*(N+1)^174*(2^67*(N+1)^4*(U+2))^2=
      (2:ℕ)^3834*(N+1)^182*(U+2)^2 := by
    simp only [mul_pow,←pow_mul]
    ring
  rw [he] at hm
  exact hmain.trans (hm.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by decide) (by decide)))))

#print axioms cutoffQuery_computes_enclosure
#print axioms cutoffQueryCost_input_precision
end Maxwell.Continuum.Calibration.RawCutoff
