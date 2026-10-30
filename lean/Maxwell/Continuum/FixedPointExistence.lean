import Maxwell.Target
import Mathlib.Algebra.Order.Floor.Ring

/-! Finite reports exist throughout the advertised fixed-point range. This
is a semantic existence result, not an algorithm for integrating a field. -/

noncomputable section
namespace Maxwell.Target.FixedPointFormat
set_option maxHeartbeats 600000

theorem exists_accurate (F : FixedPointFormat) (x : ℝ) (hx : F.InRange x) :
    ∃w : F.Word, |(F.value w : ℝ)-x|≤1/(2 : ℝ)^F.fractionalBits := by
  let d : ℤ := ⌊x*(2 : ℝ)^F.fractionalBits⌋
  let a : ℤ := 2^(F.integerBits+F.fractionalBits)
  have hD : (0 : ℝ)<(2 : ℝ)^F.fractionalBits := by positivity
  have hLo : -a≤d := by
    apply Int.le_floor.mpr
    dsimp only [a]
    push_cast
    rw [pow_add,← neg_mul]
    exact mul_le_mul_of_nonneg_right hx.1 hD.le
  have hHi : d<a := by
    apply Int.floor_lt.mpr
    dsimp only [a]
    push_cast
    rw [pow_add]
    exact mul_lt_mul_of_pos_right hx.2 hD
  have hnonneg : 0≤d+a := by omega
  have hword : (d+a).toNat<2^F.width := by
    have hp : ((2^F.width : ℕ) : ℤ)=2*a := by
      simp only [width,Nat.cast_pow,Nat.cast_ofNat,a]
      rw [show 1+F.integerBits+F.fractionalBits=1+(F.integerBits+F.fractionalBits) by omega,pow_add]
      ring
    have hz : ((d+a).toNat : ℤ)<((2^F.width : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hnonneg,hp]
      omega
    exact_mod_cast hz
  let w : F.Word := ⟨(d+a).toNat,hword⟩
  have hn : F.numerator w=d := by
    change ((d+a).toNat : ℤ)-a=d
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  have hv : (F.value w : ℝ)=(d : ℝ)/(2 : ℝ)^F.fractionalBits := by
    simp only [value,hn,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat]
  have hfloor : (d : ℝ)≤x*(2 : ℝ)^F.fractionalBits := Int.floor_le _
  have herr : x*(2 : ℝ)^F.fractionalBits<(d : ℝ)+1 := Int.lt_floor_add_one _
  have hle : (d : ℝ)/(2 : ℝ)^F.fractionalBits≤x := (div_le_iff₀ hD).mpr hfloor
  have herror : x-(d : ℝ)/(2 : ℝ)^F.fractionalBits≤1/(2 : ℝ)^F.fractionalBits := by
    apply (le_div_iff₀ hD).mpr
    rw [sub_mul,div_mul_cancel₀ _ hD.ne']
    linarith
  refine ⟨w,?_⟩
  rw [hv,abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith only [herror]

#print axioms exists_accurate

end Maxwell.Target.FixedPointFormat

namespace Maxwell.Target.WeightedDecoder

theorem exists_accurate {ι : Type*} {n : ℕ} (D : WeightedDecoder ι n)
    (y : ι → ℝ) (h : D.Fits y) : ∃w : D.Messages,D.Accurate w y := by
  choose w hw using fun i => D.format.exists_accurate (y (D.coordinate i)) (h i)
  exact ⟨w,hw⟩

#print axioms exists_accurate

end Maxwell.Target.WeightedDecoder
