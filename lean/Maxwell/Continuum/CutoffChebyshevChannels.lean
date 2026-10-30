import Maxwell.Continuum.CutoffAntiderivativeTable
import Maxwell.Continuum.RawSharedDenominator

/-! Raw integer channels for the cached two-row Chebyshev recurrence. The
positive and negative channels themselves have linear bit width; no gcd or
integer cancellation is needed to obtain the bound. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow Profile
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def rawChebyshevState (D : ℕ) : ℕ→Vector Parts D×Vector Parts D
  | 0 => (Vector.ofFn (fun i => if i.val=0 then Parts.literal 1 else Parts.literal 0),
      Vector.ofFn (fun i => if i.val=1 then Parts.literal 1 else Parts.literal 0))
  | j+1 =>
      let v := rawChebyshevState D j
      (v.2,Vector.ofFn (fun i => ((Parts.literal 2).mul
        (if hi : i.val=0 then Parts.literal 0 else v.2.get ⟨i.val-1,by omega⟩)).sub (v.1.get i)))

theorem rawChebyshevState_denominator (D j : ℕ) :
    (∀ i : Fin D, ((rawChebyshevState D j).1.get i).denominator=1) ∧
    (∀ i : Fin D, ((rawChebyshevState D j).2.get i).denominator=1) := by
  induction j with
  | zero =>
    constructor <;> intro i <;> simp only [rawChebyshevState,vector_get_ofFn] <;>
      split_ifs <;> rfl
  | succ j ih =>
    refine ⟨ih.2,?_⟩
    intro i
    simp only [rawChebyshevState,vector_get_ofFn,Parts.sub,Parts.mul]
    split_ifs <;> simp [ih.1,ih.2,Parts.literal]

theorem rawChebyshevState_valid (D j : ℕ) :
    (∀ i : Fin D, ((rawChebyshevState D j).1.get i).Valid) ∧
    (∀ i : Fin D, ((rawChebyshevState D j).2.get i).Valid) := by
  have h := rawChebyshevState_denominator D j
  exact ⟨fun i => by change 0<_ ; rw [h.1]; decide,
    fun i => by change 0<_ ; rw [h.2]; decide⟩

theorem rawChebyshevState_value (D j : ℕ) :
    (∀ i : Fin D, ((rawChebyshevState D j).1.get i).value=((chebyshevState D j).1.get i : ℚ)) ∧
    (∀ i : Fin D, ((rawChebyshevState D j).2.get i).value=((chebyshevState D j).2.get i : ℚ)) := by
  induction j with
  | zero =>
    constructor <;> intro i <;> simp only [rawChebyshevState,chebyshevState,vector_get_ofFn] <;>
      split_ifs <;> simp only [Parts.literal_value,Int.cast_one,Int.cast_zero]
  | succ j ih =>
    refine ⟨ih.2,?_⟩
    intro i
    have hv := rawChebyshevState_valid D j
    simp only [rawChebyshevState,chebyshevState,vector_get_ofFn]
    rw [Parts.sub_value _ _ (Parts.mul_valid (Parts.literal_valid _)
      (by split_ifs; exact Parts.literal_valid _; exact hv.2 _)) (hv.1 i),Parts.mul_value,
      Parts.literal_value,ih.1]
    split_ifs <;> simp only [Parts.literal_value,ih.2,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,
      Int.cast_zero]

theorem rawChebyshevState_channels (D j : ℕ) :
    (∀ i : Fin D, ((rawChebyshevState D j).1.get i).positive+
      ((rawChebyshevState D j).1.get i).negative≤3^j) ∧
    (∀ i : Fin D, ((rawChebyshevState D j).2.get i).positive+
      ((rawChebyshevState D j).2.get i).negative≤3^(j+1)) := by
  induction j with
  | zero =>
    constructor <;> intro i <;> simp only [rawChebyshevState,vector_get_ofFn] <;>
      split_ifs <;> norm_num [Parts.literal]
  | succ j ih =>
    refine ⟨ih.2,?_⟩
    intro i
    let x := if hi : i.val=0 then Parts.literal 0 else (rawChebyshevState D j).2.get ⟨i.val-1,by omega⟩
    have hxd : x.denominator=1 := by
      dsimp [x]
      split_ifs
      · rfl
      · exact (rawChebyshevState_denominator D j).2 _
    have hxb : x.positive+x.negative≤3^(j+1) := by
      dsimp [x]
      split_ifs
      · norm_num [Parts.literal]
      · exact ih.2 _
    have hyd := (rawChebyshevState_denominator D j).1 i
    have hyb := ih.1 i
    simp only [rawChebyshevState,vector_get_ofFn]
    change (((Parts.literal 2).mul x).sub ((rawChebyshevState D j).1.get i)).positive+
      (((Parts.literal 2).mul x).sub ((rawChebyshevState D j).1.get i)).negative≤3^(j+1+1)
    simp only [Parts.sub,Parts.mul,hyd,hxd,Parts.literal]
    norm_num
    simp only [pow_succ] at hxb ⊢
    nlinarith only [hxb,hyb]

theorem rawChebyshevState_width (D j : ℕ) :
    (∀ i : Fin D, ((rawChebyshevState D j).1.get i).Width (2*j+1)) ∧
    (∀ i : Fin D, ((rawChebyshevState D j).2.get i).Width (2*(j+1)+1)) := by
  have general (x : Parts) (k : ℕ) (hd : x.denominator=1)
      (hb : x.positive+x.negative≤3^k) : x.Width (2*k+1) := by
    have h3 : (3:ℕ)^k≤2^(2*k) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) k
    have hp : x.positive≤2^(2*k) := (Nat.le_add_right _ _).trans (hb.trans h3)
    have hn : x.negative≤2^(2*k) := (Nat.le_add_left _ _).trans (hb.trans h3)
    refine ⟨?_,?_,?_⟩
    · rw [Nat.size_eq_bits_len]
      exact (Nat.size_le_size hp).trans (by simp only [Nat.size_pow]; exact le_rfl)
    · rw [Nat.size_eq_bits_len]
      exact (Nat.size_le_size hn).trans (by simp only [Nat.size_pow]; exact le_rfl)
    · rw [hd]
      change 1≤2*k+1
      omega
  have hd := rawChebyshevState_denominator D j
  have hb := rawChebyshevState_channels D j
  exact ⟨fun i => general _ _ (hd.1 i) (hb.1 i),fun i => general _ _ (hd.2 i) (hb.2 i)⟩

#print axioms rawChebyshevState_width
#print axioms rawChebyshevState_value
end Maxwell.Continuum.Calibration.RawCutoff
