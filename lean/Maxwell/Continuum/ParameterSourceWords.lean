import Maxwell.Continuum.ParameterSourceInput
import Maxwell.Continuum.ParameterPrecision

/-! The two rational source-side budgets are literal short integers and
integer reciprocals; their width is not inferred merely from their size. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open Maxwell.Composition Maxwell.Logical Maxwell.Realization
set_option backward.isDefEq.respectTransparency true

def sourceBudgetNat (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) : ℕ :=
  let n := (SelectedInput.input p S hm).precision
  9*(1024*PhysicalParameters.routingSide S n)^2*
    (256*S.nnz^(⌈p.conditionExponent⌉₊+1)*(sourceCircuit S n).size^4+
      1024*PhysicalParameters.routingSide S n)

theorem source_K_eq (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    (sourceInput p S hm).K = (sourceBudgetNat p S hm : ℚ) := by
  change 9*(1024*(PhysicalParameters.routingSide S (SelectedInput.input p S hm).precision : ℚ))^2*
    (256*(S.nnz : ℚ)^(⌈p.conditionExponent⌉₊+1)*
      ((sourceCircuit S (SelectedInput.input p S hm).precision).size : ℚ)^4+
      1024*(PhysicalParameters.routingSide S (SelectedInput.input p S hm).precision : ℚ)) = _
  unfold sourceBudgetNat
  push_cast
  rfl

def sourceErrorDen (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) : ℕ :=
  16*max 2 (S.nnz^⌈p.accuracyExponent⌉₊*PhysicalAccuracy.denominator S (SelectedInput.input p S hm).precision)

theorem sourceErrorDen_pos (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    0 < sourceErrorDen p S hm := by unfold sourceErrorDen; positivity

private theorem min_inverse_pos {a b : ℚ} (ha : 0 < a) (hb : 0 < b) :
    min (1/a) (1/b) = 1/max a b := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, min_eq_right ((one_div_le_one_div_of_le ha hab))]
  · rw [max_eq_left (le_of_not_ge hab), min_eq_left (one_div_le_one_div_of_le hb (le_of_not_ge hab))]

theorem source_epsilon_eq (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    (sourceInput p S hm).epsilon = 1/(sourceErrorDen p S hm : ℚ) := by
  have hd : (0 : ℚ) < PhysicalAccuracy.denominator S (SelectedInput.input p S hm).precision := by
    exact_mod_cast PhysicalAccuracy.denominator_ge_one S (SelectedInput.input p S hm).precision
  have hmQ : (0 : ℚ) < S.nnz := by exact_mod_cast hm
  change min (1/2) ((1/(S.nnz : ℚ)^⌈p.accuracyExponent⌉₊)/
    (PhysicalAccuracy.denominator S (SelectedInput.input p S hm).precision : ℚ))/16 = _
  rw [div_div, min_inverse_pos (by norm_num) (by positivity)]
  unfold sourceErrorDen
  push_cast
  rw [div_div]
  congr 1
  ring

theorem nat_rational_bits (n : ℕ) : rationalBitLength (n : ℚ) = n.bits.length+2 := by
  simp only [rationalBitLength, Rat.num_natCast, Rat.den_natCast, signedBitLength,
    Int.natAbs_natCast, Codec.unsignedBitLength_eq_size, Nat.size_eq_bits_len]
  norm_num

theorem inverse_nat_rational_bits {n : ℕ} (hn : 0 < n) :
    rationalBitLength ((n : ℚ)⁻¹) = n.bits.length+2 := by
  simp only [rationalBitLength, Rat.inv_natCast_num_of_pos hn, Rat.inv_natCast_den_of_pos hn,
    signedBitLength, Int.natAbs_one, Codec.unsignedBitLength_eq_size, Nat.size_eq_bits_len]
  norm_num
  omega

theorem source_input_rational_bits (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    rationalBitLength (sourceInput p S hm).K ≤ sourceBudgetExponent p*inputLog S.nnz+3 ∧
    rationalBitLength (sourceInput p S hm).epsilon ≤ sourceBudgetExponent p*inputLog S.nnz+3 := by
  have hI := sourceInput_binary p S hm hm2 hunit
  have hK := hI.K
  have he := hI.epsilon
  rw [source_K_eq] at hK
  rw [source_epsilon_eq, one_div, inv_inv] at he
  have hnK : sourceBudgetNat p S hm ≤ 2^(sourceBudgetExponent p*inputLog S.nnz) := by exact_mod_cast hK
  have hnE : sourceErrorDen p S hm ≤ 2^(sourceBudgetExponent p*inputLog S.nnz) := by exact_mod_cast he
  have hbK := Nat.size_le_size hnK
  have hbE := Nat.size_le_size hnE
  rw [Nat.size_pow, ← Nat.size_eq_bits_len] at hbK hbE
  rw [source_K_eq, nat_rational_bits, source_epsilon_eq, one_div,
    inverse_nat_rational_bits (sourceErrorDen_pos p S hm)]
  constructor <;> omega

#print axioms source_input_rational_bits

end Maxwell.Continuum.Parameters
