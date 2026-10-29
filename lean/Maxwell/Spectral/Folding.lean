import Maxwell.Spectral.PrimitiveYee
import Maxwell.Spectral.BlockFolding
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Block

/-!
# Index-four FCC cell decomposition

The conventional 8000-cell cube splits into four translates of the primitive
2000-cell set.  The exact coordinate bijection, normalized Fourier matrix of
the quotient `(Z/2)^2`, and momentum-dependent gauge give a unitary map whose
sector columns intertwine the actual Yee curl, adjoint curl, and material mass.
-/

namespace Maxwell.Spectral.Folding

open PeriodicYee
open scoped Matrix

abbrev Coset := Fin 2 × Fin 2
abbrev SplitCell := PrimitiveYee.Cell × Coset

def splitCell (r : Cell20) : SplitCell :=
  ((⟨((r 0).val + 40 - 10 * ((r 1).val / 10 + (r 2).val / 10)) % 20,
      Nat.mod_lt _ (by decide)⟩,
    ⟨(r 1).val % 10, Nat.mod_lt _ (by decide)⟩,
    ⟨(r 2).val % 10, Nat.mod_lt _ (by decide)⟩),
    ⟨(r 1).val / 10, by have h := ZMod.val_lt (r 1); omega⟩,
    ⟨(r 2).val / 10, by have h := ZMod.val_lt (r 2); omega⟩)

def joinCell (p : SplitCell) : Cell20 :=
  ![(p.1.1.val + 10 * (p.2.1.val + p.2.2.val) : ℕ),
    (p.1.2.1.val + 10 * p.2.1.val : ℕ),
    (p.1.2.2.val + 10 * p.2.2.val : ℕ)]

theorem join_split (r : Cell20) : joinCell (splitCell r) = r := by
  have h0 := ZMod.val_lt (r 0)
  have h1 := ZMod.val_lt (r 1)
  have h2 := ZMod.val_lt (r 2)
  funext j
  apply ZMod.val_injective
  fin_cases j <;> dsimp [joinCell, splitCell] <;>
    simp only [ZMod.val_natCast] <;> omega

theorem split_join (p : SplitCell) : splitCell (joinCell p) = p := by
  obtain ⟨⟨x, y, z⟩, a, b⟩ := p
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have ha := a.isLt
  have hb := b.isLt
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      dsimp [splitCell, joinCell]
      simp only [ZMod.val_natCast]
      omega
    · apply Prod.ext <;> apply Fin.ext <;>
        dsimp [splitCell, joinCell] <;> simp only [ZMod.val_natCast] <;> omega
  · apply Prod.ext <;> apply Fin.ext <;>
      dsimp [splitCell, joinCell] <;> simp only [ZMod.val_natCast] <;> omega

def cellEquiv : Cell20 ≃ SplitCell where
  toFun := splitCell
  invFun := joinCell
  left_inv := join_split
  right_inv := split_join

theorem coset_count : Fintype.card Coset = 4 := by norm_num [Coset]

theorem index_four : Fintype.card Cell20 = 4 * Fintype.card PrimitiveYee.Cell := by
  rw [PeriodicYee.cell_count, PrimitiveYee.cell_count]

noncomputable section

def rawCoordinate (r : Cell20) : PrimitiveYee.RawCell := fun j => (r j).val

theorem split_matches_reduction (r : Cell20) :
    (splitCell r).1 = PrimitiveYee.reduceCell (rawCoordinate r) := by
  have h0 := ZMod.val_lt (r 0)
  have h1 := ZMod.val_lt (r 1)
  have h2 := ZMod.val_lt (r 2)
  have hr : PrimitiveYee.reconstruct (splitCell r).1
      (PrimitiveYee.reduceTranslation (rawCoordinate r)) = rawCoordinate r := by
    funext j
    fin_cases j <;>
      dsimp [PrimitiveYee.reconstruct, PrimitiveYee.representative,
        PrimitiveYee.latticeVector, PrimitiveYee.reduceTranslation, rawCoordinate, splitCell] <;>
      omega
  rw [← hr, PrimitiveYee.reduceCell_reconstruct]

theorem translation_coset_one (r : Cell20) :
    PrimitiveYee.reduceTranslation (rawCoordinate r) 1 = ((splitCell r).2.1.val : ℤ) := by
  dsimp [PrimitiveYee.reduceTranslation, rawCoordinate, splitCell]

theorem translation_coset_two (r : Cell20) :
    PrimitiveYee.reduceTranslation (rawCoordinate r) 2 = ((splitCell r).2.2.val : ℤ) := by
  dsimp [PrimitiveYee.reduceTranslation, rawCoordinate, splitCell]

theorem character_momentum_add (k l : Momentum) (n : PrimitiveYee.Translation) :
    PrimitiveYee.character (k + l) n =
      PrimitiveYee.character k n * PrimitiveYee.character l n := by
  simp only [PrimitiveYee.character, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    Complex.ofReal_add, mul_add, Complex.exp_add]

def sectorTranslation (a : Coset) : PrimitiveYee.Translation := ![0, a.1.val, a.2.val]

def sectorMomentum (k : Momentum) (a : Coset) : Momentum :=
  k + PrimitiveYee.timeReversalMomentum (sectorTranslation a)

def conventionalMomentum (k : Momentum) : Momentum :=
  ![k 0, 2 * k 1 - k 0, 2 * k 2 - k 0]

def standardTranslation (j : Direction) : PrimitiveYee.Translation :=
  if j = 0 then ![1, 0, 0] else if j = 1 then ![-1, 2, 0] else ![-1, 0, 2]

theorem standardTranslation_vector (j : Direction) :
    PrimitiveYee.latticeVector (standardTranslation j) = 20 • PrimitiveYee.rawUnit j := by
  funext i
  fin_cases j <;> fin_cases i <;>
    norm_num [PrimitiveYee.latticeVector, PrimitiveYee.rawUnit, standardTranslation,
      Pi.single_apply]

def wrapTranslation (j : Direction) (r : Cell20) : PrimitiveYee.Translation :=
  if r j = 19 then standardTranslation j else 0

theorem raw_forward_relation (j : Direction) (r : Cell20) :
    rawCoordinate r + PrimitiveYee.rawUnit j =
      rawCoordinate (PeriodicYee.forwardCell j r) +
        PrimitiveYee.latticeVector (wrapTranslation j r) := by
  have hv : ((r j).val : ℤ) + 1 = ((r j + 1).val : ℤ) +
      if r j = 19 then 20 else 0 := by
    have hb := ZMod.val_lt (r j)
    have he : r j = 19 ↔ (r j).val = 19 := by
      constructor
      · intro h; rw [h]; decide
      · intro h
        apply ZMod.val_injective
        simpa only [show (19 : ZMod 20).val = 19 by decide] using h
    simp only [ZMod.val_add, he, show (1 : ZMod 20).val = 1 by decide]
    split_ifs <;> omega
  funext i
  fin_cases j <;> fin_cases i <;>
    simp [rawCoordinate, PeriodicYee.forwardCell, PeriodicYee.unitCell,
      PrimitiveYee.rawUnit, wrapTranslation, PrimitiveYee.latticeVector,
      standardTranslation] at hv ⊢ <;>
    split_ifs at hv ⊢ <;> simp_all

theorem character_standardTranslation (k : Momentum) (j : Direction) :
    PrimitiveYee.character k (standardTranslation j) =
      Complex.exp (Complex.I * (conventionalMomentum k j : ℂ)) := by
  fin_cases j <;>
    simp [PrimitiveYee.character, standardTranslation, conventionalMomentum,
      Fin.sum_univ_three] <;> congr 1 <;> ring

theorem character_wrapTranslation (k : Momentum) (j : Direction) (r : Cell20) :
    PrimitiveYee.character k (wrapTranslation j r) =
      PeriodicYee.boundaryPhase (conventionalMomentum k) j r := by
  by_cases h : r j = 19 <;>
    simp [wrapTranslation, PeriodicYee.boundaryPhase, h,
      character_standardTranslation, PrimitiveYee.character_zero]

/-- Restrict a primitive quasiperiodic field to the conventional cube. -/
def liftField (k : Momentum) (v : PrimitiveYee.Cell → ℂ) (r : Cell20) : ℂ :=
  PrimitiveYee.extend k v (rawCoordinate r)

theorem conventional_difference_mulVec (q : Momentum) (j : Direction)
    (v : Cell20 → ℂ) (r : Cell20) :
    (PeriodicYee.difference q j *ᵥ v) r =
      PeriodicYee.boundaryPhase q j r * v (PeriodicYee.forwardCell j r) - v r := by
  simp [PeriodicYee.difference, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, ite_mul]

/-- Actual forward Yee differences intertwine under the primitive-to-
conventional quasiperiodic lift, with the required momentum conversion. -/
theorem difference_intertwining (k : Momentum) (j : Direction)
    (v : PrimitiveYee.Cell → ℂ) :
    PeriodicYee.difference (conventionalMomentum k) j *ᵥ liftField k v =
      liftField k (PrimitiveYee.difference k j *ᵥ v) := by
  funext r
  rw [conventional_difference_mulVec]
  change _ = PrimitiveYee.extend k (PrimitiveYee.difference k j *ᵥ v) (rawCoordinate r)
  rw [PrimitiveYee.extend_difference, raw_forward_relation,
    PrimitiveYee.extend_translate, character_wrapTranslation]
  rfl

def liftingMatrix (k : Momentum) : Matrix Cell20 PrimitiveYee.Cell ℂ :=
  fun r p => if p = PrimitiveYee.reduceCell (rawCoordinate r) then
    PrimitiveYee.character k (PrimitiveYee.reduceTranslation (rawCoordinate r)) else 0

theorem liftingMatrix_mulVec (k : Momentum) (v : PrimitiveYee.Cell → ℂ) :
    liftingMatrix k *ᵥ v = liftField k v := by
  funext r
  simp [liftingMatrix, Matrix.mulVec, dotProduct, ite_mul, liftField, PrimitiveYee.extend]

theorem difference_intertwining_matrix (k : Momentum) (j : Direction) :
    PeriodicYee.difference (conventionalMomentum k) j * liftingMatrix k =
      liftingMatrix k * PrimitiveYee.difference k j := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simpa only [← Matrix.mulVec_mulVec, liftingMatrix_mulVec] using difference_intertwining k j v

def conventionalShift (k : Momentum) (j : Direction) : Matrix Cell20 Cell20 ℂ :=
  fun r s => if s = PeriodicYee.forwardCell j r then PeriodicYee.boundaryPhase k j r else 0

theorem conventionalPhase_unit (k : Momentum) (j : Direction) (r : Cell20) :
    PeriodicYee.boundaryPhase k j r * star (PeriodicYee.boundaryPhase k j r) = 1 := by
  unfold PeriodicYee.boundaryPhase
  split_ifs
  · change Complex.exp _ * starRingEnd ℂ (Complex.exp _) = _
    rw [Complex.mul_conj', Complex.norm_exp_I_mul_ofReal]
    norm_num
  · simp

theorem conventionalShift_mul_conjTranspose (k : Momentum) (j : Direction) :
    conventionalShift k j * (conventionalShift k j).conjTranspose = 1 := by
  ext r s
  by_cases h : r = s
  · subst s
    simpa [conventionalShift, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul] using
      conventionalPhase_unit k j r
  · have hf : PeriodicYee.forwardCell j r ≠ PeriodicYee.forwardCell j s := by
      intro hh
      apply h
      exact add_right_cancel hh
    simp [conventionalShift, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul, hf, h]

theorem conventionalShift_conjTranspose_mul (k : Momentum) (j : Direction) :
    (conventionalShift k j).conjTranspose * conventionalShift k j = 1 :=
  mul_eq_one_comm.mp (conventionalShift_mul_conjTranspose k j)

theorem conventional_difference_eq_shift_sub_one (k : Momentum) (j : Direction) :
    PeriodicYee.difference k j = conventionalShift k j - 1 := by
  ext r s
  simp [PeriodicYee.difference, conventionalShift, Matrix.one_apply, eq_comm]

private theorem adjoint_intertwining {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (S : Matrix n n ℂ) (T : Matrix m m ℂ)
    (L : Matrix n m ℂ) (h : S * L = L * T)
    (hS : S.conjTranspose * S = 1) (hT : T * T.conjTranspose = 1) :
    S.conjTranspose * L = L * T.conjTranspose := by
  calc
    S.conjTranspose * L = S.conjTranspose * (L * (T * T.conjTranspose)) := by
      rw [hT, Matrix.mul_one]
    _ = (S.conjTranspose * (L * T)) * T.conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = (S.conjTranspose * (S * L)) * T.conjTranspose := by rw [← h]
    _ = L * T.conjTranspose := by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]

theorem difference_adjoint_intertwining_matrix (k : Momentum) (j : Direction) :
    (PeriodicYee.difference (conventionalMomentum k) j).conjTranspose * liftingMatrix k =
      liftingMatrix k * (PrimitiveYee.difference k j).conjTranspose := by
  have hs : conventionalShift (conventionalMomentum k) j * liftingMatrix k =
      liftingMatrix k * PrimitiveYee.shift k j := by
    have hd := difference_intertwining_matrix k j
    rw [conventional_difference_eq_shift_sub_one, PrimitiveYee.difference_eq_shift_sub_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one] at hd
    exact sub_left_injective hd
  have ht := adjoint_intertwining _ _ _ hs
    (conventionalShift_conjTranspose_mul (conventionalMomentum k) j)
    (PrimitiveYee.shift_mul_conjTranspose k j)
  simp only [conventional_difference_eq_shift_sub_one, PrimitiveYee.difference_eq_shift_sub_one,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, ht]

theorem difference_adjoint_intertwining (k : Momentum) (j : Direction)
    (v : PrimitiveYee.Cell → ℂ) :
    (PeriodicYee.difference (conventionalMomentum k) j).conjTranspose *ᵥ liftField k v =
      liftField k ((PrimitiveYee.difference k j).conjTranspose *ᵥ v) := by
  have h := congrArg (fun A => A *ᵥ v) (difference_adjoint_intertwining_matrix k j)
  simpa only [← Matrix.mulVec_mulVec, liftingMatrix_mulVec] using h

theorem liftField_sub (k : Momentum) (u v : PrimitiveYee.Cell → ℂ) :
    liftField k (u - v) = liftField k u - liftField k v := by
  funext r
  simp [liftField, PrimitiveYee.extend, mul_sub]

def liftElectric (k : Momentum) (v : PrimitiveYee.Electric → ℂ) (e : Electric20) : ℂ :=
  liftField k (fun p => v (e.1, p)) e.2

theorem conventional_curl_mulVec (k : Momentum) (v : Electric20 → ℂ)
    (d : Direction) (p : Cell20) :
    (PeriodicYee.curl k *ᵥ v) (d, p) =
      if d = 0 then
        (PeriodicYee.difference k 1 *ᵥ fun q => v (2, q)) p -
          (PeriodicYee.difference k 2 *ᵥ fun q => v (1, q)) p
      else if d = 1 then
        (PeriodicYee.difference k 2 *ᵥ fun q => v (0, q)) p -
          (PeriodicYee.difference k 0 *ᵥ fun q => v (2, q)) p
      else
        (PeriodicYee.difference k 0 *ᵥ fun q => v (1, q)) p -
          (PeriodicYee.difference k 1 *ᵥ fun q => v (0, q)) p := by
  fin_cases d <;>
    simp [PeriodicYee.curl, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_three, neg_mul, Finset.sum_neg_distrib] <;> ring

theorem curl_intertwining (k : Momentum) (v : PrimitiveYee.Electric → ℂ) :
    PeriodicYee.curl (conventionalMomentum k) *ᵥ liftElectric k v =
      liftElectric k (PrimitiveYee.curl k *ᵥ v) := by
  funext e
  obtain ⟨d, r⟩ := e
  fin_cases d <;>
    norm_num only [conventional_curl_mulVec, liftElectric, PrimitiveYee.curl_mulVec] <;>
    simp only [difference_intertwining] <;>
    simp [liftField, PrimitiveYee.extend, mul_sub]

theorem conventional_curl_adjoint_mulVec (k : Momentum) (v : Face20 → ℂ)
    (d : Direction) (p : Cell20) :
    ((PeriodicYee.curl k).conjTranspose *ᵥ v) (d, p) =
      if d = 0 then
        ((PeriodicYee.difference k 2).conjTranspose *ᵥ fun q => v (1, q)) p -
          ((PeriodicYee.difference k 1).conjTranspose *ᵥ fun q => v (2, q)) p
      else if d = 1 then
        ((PeriodicYee.difference k 0).conjTranspose *ᵥ fun q => v (2, q)) p -
          ((PeriodicYee.difference k 2).conjTranspose *ᵥ fun q => v (0, q)) p
      else
        ((PeriodicYee.difference k 1).conjTranspose *ᵥ fun q => v (0, q)) p -
          ((PeriodicYee.difference k 0).conjTranspose *ᵥ fun q => v (1, q)) p := by
  fin_cases d <;>
    simp [PeriodicYee.curl, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_three, Matrix.conjTranspose_apply, neg_mul,
      Finset.sum_neg_distrib] <;> ring

theorem curl_adjoint_intertwining (k : Momentum) (v : PrimitiveYee.Face → ℂ) :
    (PeriodicYee.curl (conventionalMomentum k)).conjTranspose *ᵥ liftElectric k v =
      liftElectric k ((PrimitiveYee.curl k).conjTranspose *ᵥ v) := by
  funext e
  obtain ⟨d, r⟩ := e
  fin_cases d <;>
    norm_num only [conventional_curl_adjoint_mulVec, liftElectric,
      PrimitiveYee.curl_adjoint_mulVec] <;>
    simp only [difference_adjoint_intertwining] <;>
    simp [liftField, PrimitiveYee.extend, mul_sub]

theorem curlGram_intertwining (k : Momentum) (v : PrimitiveYee.Electric → ℂ) :
    ((PeriodicYee.curl (conventionalMomentum k)).conjTranspose *
        PeriodicYee.curl (conventionalMomentum k)) *ᵥ liftElectric k v =
      liftElectric k (((PrimitiveYee.curl k).conjTranspose * PrimitiveYee.curl k) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, curl_intertwining, curl_adjoint_intertwining,
    Matrix.mulVec_mulVec]

theorem conventionalCell_rawCoordinate (r : Cell20) :
    PrimitiveYee.conventionalCell (rawCoordinate r) = r := by
  funext j
  simp [PrimitiveYee.conventionalCell, rawCoordinate]

/-- FCC periodicity is a constitutive property, separate from all spectral
or folding conclusions. -/
def FCCPeriodic (material : Cell20 → ℝ) : Prop :=
  ∀ (r : PrimitiveYee.RawCell) (n : PrimitiveYee.Translation),
    material (PrimitiveYee.conventionalCell (r + PrimitiveYee.latticeVector n)) =
      material (PrimitiveYee.conventionalCell r)

theorem edgeAverage_translate (material : Cell20 → ℝ) (hmat : FCCPeriodic material)
    (d : Direction) (r : PrimitiveYee.RawCell) (n : PrimitiveYee.Translation) :
    PeriodicYee.edgeAverage material
      (d, PrimitiveYee.conventionalCell (r + PrimitiveYee.latticeVector n)) =
    PeriodicYee.edgeAverage material (d, PrimitiveYee.conventionalCell r) := by
  have hshift (t s : PrimitiveYee.RawCell) :
      t + PrimitiveYee.latticeVector n - s = (t - s) + PrimitiveYee.latticeVector n := by
    abel
  unfold FCCPeriodic at hmat
  simp only [PeriodicYee.edgeAverage, ← PrimitiveYee.conventionalCell_rawUnit,
    ← PrimitiveYee.conventionalCell_sub, hshift, hmat]

theorem edgeAverage_reduce (material : Cell20 → ℝ) (hmat : FCCPeriodic material)
    (d : Direction) (r : Cell20) :
    PeriodicYee.edgeAverage material (d, r) =
      PrimitiveYee.edgeAverage material (d, PrimitiveYee.reduceCell (rawCoordinate r)) := by
  rw [PrimitiveYee.edgeAverage_binding]
  calc
    PeriodicYee.edgeAverage material (d, r) =
        PeriodicYee.edgeAverage material (d, PrimitiveYee.conventionalCell (rawCoordinate r)) := by
      rw [conventionalCell_rawCoordinate]
    _ = _ := by
      conv_lhs => rw [← PrimitiveYee.reconstruct_reduce (rawCoordinate r)]
      exact edgeAverage_translate material hmat d _ _

theorem mass_intertwining (material : Cell20 → ℝ) (hmat : FCCPeriodic material)
    (k : Momentum) (v : PrimitiveYee.Electric → ℂ) :
    PeriodicYee.mass material *ᵥ liftElectric k v =
      liftElectric k (PrimitiveYee.mass material *ᵥ v) := by
  funext e
  obtain ⟨d, r⟩ := e
  simp only [PeriodicYee.mass, PrimitiveYee.mass, Matrix.mulVec_diagonal,
    liftElectric, liftField, PrimitiveYee.extend]
  rw [edgeAverage_reduce material hmat]
  ring

theorem liftElectric_sub (k : Momentum) (u v : PrimitiveYee.Electric → ℂ) :
    liftElectric k (u - v) = liftElectric k u - liftElectric k v := by
  funext e
  simp [liftElectric, liftField, PrimitiveYee.extend, mul_sub]

theorem liftElectric_smul (k : Momentum) (c : ℂ) (v : PrimitiveYee.Electric → ℂ) :
    liftElectric k (c • v) = c • liftElectric k v := by
  funext e
  simp [liftElectric, liftField, PrimitiveYee.extend, mul_left_comm]

theorem fiber_intertwining (material : Cell20 → ℝ) (hmat : FCCPeriodic material)
    (k : Momentum) (v : PrimitiveYee.Electric → ℂ) :
    PeriodicYee.fiber material (conventionalMomentum k) *ᵥ liftElectric k v =
      liftElectric k (PrimitiveYee.fiber material k *ᵥ v) := by
  simp only [PeriodicYee.fiber, PrimitiveYee.fiber, Matrix.sub_mulVec,
    Matrix.smul_mulVec, liftElectric_sub, liftElectric_smul,
    curlGram_intertwining, mass_intertwining material hmat]

def sign (a b : Fin 2) : ℂ := if a = 1 ∧ b = 1 then -1 else 1

def quotientFourier : Matrix Coset Coset ℂ :=
  fun a b => sign a.1 b.1 * sign a.2 b.2 / 2

theorem quotientFourier_conjTranspose : quotientFourier.conjTranspose = quotientFourier := by
  ext a b
  obtain ⟨a₀, a₁⟩ := a
  obtain ⟨b₀, b₁⟩ := b
  fin_cases a₀ <;> fin_cases a₁ <;> fin_cases b₀ <;> fin_cases b₁ <;>
    norm_num [quotientFourier, sign, Matrix.conjTranspose_apply]

theorem quotientFourier_square : quotientFourier * quotientFourier = 1 := by
  ext a b
  obtain ⟨a₀, a₁⟩ := a
  obtain ⟨b₀, b₁⟩ := b
  fin_cases a₀ <;> fin_cases a₁ <;> fin_cases b₀ <;> fin_cases b₁ <;>
    norm_num [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      quotientFourier, sign, Matrix.one_apply]

theorem quotientFourier_unitary :
    quotientFourier.conjTranspose * quotientFourier = 1 ∧
      quotientFourier * quotientFourier.conjTranspose = 1 := by
  rw [quotientFourier_conjTranspose]
  exact ⟨quotientFourier_square, quotientFourier_square⟩

theorem sector_character (k : Momentum) (a : Coset) (r : Cell20) :
    PrimitiveYee.character (sectorMomentum k a)
        (PrimitiveYee.reduceTranslation (rawCoordinate r)) =
      PrimitiveYee.character k (PrimitiveYee.reduceTranslation (rawCoordinate r)) *
        (sign a.1 (splitCell r).2.1 * sign a.2 (splitCell r).2.2) := by
  rw [sectorMomentum, character_momentum_add, PrimitiveYee.character_timeReversal]
  congr 1
  simp only [sectorTranslation, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, zero_mul, zero_add,
    translation_coset_one, translation_coset_two]
  generalize (splitCell r).2.1 = b₀
  generalize (splitCell r).2.2 = b₁
  obtain ⟨a₀, a₁⟩ := a
  fin_cases a₀ <;> fin_cases a₁ <;> fin_cases b₀ <;> fin_cases b₁ <;>
    norm_num [sign]

theorem sector_character_standard (k : Momentum) (a : Coset) (j : Direction) :
    PrimitiveYee.character (sectorMomentum k a) (standardTranslation j) =
      PrimitiveYee.character k (standardTranslation j) := by
  rw [sectorMomentum, character_momentum_add, PrimitiveYee.character_timeReversal]
  have h : (-1 : ℂ) ^ (∑ i, sectorTranslation a i * standardTranslation j i) = 1 := by
    obtain ⟨a₀, a₁⟩ := a
    fin_cases a₀ <;> fin_cases a₁ <;> fin_cases j <;>
      norm_num [sectorTranslation, standardTranslation, Fin.sum_univ_three]
  rw [h, mul_one]

theorem sector_boundaryPhase (k : Momentum) (a : Coset) (j : Direction) (r : Cell20) :
    PeriodicYee.boundaryPhase (conventionalMomentum (sectorMomentum k a)) j r =
      PeriodicYee.boundaryPhase (conventionalMomentum k) j r := by
  rw [← character_wrapTranslation, ← character_wrapTranslation]
  unfold wrapTranslation
  split_ifs
  · exact sector_character_standard k a j
  · simp only [PrimitiveYee.character_zero]

theorem sector_conventional_fiber (material : Cell20 → ℝ) (k : Momentum) (a : Coset) :
    PeriodicYee.fiber material (conventionalMomentum (sectorMomentum k a)) =
      PeriodicYee.fiber material (conventionalMomentum k) := by
  have hd (j : Direction) :
      PeriodicYee.difference (conventionalMomentum (sectorMomentum k a)) j =
        PeriodicYee.difference (conventionalMomentum k) j := by
    ext r s
    simp only [PeriodicYee.difference, sector_boundaryPhase]
  have hc : PeriodicYee.curl (conventionalMomentum (sectorMomentum k a)) =
      PeriodicYee.curl (conventionalMomentum k) := by
    ext e f
    simp only [PeriodicYee.curl, hd]
  simp only [PeriodicYee.fiber, hc]

def sectorEquiv : Cell20 ≃ Coset × PrimitiveYee.Cell :=
  cellEquiv.trans (Equiv.prodComm _ _)

/-- The normalized four-character transform, independently at every
primitive cell. -/
def splitFourier : Matrix (Coset × PrimitiveYee.Cell) (Coset × PrimitiveYee.Cell) ℂ :=
  Matrix.blockDiagonal fun _ : PrimitiveYee.Cell => quotientFourier

theorem splitFourier_conjTranspose : splitFourier.conjTranspose = splitFourier := by
  simp [splitFourier, quotientFourier_conjTranspose]

theorem splitFourier_square : splitFourier * splitFourier = 1 := by
  unfold splitFourier
  rw [← Matrix.blockDiagonal_mul]
  simp only [quotientFourier_square]
  exact Matrix.blockDiagonal_one

/-- The same unitary in the exact conventional cell indexing. The Bloch
gauge and the operator intertwining are separate from this Fourier matrix. -/
def conventionalFourier : Matrix Cell20 Cell20 ℂ :=
  Matrix.reindex sectorEquiv.symm sectorEquiv.symm splitFourier

theorem conventionalFourier_conjTranspose :
    conventionalFourier.conjTranspose = conventionalFourier := by
  unfold conventionalFourier
  rw [Matrix.conjTranspose_reindex, splitFourier_conjTranspose]

theorem conventionalFourier_square : conventionalFourier * conventionalFourier = 1 := by
  change Matrix.reindexRingEquiv ℂ sectorEquiv.symm splitFourier *
    Matrix.reindexRingEquiv ℂ sectorEquiv.symm splitFourier = 1
  rw [← map_mul, splitFourier_square, map_one]

theorem conventionalFourier_unitary :
    conventionalFourier.conjTranspose * conventionalFourier = 1 ∧
      conventionalFourier * conventionalFourier.conjTranspose = 1 := by
  rw [conventionalFourier_conjTranspose]
  exact ⟨conventionalFourier_square, conventionalFourier_square⟩

def scalarGauge (k : Momentum) : Matrix Cell20 Cell20 ℂ :=
  Matrix.diagonal fun r =>
    PrimitiveYee.character k (PrimitiveYee.reduceTranslation (rawCoordinate r))

theorem scalarGauge_unitary (k : Momentum) :
    (scalarGauge k).conjTranspose * scalarGauge k = 1 := by
  ext r s
  simp only [scalarGauge, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have hu := PrimitiveYee.character_unit k
    (PrimitiveYee.reduceTranslation (rawCoordinate r))
  by_cases h : r = s
  · subst s
    simpa using hu
  · simp [h]

/-- The actual Bloch gauge followed by the normalized quotient transform. -/
def scalarFold (k : Momentum) : Matrix Cell20 Cell20 ℂ :=
  scalarGauge k * conventionalFourier

theorem scalarFold_unitary (k : Momentum) :
    (scalarFold k).conjTranspose * scalarFold k = 1 ∧
      scalarFold k * (scalarFold k).conjTranspose = 1 := by
  have h : (scalarFold k).conjTranspose * scalarFold k = 1 := by
    simp only [scalarFold, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (scalarGauge k).conjTranspose, scalarGauge_unitary]
    simpa only [Matrix.one_mul] using conventionalFourier_unitary.1
  exact ⟨h, mul_eq_one_comm.mp h⟩

theorem scalarFold_apply (k : Momentum) (r s : Cell20) :
    scalarFold k r s =
      if (splitCell r).1 = (splitCell s).1 then
        PrimitiveYee.character (sectorMomentum k (splitCell s).2)
          (PrimitiveYee.reduceTranslation (rawCoordinate r)) / 2
      else 0 := by
  rw [scalarFold, scalarGauge, Matrix.diagonal_mul]
  change PrimitiveYee.character k (PrimitiveYee.reduceTranslation (rawCoordinate r)) *
    (if (splitCell r).1 = (splitCell s).1 then
      sign (splitCell r).2.1 (splitCell s).2.1 *
        sign (splitCell r).2.2 (splitCell s).2.2 / 2 else 0) = _
  by_cases h : (splitCell r).1 = (splitCell s).1
  · simp only [h, ite_true, sector_character]
    have hs (a b : Fin 2) : sign a b = sign b a := by simp [sign, and_comm]
    rw [hs (splitCell r).2.1, hs (splitCell r).2.2]
    ring
  · simp only [h, ite_false, mul_zero]

def electricFold (k : Momentum) : Matrix Electric20 Electric20 ℂ :=
  Matrix.reindex (Equiv.prodComm Cell20 Direction) (Equiv.prodComm Cell20 Direction)
    (Matrix.blockDiagonal fun _ : Direction => scalarFold k)

theorem electricFold_unitary (k : Momentum) :
    (electricFold k).conjTranspose * electricFold k = 1 ∧
      electricFold k * (electricFold k).conjTranspose = 1 := by
  have h : (electricFold k).conjTranspose * electricFold k = 1 := by
    unfold electricFold
    rw [Matrix.conjTranspose_reindex, Matrix.blockDiagonal_conjTranspose]
    change Matrix.reindexRingEquiv ℂ (Equiv.prodComm Cell20 Direction)
        (Matrix.blockDiagonal fun _ : Direction => (scalarFold k).conjTranspose) *
      Matrix.reindexRingEquiv ℂ (Equiv.prodComm Cell20 Direction)
        (Matrix.blockDiagonal fun _ : Direction => scalarFold k) = 1
    rw [← map_mul, ← Matrix.blockDiagonal_mul]
    simp only [(scalarFold_unitary k).1]
    change Matrix.reindexRingEquiv ℂ (Equiv.prodComm Cell20 Direction)
      (Matrix.blockDiagonal (1 : Direction → Matrix Cell20 Cell20 ℂ)) = 1
    rw [Matrix.blockDiagonal_one, map_one]
  exact ⟨h, mul_eq_one_comm.mp h⟩

theorem electricFold_apply (k : Momentum) (e f : Electric20) :
    electricFold k e f = if e.1 = f.1 then scalarFold k e.2 f.2 else 0 := by
  rfl

def electricEquiv : Electric20 ≃ PrimitiveYee.Electric × Coset :=
  ((Equiv.refl Direction).prodCongr cellEquiv).trans
    (Equiv.prodAssoc Direction PrimitiveYee.Cell Coset).symm

theorem electricEquiv_symm_apply (p : PrimitiveYee.Electric) (a : Coset) :
    electricEquiv.symm (p, a) = (p.1, joinCell (p.2, a)) := rfl

def foldingMatrix (k : Momentum) : Matrix Electric20 (PrimitiveYee.Electric × Coset) ℂ :=
  Matrix.reindex (Equiv.refl Electric20) electricEquiv (electricFold k)

theorem foldingMatrix_unitary (k : Momentum) :
    (foldingMatrix k).conjTranspose * foldingMatrix k = 1 ∧
      foldingMatrix k * (foldingMatrix k).conjTranspose = 1 := by
  constructor
  · unfold foldingMatrix
    rw [Matrix.conjTranspose_reindex]
    change (electricFold k).conjTranspose.submatrix electricEquiv.symm (Equiv.refl _) *
      (electricFold k).submatrix (Equiv.refl _) electricEquiv.symm = 1
    rw [Matrix.submatrix_mul_equiv, (electricFold_unitary k).1,
      Matrix.submatrix_one_equiv]
  · unfold foldingMatrix
    rw [Matrix.conjTranspose_reindex]
    change (electricFold k).submatrix (Equiv.refl _) electricEquiv.symm *
      (electricFold k).conjTranspose.submatrix electricEquiv.symm (Equiv.refl _) = 1
    rw [Matrix.submatrix_mul_equiv, (electricFold_unitary k).2,
      Matrix.submatrix_one_equiv]

def electricLiftingMatrix (k : Momentum) : Matrix Electric20 PrimitiveYee.Electric ℂ :=
  fun e p => if p = (e.1, PrimitiveYee.reduceCell (rawCoordinate e.2)) then
    PrimitiveYee.character k (PrimitiveYee.reduceTranslation (rawCoordinate e.2)) else 0

theorem electricLiftingMatrix_mulVec (k : Momentum) (v : PrimitiveYee.Electric → ℂ) :
    electricLiftingMatrix k *ᵥ v = liftElectric k v := by
  ext e
  simp [electricLiftingMatrix, Matrix.mulVec, dotProduct, liftElectric, liftField,
    PrimitiveYee.extend]

theorem foldingMatrix_apply (k : Momentum) (e : Electric20)
    (p : PrimitiveYee.Electric) (a : Coset) :
    foldingMatrix k e (p, a) = electricLiftingMatrix (sectorMomentum k a) e p / 2 := by
  change electricFold k e (electricEquiv.symm (p, a)) = _
  rw [electricEquiv_symm_apply, electricFold_apply, scalarFold_apply, split_join]
  obtain ⟨d, p⟩ := p
  simp only [electricLiftingMatrix, Prod.mk.injEq, ← split_matches_reduction]
  by_cases hd : e.1 = d
  · by_cases hp : (splitCell e.2).1 = p
    · simp [hd, hp]
    · simp [hd, hp, Ne.symm hp]
  · simp [hd, Ne.symm hd]

theorem electricLiftingMatrix_intertwining (material : Cell20 → ℝ)
    (hmat : FCCPeriodic material) (k : Momentum) (a : Coset) :
    PeriodicYee.fiber material (conventionalMomentum k) *
        electricLiftingMatrix (sectorMomentum k a) =
      electricLiftingMatrix (sectorMomentum k a) *
        PrimitiveYee.fiber material (sectorMomentum k a) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  simp only [← Matrix.mulVec_mulVec, electricLiftingMatrix_mulVec]
  rw [← sector_conventional_fiber material k a]
  exact fiber_intertwining material hmat (sectorMomentum k a) v

def normalizedLift (k : Momentum) (a : Coset) :
    Matrix Electric20 PrimitiveYee.Electric ℂ :=
  (2⁻¹ : ℂ) • electricLiftingMatrix (sectorMomentum k a)

theorem normalizedLift_intertwining (material : Cell20 → ℝ)
    (hmat : FCCPeriodic material) (k : Momentum) (a : Coset) :
    PeriodicYee.fiber material (conventionalMomentum k) * normalizedLift k a =
      normalizedLift k a * PrimitiveYee.fiber material (sectorMomentum k a) := by
  simp only [normalizedLift, Matrix.mul_smul, Matrix.smul_mul,
    electricLiftingMatrix_intertwining material hmat]

theorem foldingMatrix_normalizedLift (k : Momentum) (e : Electric20)
    (p : PrimitiveYee.Electric) (a : Coset) :
    foldingMatrix k e (p, a) = normalizedLift k a e p := by
  rw [foldingMatrix_apply]
  simp only [normalizedLift, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem foldingMatrix_eq_sectorLift (k : Momentum) :
    foldingMatrix k = sectorLift (normalizedLift k) := by
  ext e p
  exact foldingMatrix_normalizedLift k e p.1 p.2

/-- Exact unitary index-four folding of the actual Yee operator.  The only
material hypothesis is scalar FCC periodicity.  The four blocks have 6000
electric unknowns each and their Bloch phases are stated explicitly above. -/
theorem fiber_folding (material : Cell20 → ℝ) (hmat : FCCPeriodic material)
    (k : Momentum) :
    (foldingMatrix k).conjTranspose * PeriodicYee.fiber material (conventionalMomentum k) *
        foldingMatrix k =
      sectorDiagonal (fun a => PrimitiveYee.fiber material (sectorMomentum k a)) := by
  have hu : (sectorLift (normalizedLift k)).conjTranspose *
      sectorLift (normalizedLift k) = 1 := by
    rw [← foldingMatrix_eq_sectorLift]
    exact (foldingMatrix_unitary k).1
  rw [foldingMatrix_eq_sectorLift]
  exact sectorLift_folding _ _ _ (normalizedLift_intertwining material hmat k) hu

theorem fiber_folding_intertwining (material : Cell20 → ℝ) (hmat : FCCPeriodic material)
    (k : Momentum) :
    PeriodicYee.fiber material (conventionalMomentum k) * foldingMatrix k =
      foldingMatrix k *
        sectorDiagonal (fun a => PrimitiveYee.fiber material (sectorMomentum k a)) := by
  rw [foldingMatrix_eq_sectorLift]
  exact sectorLift_intertwining _ _ _ (normalizedLift_intertwining material hmat k)

end
end Maxwell.Spectral.Folding
