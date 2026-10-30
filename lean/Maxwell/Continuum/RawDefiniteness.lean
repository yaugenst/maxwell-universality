import Maxwell.Continuum.RationalDefiniteness
import Maxwell.Continuum.RationalDataflowParts

/-! Exact definiteness testing on unreduced rational words. Each positive-pivot
branch has a proved nonzero reciprocal and a bound on every later matrix. -/

namespace Maxwell.Continuum.Calibration.RawDefiniteness

open RationalDataflow

def values {n : ℕ} (A : Matrix (Fin n) (Fin n) Parts) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (A i j).value

def schur {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) Parts) : Matrix (Fin n) (Fin n) Parts :=
  fun i j => (A i.succ j.succ).sub (((A i.succ 0).mul (A 0 j.succ)).mul (A 0 0).inverse)

def positive : {n : ℕ} → Matrix (Fin n) (Fin n) Parts → Bool
  | 0,_ => true
  | _n+1,A => if 0<(A 0 0).value then positive (schur A) else false

def negate {n : ℕ} (A : Matrix (Fin n) (Fin n) Parts) : Matrix (Fin n) (Fin n) Parts :=
  fun i j => (Parts.literal 0).sub (A i j)

def negative {n : ℕ} (A : Matrix (Fin n) (Fin n) Parts) : Bool := positive (negate A)

def Valid {n : ℕ} (A : Matrix (Fin n) (Fin n) Parts) : Prop := ∀ i j, (A i j).Valid
def Width {n : ℕ} (A : Matrix (Fin n) (Fin n) Parts) (B : ℕ) : Prop := ∀ i j, (A i j).Width B

theorem schur_valid {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) Parts)
    (hA : Valid A) (hp : (A 0 0).value≠0) : Valid (schur A) := by
  intro i j
  exact Parts.sub_valid (hA _ _) (Parts.mul_valid (Parts.mul_valid (hA _ _) (hA _ _))
    (Parts.inverse_valid hp))

theorem schur_values {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) Parts)
    (hA : Valid A) (hp : (A 0 0).value≠0) : values (schur A)=scalarSchur (values A) := by
  ext i j
  rw [values,schur,Parts.sub_value _ _ (hA _ _)
    (Parts.mul_valid (Parts.mul_valid (hA _ _) (hA _ _)) (Parts.inverse_valid hp)),
    Parts.mul_value,Parts.mul_value,Parts.inverse_value _ (hA 0 0) hp]
  rfl

theorem positive_value {n : ℕ} (A : Matrix (Fin n) (Fin n) Parts) (hA : Valid A) :
    positive A=positiveTest (values A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (if 0<(A 0 0).value then positive (schur A) else false)=
      (if 0<(A 0 0).value then positiveTest (scalarSchur (values A)) else false)
    split_ifs with hp
    · rw [ih (schur A) (schur_valid A hA hp.ne'),schur_values A hA hp.ne']
    · rfl

theorem negate_valid {n : ℕ} (A : Matrix (Fin n) (Fin n) Parts) (hA : Valid A) : Valid (negate A) :=
  fun i j => Parts.sub_valid (Parts.literal_valid _) (hA i j)

theorem negate_values {n : ℕ} (A : Matrix (Fin n) (Fin n) Parts) (hA : Valid A) :
    values (negate A)=-(values A) := by
  ext i j
  rw [values,negate,Parts.sub_value _ _ (Parts.literal_valid _) (hA i j),Parts.literal_value,zero_sub]
  rfl

theorem negative_value {n : ℕ} (A : Matrix (Fin n) (Fin n) Parts) (hA : Valid A) :
    negative A=negativeTest (values A) := by
  rw [negative,positive_value _ (negate_valid A hA),negate_values A hA]
  rfl

theorem Width.mono {n B C : ℕ} {A : Matrix (Fin n) (Fin n) Parts} (hA : Width A B) (hBC : B≤C) :
    Width A C := fun i j => (hA i j).mono hBC

theorem schur_width {n W : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) Parts)
    (hA : Width A W) : Width (schur A) (4*W+4) := by
  intro i j
  have h := (hA i.succ j.succ).sub (((hA i.succ 0).mul (hA 0 j.succ)).mul (hA 0 0).inverse)
  unfold schur
  convert h using 1
  ring

theorem negate_width {n W : ℕ} (A : Matrix (Fin n) (Fin n) Parts) (hA : Width A W) :
    Width (negate A) (W+2) := by
  intro i j
  have h := (Parts.literal_width RationalWords.width_zero').sub (hA i j)
  unfold negate
  convert h using 1
  omega

def WidthTrace : {n : ℕ} → Matrix (Fin n) (Fin n) Parts → ℕ → Prop
  | 0,A,B => Width A B
  | _n+1,A,B => Width A B ∧ (0<(A 0 0).value → WidthTrace (schur A) B)

theorem WidthTrace.mono {n B C : ℕ} {A : Matrix (Fin n) (Fin n) Parts}
    (hA : WidthTrace A B) (hBC : B≤C) : WidthTrace A C := by
  induction n with
  | zero => exact Width.mono hA hBC
  | succ n ih => exact ⟨hA.1.mono hBC,fun hp => ih (hA.2 hp)⟩

theorem positive_widthTrace {n W : ℕ} (A : Matrix (Fin n) (Fin n) Parts) (hA : Width A W) :
    WidthTrace A (4^n*(W+2)) := by
  induction n generalizing W with
  | zero => simpa only [WidthTrace,pow_zero,one_mul] using hA.mono (show W≤W+2 by omega)
  | succ n ih =>
    have hbase : W≤4^(n+1)*(W+2) := by
      have hp : 1≤(4 : ℕ)^(n+1) := one_le_pow₀ (by decide)
      nlinarith only [Nat.mul_le_mul_right (W+2) hp]
    refine ⟨hA.mono hbase,fun _ => ?_⟩
    apply (ih (schur A) (schur_width A hA)).mono
    rw [pow_succ]
    nlinarith only [Nat.zero_le ((4 : ℕ)^n)]

theorem negative_widthTrace {n W : ℕ} (A : Matrix (Fin n) (Fin n) Parts) (hA : Width A W) :
    WidthTrace (negate A) (4^n*(W+4)) := by
  exact positive_widthTrace (negate A) (negate_width A hA)

def AdmissibleTrace : {n : ℕ} → Matrix (Fin n) (Fin n) Parts → Prop
  | 0,_ => True
  | _n+1,A => 0<(A 0 0).value → (A 0 0).value≠0 ∧ AdmissibleTrace (schur A)

theorem positive_admissible {n : ℕ} (A : Matrix (Fin n) (Fin n) Parts) (hA : Valid A) :
    AdmissibleTrace A := by
  induction n with
  | zero => trivial
  | succ n ih => exact fun hp => ⟨hp.ne',ih (schur A) (schur_valid A hA hp.ne')⟩

#print axioms negative_value
#print axioms negative_widthTrace
#print axioms positive_admissible

end Maxwell.Continuum.Calibration.RawDefiniteness
