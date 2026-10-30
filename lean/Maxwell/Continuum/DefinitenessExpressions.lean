import Maxwell.Continuum.RationalExpressionSound
import Maxwell.Continuum.RawDefiniteness

/-! A fixed symbolic Schur circuit. The input matrix entries remain runtime
words. Expression duplication depends only on the fixed matrix dimension. -/

namespace Maxwell.Continuum.Calibration.ExpressionDefiniteness

open RationalDataflow

def evaluate {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression) (v : ℕ → Parts) :
    Matrix (Fin n) (Fin n) Parts := fun i j => (A i j).evaluate v

def schur {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) RationalExpression) :
    Matrix (Fin n) (Fin n) RationalExpression := fun i j =>
  .binary .sub (A i.succ j.succ)
    (.binary .mul (.binary .mul (A i.succ 0) (A 0 j.succ)) (.inverse (A 0 0)))

def Below {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression) (s : ℕ) : Prop :=
  ∀ i j, (A i j).Below s

def Safe {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression) (v : ℕ → Parts) : Prop :=
  ∀ i j, (A i j).Safe v

theorem schur_below {n s : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) RationalExpression)
    (hA : Below A s) : Below (schur A) s := fun _i _j =>
  ⟨hA _ _,⟨hA _ _,hA _ _⟩,hA _ _⟩

theorem evaluate_schur {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) RationalExpression)
    (v : ℕ → Parts) : evaluate (schur A) v=RawDefiniteness.schur (evaluate A v) := rfl

theorem schur_safe {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) RationalExpression)
    (v : ℕ → Parts) (hA : Safe A v) (hp : ((A 0 0).evaluate v).value≠0) :
    Safe (schur A) v := fun _i _j => ⟨hA _ _,⟨hA _ _,hA _ _⟩,hA _ _,hp⟩

theorem evaluate_congr {n s : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression)
    (hA : Below A s) (v w : ℕ → Parts) (hv : ∀ i<s, v i=w i) :
    evaluate A v=evaluate A w := by
  ext i j
  exact (A i j).evaluate_congr s (hA i j) v w hv

theorem safe_congr {n s : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression)
    (hA : Below A s) (v w : ℕ → Parts) (hv : ∀ i<s, v i=w i) : Safe A v ↔ Safe A w := by
  constructor <;> intro h i j
  · exact ((A i j).safe_congr s (hA i j) v w hv).mp (h i j)
  · exact ((A i j).safe_congr s (hA i j) v w hv).mpr (h i j)

def extent : {n : ℕ} → Matrix (Fin n) (Fin n) RationalExpression → ℕ
  | 0,_ => 1
  | _n+1,A => max (A 0 0).nodes (extent (schur A))

theorem extent_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression) : 0<extent A := by
  cases n with
  | zero => exact Nat.zero_lt_one
  | succ n => exact lt_of_lt_of_le (A 0 0).nodes_pos (le_max_left _ _)

def result (out : ℕ) (b : Bool) : Control := .step (.literal out (if b then 1 else 0)) .done

def control : {n : ℕ} → Matrix (Fin n) (Fin n) RationalExpression → ℕ → ℕ → Control
  | 0,_,out,_ => result out true
  | _n+1,A,out,s =>
    (Control.positive ((A 0 0).output s) (control (schur A) out s) (result out false)).prepend
      ((A 0 0).instructions s)

theorem result_evaluate (out : ℕ) (b : Bool) (v : ℕ → Parts) :
    (result out b).evaluate v out=Parts.literal (if b then 1 else 0) := Function.update_self _ _ _

theorem result_valid (out : ℕ) (b : Bool) (S : Finset ℕ) (ho : out∈S) :
    (result out b).Valid S := ⟨ho,trivial⟩

theorem result_widthTrace (out : ℕ) (b : Bool) (S : Finset ℕ) (B : ℕ) (hB : 1≤B)
    (v : ℕ → Parts) (hv : WidthBank S B v) : (result out b).WidthTrace S B v := by
  have hw : (Parts.literal (if b then 1 else 0)).Width B := by
    cases b
    · exact (Parts.literal_width RationalWords.width_zero').mono hB
    · exact (Parts.literal_width RationalWords.width_one).mono hB
  exact ⟨hv,hw,hv.update out hw⟩

theorem control_valid {n : ℕ} (A : Matrix (Fin n) (Fin n) RationalExpression)
    (out s M : ℕ) (ho : out<M) (hA : Below A s) (hM : s+extent A≤M) :
    (control A out s).Valid (Finset.range M) := by
  induction n with
  | zero => exact result_valid out true _ (Finset.mem_range.mpr ho)
  | succ n ih =>
    have hp : s+(A 0 0).slots≤M := by
      have h1 := (A 0 0).slots_le_nodes
      have h2 := le_max_left (A 0 0).nodes (extent (schur A))
      change s+max (A 0 0).nodes (extent (schur A))≤M at hM
      omega
    apply Control.prepend_valid
    · exact (A 0 0).instructions_valid s M (hA 0 0) hp
    · refine ⟨Finset.mem_range.mpr (lt_of_lt_of_le ((A 0 0).output_lt s (hA 0 0)) hp),?_,
        result_valid out false _ (Finset.mem_range.mpr ho)⟩
      apply ih (schur A) (schur_below A hA)
      change s+max (A 0 0).nodes (extent (schur A))≤M at hM
      have := le_max_right (A 0 0).nodes (extent (schur A))
      omega

#print axioms control_valid

end Maxwell.Continuum.Calibration.ExpressionDefiniteness
