import Maxwell.Certificate.IntervalMatrix

/-! Sound finite complex interval linear algebra.  Proposed intermediate
enclosures can be rounded after every operation; matrix semantics is retained. -/
namespace Maxwell.Certificate.IntervalLinear
open Matrix
open IntervalMatrix Trigonometric

def zero : ComplexRectangle := realRectangle zeroBall

theorem zero_contains : zero.Contains 0 := realRectangle_contains zeroBall_contains

def point (re im : ℚ) : ComplexRectangle :=
  ⟨⟨re, 0, le_rfl⟩, ⟨im, 0, le_rfl⟩⟩

theorem point_contains (re im : ℚ) :
    (point re im).Contains ((re : ℂ) + Complex.I * (im : ℂ)) := by
  constructor <;> simp [point, Ball.Contains]

def round (p : ℕ) (a : ComplexRectangle) : ComplexRectangle :=
  ⟨roundBall p a.re, roundBall p a.im⟩

theorem round_contains (p : ℕ) {a : ComplexRectangle} {z : ℂ}
    (h : a.Contains z) : (round p a).Contains z :=
  ⟨roundBall_contains p h.1, roundBall_contains p h.2⟩

def sum : {n : ℕ} → (Fin n → ComplexRectangle) → ComplexRectangle
  | 0, _ => zero
  | _ + 1, a => (a 0).add (sum (fun i => a i.succ))

theorem sum_contains {n : ℕ} {a : Fin n → ComplexRectangle} {z : Fin n → ℂ}
    (h : ∀ i, (a i).Contains (z i)) : (sum a).Contains (∑ i, z i) := by
  induction n with
  | zero => simpa [sum] using zero_contains
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      exact ComplexRectangle.contains_add (h 0) (ih fun i => h i.succ)

def dot {n : ℕ} (a b : Fin n → ComplexRectangle) : ComplexRectangle :=
  sum fun i => (a i).conjugate.mul (b i)

theorem dot_contains {n : ℕ} {a b : Fin n → ComplexRectangle} {z w : Fin n → ℂ}
    (ha : ∀ i, (a i).Contains (z i)) (hb : ∀ i, (b i).Contains (w i)) :
    (dot a b).Contains (∑ i, star (z i) * w i) :=
  sum_contains fun i => ComplexRectangle.contains_mul
    (ComplexRectangle.contains_conjugate (ha i)) (hb i)

abbrev Rectangular (m n : ℕ) := Matrix (Fin m) (Fin n) ComplexRectangle

def Contains {m n : ℕ} (a : Rectangular m n) (A : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∀ i j, (a i j).Contains (A i j)

def mul {m n p : ℕ} (a : Rectangular m n) (b : Rectangular n p) : Rectangular m p :=
  fun i j => sum fun k => (a i k).mul (b k j)

theorem mul_contains {m n p : ℕ} {a : Rectangular m n} {b : Rectangular n p}
    {A : Matrix (Fin m) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p) ℂ}
    (ha : Contains a A) (hb : Contains b B) : Contains (mul a b) (A * B) := by
  intro i j
  exact sum_contains fun k => ComplexRectangle.contains_mul (ha i k) (hb k j)

def gram {m n : ℕ} (a : Rectangular m n) : Rectangular n n :=
  fun i j => dot (fun k => a k i) (fun k => a k j)

theorem gram_contains {m n : ℕ} {a : Rectangular m n}
    {A : Matrix (Fin m) (Fin n) ℂ} (ha : Contains a A) :
    Contains (gram a) (A.conjTranspose * A) := by
  intro i j
  exact dot_contains (fun k => ha k i) (fun k => ha k j)

def rounded {m n : ℕ} (p : ℕ) (a : Rectangular m n) : Rectangular m n :=
  fun i j => round p (a i j)

theorem rounded_contains {m n : ℕ} (p : ℕ) {a : Rectangular m n}
    {A : Matrix (Fin m) (Fin n) ℂ} (ha : Contains a A) : Contains (rounded p a) A :=
  fun i j => round_contains p (ha i j)

def subsetCheck {m n : ℕ} (a b : Rectangular m n) : Bool :=
  decide (∀ i j, rectangleSubsetCheck (a i j) (b i j) = true)

theorem subsetCheck_sound {m n : ℕ} {a b : Rectangular m n}
    (h : subsetCheck a b = true) {A : Matrix (Fin m) (Fin n) ℂ}
    (ha : Contains a A) : Contains b A := by
  have hh : ∀ i j, rectangleSubsetCheck (a i j) (b i j) = true := of_decide_eq_true h
  exact fun i j => rectangleSubsetCheck_sound (hh i j) (ha i j)

end Maxwell.Certificate.IntervalLinear
