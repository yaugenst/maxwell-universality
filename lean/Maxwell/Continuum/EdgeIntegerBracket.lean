import Maxwell.Continuum.EdgeBisection
import Maxwell.Continuum.RationalFiniteWidths

/-! Bisection with a shared integer denominator. The actual endpoint words grow
linearly with the iteration count, without relying on rational normalization. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate

structure EdgeWords where
  lower : ℤ
  upper : ℤ
  denominator : ℕ
  deriving DecidableEq, Repr

namespace EdgeWords

def lo (w : EdgeWords) : ℚ := w.lower/w.denominator
def hi (w : EdgeWords) : ℚ := w.upper/w.denominator
def midpoint (w : EdgeWords) : ℚ := (w.lower+w.upper)/(2*w.denominator)
def ofInterval (I : Interval) : EdgeWords :=
  ⟨I.lo.num*I.hi.den,I.hi.num*I.lo.den,I.lo.den*I.hi.den⟩
def step (w : EdgeWords) (negative : Bool) : EdgeWords :=
  if negative then ⟨64*w.lower,31*w.lower+33*w.upper,64*w.denominator⟩
  else ⟨33*w.lower+31*w.upper,64*w.upper,64*w.denominator⟩

def Bound (w : EdgeWords) (B : ℕ) : Prop :=
  w.lower.natAbs≤B ∧ w.upper.natAbs≤B ∧ w.denominator≤B

theorem midpoint_eq (w : EdgeWords) : w.midpoint=(w.lo+w.hi)/2 := by
  unfold midpoint lo hi
  ring

theorem ofInterval_den_pos (I : Interval) : 0<(ofInterval I).denominator :=
  Nat.mul_pos I.lo.den_pos I.hi.den_pos

theorem ofInterval_endpoints (I : Interval) :
    (ofInterval I).lo=I.lo ∧ (ofInterval I).hi=I.hi := by
  have hl : (I.lo.den : ℚ)≠0 := by exact_mod_cast I.lo.den_pos.ne'
  have hu : (I.hi.den : ℚ)≠0 := by exact_mod_cast I.hi.den_pos.ne'
  constructor
  · change ((I.lo.num*I.hi.den : ℤ) : ℚ)/(I.lo.den*I.hi.den : ℕ)=I.lo
    push_cast
    rw [mul_div_mul_right _ _ hu,I.lo.num_div_den]
  · change ((I.hi.num*I.lo.den : ℤ) : ℚ)/(I.lo.den*I.hi.den : ℕ)=I.hi
    push_cast
    rw [mul_comm (I.lo.den : ℚ),mul_div_mul_right _ _ hl,I.hi.num_div_den]

theorem step_den_pos (w : EdgeWords) (negative : Bool) (hw : 0<w.denominator) :
    0<(w.step negative).denominator := by
  cases negative <;> simpa only [step,Bool.false_eq_true,↓reduceIte] using
    Nat.mul_pos (by decide : 0<64) hw

theorem step_endpoints (w : EdgeWords) (I : Interval) (hw : 0<w.denominator)
    (hlo : w.lo=I.lo) (hhi : w.hi=I.hi) (negative : Bool) :
    (w.step negative).lo=(edgeStep I negative).lo ∧
      (w.step negative).hi=(edgeStep I negative).hi := by
  have hd : (w.denominator : ℚ)≠0 := by exact_mod_cast hw.ne'
  cases negative <;>
    simp only [step,edgeStep,Bool.false_eq_true,↓reduceIte,Interval.midpoint,Interval.width,
      ← hlo,← hhi,lo,hi] <;> push_cast <;> constructor <;> field_simp <;> ring

theorem step_bound (w : EdgeWords) (negative : Bool) {B : ℕ} (hw : w.Bound B) :
    (w.step negative).Bound (64*B) := by
  obtain ⟨hwl,hwu,hwd⟩ := hw
  have h31 : (31*w.lower+33*w.upper).natAbs≤64*B := by
    apply (Int.natAbs_add_le _ _).trans
    norm_num only [Int.natAbs_mul,Int.natAbs_natCast]
    omega
  have h33 : (33*w.lower+31*w.upper).natAbs≤64*B := by
    apply (Int.natAbs_add_le _ _).trans
    norm_num only [Int.natAbs_mul,Int.natAbs_natCast]
    omega
  have hl : (64*w.lower).natAbs≤64*B := by
    simpa only [Int.natAbs_mul,show (64 : ℤ).natAbs=64 by rfl] using Nat.mul_le_mul_left 64 hwl
  have hu : (64*w.upper).natAbs≤64*B := by
    simpa only [Int.natAbs_mul,show (64 : ℤ).natAbs=64 by rfl] using Nat.mul_le_mul_left 64 hwu
  have hd := Nat.mul_le_mul_left 64 hwd
  cases negative
  · exact ⟨h33,hu,hd⟩
  · exact ⟨hl,h31,hd⟩

theorem ofInterval_bound (I : Interval) (W : ℕ)
    (hl : RationalWords.Width I.lo W) (hu : RationalWords.Width I.hi W) :
    (ofInterval I).Bound (2^(2*W)) := by
  have bound {n : ℕ} (h : n.bits.length≤W) : n≤2^W := by
    rw [Nat.size_eq_bits_len] at h
    exact (Nat.size_le.mp h).le
  have hnlo := bound hl.num
  have hnhi := bound hu.num
  have hdlo := bound hl.den
  have hdhi := bound hu.den
  have hp : 2^W*2^W=2^(2*W) := by rw [← pow_add]; congr 1; omega
  constructor
  · simpa only [ofInterval,Int.natAbs_mul,Int.natAbs_natCast,hp] using Nat.mul_le_mul hnlo hdhi
  · constructor
    · simpa only [ofInterval,Int.natAbs_mul,Int.natAbs_natCast,hp] using Nat.mul_le_mul hnhi hdlo
    · simpa only [ofInterval,hp] using Nat.mul_le_mul hdlo hdhi

theorem endpoint_width {w : EdgeWords} {B : ℕ} (hw : w.Bound (2^B))
    (hd : 0<w.denominator) :
    RationalWords.Width w.lo (B+1) ∧ RationalWords.Width w.hi (B+1) := by
  have bound {n : ℕ} (h : n≤2^B) : n.bits.length≤B+1 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    have hp : 0<(2 : ℕ)^B := by positivity
    exact h.trans_lt (by rw [pow_succ]; omega)
  exact ⟨RationalWords.width_fraction hd (bound hw.1) (bound hw.2.2),
    RationalWords.width_fraction hd (bound hw.2.1) (bound hw.2.2)⟩

end EdgeWords

def edgeWordBrackets (decideNegative : ℚ → ℕ → Bool) (base : ℕ) (I : Interval) : ℕ → EdgeWords
  | 0 => EdgeWords.ofInterval I
  | k+1 => let w := edgeWordBrackets decideNegative base I k
      w.step (decideNegative w.midpoint (base+k+6))

theorem edgeWordBrackets_den_pos (decideNegative : ℚ → ℕ → Bool) (base : ℕ)
    (I : Interval) (k : ℕ) : 0<(edgeWordBrackets decideNegative base I k).denominator := by
  induction k with
  | zero => exact EdgeWords.ofInterval_den_pos I
  | succ k ih => exact EdgeWords.step_den_pos _ _ ih

theorem edgeWordBrackets_endpoints (decideNegative : ℚ → ℕ → Bool) (base : ℕ)
    (I : Interval) (k : ℕ) :
    (edgeWordBrackets decideNegative base I k).lo=(edgeBrackets decideNegative base I k).lo ∧
      (edgeWordBrackets decideNegative base I k).hi=(edgeBrackets decideNegative base I k).hi := by
  induction k with
  | zero => exact EdgeWords.ofInterval_endpoints I
  | succ k ih =>
    have hm : (edgeWordBrackets decideNegative base I k).midpoint=
        (edgeBrackets decideNegative base I k).midpoint := by
      rw [EdgeWords.midpoint_eq,ih.1,ih.2]
      rfl
    simp only [edgeWordBrackets,edgeBrackets]
    rw [hm]
    exact EdgeWords.step_endpoints _ _ (edgeWordBrackets_den_pos _ _ _ _) ih.1 ih.2 _

theorem edgeWordBrackets_bound (decideNegative : ℚ → ℕ → Bool) (base : ℕ)
    (I : Interval) (W k : ℕ) (hl : RationalWords.Width I.lo W)
    (hu : RationalWords.Width I.hi W) :
    (edgeWordBrackets decideNegative base I k).Bound (2^(2*W+6*k)) := by
  induction k with
  | zero => simpa only [edgeWordBrackets,mul_zero,add_zero] using EdgeWords.ofInterval_bound I W hl hu
  | succ k ih =>
    have h := EdgeWords.step_bound (edgeWordBrackets decideNegative base I k)
      (decideNegative (edgeWordBrackets decideNegative base I k).midpoint (base+k+6)) ih
    have he : 2*W+6*(k+1)=6+(2*W+6*k) := by omega
    simpa only [edgeWordBrackets,he,pow_add,show (2 : ℕ)^6=64 by norm_num] using h

theorem edgeBrackets_endpoint_width (decideNegative : ℚ → ℕ → Bool) (base : ℕ)
    (I : Interval) (W k : ℕ) (hl : RationalWords.Width I.lo W)
    (hu : RationalWords.Width I.hi W) :
    RationalWords.Width (edgeBrackets decideNegative base I k).lo (2*W+6*k+1) ∧
      RationalWords.Width (edgeBrackets decideNegative base I k).hi (2*W+6*k+1) := by
  have h := EdgeWords.endpoint_width (edgeWordBrackets_bound decideNegative base I W k hl hu)
    (edgeWordBrackets_den_pos decideNegative base I k)
  rwa [edgeWordBrackets_endpoints decideNegative base I k |>.1,
    edgeWordBrackets_endpoints decideNegative base I k |>.2] at h

#print axioms edgeWordBrackets_endpoints
#print axioms edgeWordBrackets_bound
#print axioms edgeBrackets_endpoint_width

end Maxwell.Continuum.Calibration
