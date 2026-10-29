import Maxwell.Certificate.DyadicKernelRounded
import Maxwell.Certificate.DyadicKernelSchurSound
import Maxwell.Certificate.DyadicScaledDot

namespace Maxwell.Certificate.DyadicKernel

theorem round_checked (q : ℕ) (a : Rectangle) :
    rescaleCheck q a (round q a) = true := by
  rcases a with ⟨ar,ai,ae⟩
  have hs : 0 < (2:ℕ)^q := by positivity
  have hsZ : (0:ℤ) < ((2:ℕ)^q:ℤ) := by exact_mod_cast hs
  have hrem (x : ℤ) :
      (x - x / ((2:ℕ)^q:ℤ) * ((2:ℕ)^q:ℤ)).natAbs < (2:ℕ)^q := by
    have he : x - x / ((2:ℕ)^q:ℤ) * ((2:ℕ)^q:ℤ) = x % ((2:ℕ)^q:ℤ) := by
      rw [Int.emod_def]
      ring
    rw [he]
    have hh : (((x % ((2:ℕ)^q:ℤ)).natAbs):ℤ) < ((2:ℕ)^q:ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonneg (Int.emod_nonneg _ (ne_of_gt hsZ))]
      exact Int.emod_lt_of_pos _ hsZ
    exact_mod_cast hh
  simp only [round, rescaleCheck]
  apply decide_eq_true
  have he := Nat.div_add_mod ae ((2:ℕ)^q)
  have hm := Nat.mod_lt ae hs
  have hr := hrem ar
  have hi := hrem ai
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hr hi ⊢
  constructor <;> nlinarith

theorem round_contains {p q : ℕ} {a : Rectangle} {z : ℂ}
    (h : a.toDyadic.Contains (p+q) z) : (round q a).toDyadic.Contains p z := by
  exact DyadicRectangle.rescaleCheck_sound
    ((rescaleCheck_eq p q a (round q a)).symm.trans (round_checked q a)) h

theorem mulRound_contains {p : ℕ} {a b : Rectangle} {z w : ℂ}
    (ha : a.toDyadic.Contains p z) (hb : b.toDyadic.Contains p w) :
    (mulRound p a b).toDyadic.Contains p (z*w) := by
  apply round_contains
  rw [toDyadic_mulExact]
  exact DyadicRectangle.mulExact_contains ha hb

theorem dotRound_contains {p q : ℕ}
    {data : List (Rectangle × Rectangle)} {values : List (ℂ × ℂ)}
    (h : List.Forall₂ (fun ab zw => ab.1.toDyadic.Contains p zw.1 ∧
      ab.2.toDyadic.Contains q zw.2) data values) :
    (dotRound q data).toDyadic.Contains p (values.map (fun zw => zw.1*zw.2)).sum := by
  apply round_contains
  rw [toDyadic_dot]
  apply DyadicRectangle.dotPairs_contains
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hh ht ih => exact List.Forall₂.cons hh ih

end Maxwell.Certificate.DyadicKernel
