import Maxwell.Cost.RationalAccumulator.Prepare
import Maxwell.Cost.RationalAccumulator.Add

namespace Maxwell.Cost.RationalAccumulator

open Structured

def pushCode : Code :=
  .seq prepareCode (.seq (.call (WordTransfer.move 36 1))
    (.seq (.branch 35 (addCode 31) (addCode 30)) (.call (TapeOps.clear 1))))

def selected (sign : Bool) : ℕ := if sign then 31 else 30

def pushed (v : ℕ → ℕ) (sign : Bool) : ℕ → ℕ :=
  let base := Function.update (prepared v) 36 0
  Function.update base (selected sign) (v 32 * v 33 + base (selected sign))

theorem selected_bounds (sign : Bool) : 30 ≤ selected sign ∧ selected sign ≤ 31 := by
  cases sign <;> simp [selected]

theorem push (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (B : ℕ) (sign : Bool)
    (hbits : ∀ i, 30 ≤ i → i ≤ 36 → (v i).bits.length ≤ B)
    (hd : 0 < v 32) (htermD : 0 < v 34) (hzero : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0)
    (hsign : s.val.registers 35 = sign) :
    ∃ cost, ∃ t : Store, cost ≤ 12000 * (B + 2)^2 ∧
      Executes input tape pushCode cost s t ∧
      Bank t.val (pushed v sign) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨pcost, p, hpcost, hp, hpb, hpr, hpf⟩ :=
    prepare input tape v B hbits hd htermD hzero s hbank hready
  obtain ⟨q, hq, hqb, hqr, hqf⟩ := move_to_one 36 (by decide) (by decide)
    input tape (prepared v) p hpb hpr
  let v1 := Function.update (prepared v) 36 0
  have hv36 : prepared v 36 = v 32 * v 33 := by simp [prepared]
  rw [hv36] at hqr
  have hselected := selected_bounds sign
  obtain ⟨acost, a, hacost, ha, hab, har, haf⟩ := add_bank (selected sign) hselected.1
    (by omega) input tape v1 (v 32 * v 33) q hqb hqr
  have hsignq : q.val.registers 35 = sign :=
    ((hqf.2.2.2.2.2.2 35 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (hpf.2.2.2.2.2.2 35 (by decide) (by decide) (by decide) (by decide) (by decide))).trans hsign
  have hbranch : Executes input tape (.branch 35 (addCode 31) (addCode 30)) (1 + acost) q a := by
    cases sign
    · exact Executes.no hsignq ha
    · exact Executes.yes hsignq ha
  obtain ⟨t, ht, htb, htr, htf⟩ := clear_one input tape (pushed v sign) (v 32 * v 33) a hab har
  refine ⟨pcost + ((12 * (prepared v 36).bits.length + 11) +
      ((1 + acost) + (6 * (v 32 * v 33).bits.length + 4))), t, ?_,
    Executes.seq hp (Executes.seq hq (Executes.seq hbranch ht)), htb, htr,
    ((hpf.trans hqf).trans haf).trans htf⟩
  have h32 := hbits 32 (by decide) (by decide)
  have h33 := hbits 33 (by decide) (by decide)
  have h34 := hbits 34 (by decide) (by decide)
  have hm : (v 32 * v 33).bits.length ≤ 2 * B := (bits_mul_le _ _).trans (by omega)
  have hx : (v1 (selected sign)).bits.length ≤ 2 * B := by
    cases sign
    · have h30 := hbits 30 (by decide) (by decide)
      simpa [v1, prepared, selected] using
        (bits_mul_le (v 34) (v 30)).trans (show (v 34).bits.length + (v 30).bits.length ≤ 2*B by omega)
    · have h31 := hbits 31 (by decide) (by decide)
      simpa [v1, prepared, selected] using
        (bits_mul_le (v 34) (v 31)).trans (show (v 34).bits.length + (v 31).bits.length ≤ 2*B by omega)
  rw [hv36]
  nlinarith

def bankValue (v : ℕ → ℕ) : ℚ := ((v 30 : ℚ) - v 31) / v 32

def termValue (v : ℕ → ℕ) (sign : Bool) : ℚ :=
  (if sign then -(v 33 : ℚ) else v 33) / v 34

theorem pushed_value (v : ℕ → ℕ) (sign : Bool) (hd : 0 < v 32) (ht : 0 < v 34) :
    bankValue (pushed v sign) = bankValue v + termValue v sign := by
  have hdq : (v 32 : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have htq : (v 34 : ℚ) ≠ 0 := by exact_mod_cast ht.ne'
  cases sign <;> simp [bankValue, termValue, pushed, prepared, selected]
  all_goals field_simp
  all_goals ring

theorem pushed_denominator_pos (v : ℕ → ℕ) (sign : Bool) (hd : 0 < v 32) (ht : 0 < v 34) :
    0 < pushed v sign 32 := by
  cases sign <;> simpa [pushed, prepared, selected] using Nat.mul_pos ht hd

theorem pushed_bits (v : ℕ → ℕ) (sign : Bool) (B : ℕ)
    (hbits : ∀ i, 30 ≤ i → i ≤ 36 → (v i).bits.length ≤ B) :
    ∀ i, 30 ≤ i → i ≤ 36 → (pushed v sign i).bits.length ≤ 2 * B + 1 := by
  have h30 := hbits 30 (by decide) (by decide)
  have h31 := hbits 31 (by decide) (by decide)
  have h32 := hbits 32 (by decide) (by decide)
  have h33 := hbits 33 (by decide) (by decide)
  have h34 := hbits 34 (by decide) (by decide)
  have h35 := hbits 35 (by decide) (by decide)
  have hprod (a b : ℕ) (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B) :
      (a*b).bits.length ≤ 2*B := (bits_mul_le a b).trans (by omega)
  have hsum (a b c d : ℕ) (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B)
      (hc : c.bits.length ≤ B) (hd : d.bits.length ≤ B) :
      (a*b+c*d).bits.length ≤ 2*B+1 :=
    (bits_add_le _ _).trans (by have := hprod a b ha hb; have := hprod c d hc hd; omega)
  intro i hi hi'
  interval_cases i <;> cases sign <;> simp [pushed, prepared, selected]
  all_goals first
    | exact hsum _ _ _ _ h32 h33 h34 h30
    | exact hsum _ _ _ _ h32 h33 h34 h31
    | exact (hprod _ _ h34 h30).trans (by omega)
    | exact (hprod _ _ h34 h31).trans (by omega)
    | exact (hprod _ _ h34 h32).trans (by omega)
    | omega

theorem push_compiled_run (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (B : ℕ) (sign : Bool) (hbits : ∀ i, 30 ≤ i → i ≤ 36 → (v i).bits.length ≤ B)
    (hd : 0 < v 32) (htermD : 0 < v 34) (hzero : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0)
    (hsign : s.val.registers 35 = sign) :
    ∃ t : Store,
      (runPriced (pushCode.compile.next input tape) (12000 * (B+2)^2+1) s.val).finished =
        some (t.place pushCode.size) ∧
      (runPriced (pushCode.compile.next input tape) (12000 * (B+2)^2+1) s.val).instructions ≤
        12000 * (B+2)^2 ∧
      Bank t.val (pushed v sign) ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨cost, t, hc, he, hb, hr, hf⟩ := push input tape v B sign hbits hd htermD hzero s hbank hready hsign
  have hrun := he.compiled_run (12000*(B+2)^2+1) (by omega)
  exact ⟨t, hrun.1, hrun.2 ▸ hc, hb, hr, hf⟩

end Maxwell.Cost.RationalAccumulator
