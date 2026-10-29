import Maxwell.Cost.BankArray.Compare
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.CalibrationMatrix

open Structured BankArray

/-- Equality of two stored unsigned words. The second comparison is only
needed when the first one did not already establish strict inequality. -/
def equalWordCode (left right : ℕ) : Code :=
  .seq (compareCode left right)
    (.branch 2 (Code.atom (.literal 2 false))
      (.seq (compareCode right left) (Code.atom (.bitNot 2 2))))

private def resultStore (s : Store) (b : Bool) : Store :=
  Store.ofState (s.val.setRegister 2 b)

private theorem resultStore_frame (s : Store) (b : Bool) :
    BankArray.Frame s.val (resultStore s b).val := by
  refine ⟨rfl, rfl, rfl, fun _ _ => rfl, ?_⟩
  intro i hi _ _ _ _ _ _
  simp [resultStore, Store.ofState, BitRAMState.setRegister, show i ≠ 2 by omega]

/-- An actual finite machine decides equality, restores its scratch words,
and preserves both inputs, every tape numbered at least three, and memory.
Its charged execution has a uniform linear bound in the common word width. -/
theorem equal_word_bank (left right : ℕ) (hl : 10 ≤ left) (hr : 10 ≤ right)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool) (hlen : xs.length = ys.length)
    (s : Store) (hxs : Word s.val left xs) (hys : Word s.val right ys) (hs : Scratch s.val) :
    ∃ cost t, cost ≤ 160*xs.length+151 ∧
      Executes input tape (equalWordCode left right) cost s t ∧
      (t.val.registers 2 = true ↔ addressValue xs = addressValue ys) ∧
      Word t.val left xs ∧ Word t.val right ys ∧ Scratch t.val ∧
      t.val.memory = s.val.memory ∧
      (∀ i, 3 ≤ i → t.val.tapes i = s.val.tapes i) ∧ BankArray.Frame s.val t.val := by
  obtain ⟨a, ea, ha2, has, ham, hak, haf⟩ :=
    compare_bank left right hl hr input tape xs ys hlen s hxs hys hs
  by_cases hlt : addressValue xs < addressValue ys
  · let t := resultStore a false
    have et := Executes.literal input tape a 2 false
    have ebranch := Executes.yes
      (no := .seq (compareCode right left) (Code.atom (.bitNot 2 2))) (ha2.mpr hlt) et
    have keep (i : ℕ) (hi : 3 ≤ i) : t.val.tapes i = s.val.tapes i := hak i hi
    refine ⟨80*xs.length+77, t, by omega, ?_, ?_,
      word_of_eq (keep left (by omega)) hxs, word_of_eq (keep right (by omega)) hys,
      has, ham, keep, haf.trans (resultStore_frame a false)⟩
    · exact ea.seq ebranch
    · change false = true ↔ addressValue xs = addressValue ys
      simp [ne_of_lt hlt]
  · have hafalse : a.val.registers 2 = false := by
      cases hb : a.val.registers 2 with
      | false => rfl
      | true => exact False.elim (hlt (ha2.mp hb))
    obtain ⟨b, eb, hb2, hbs, hbm, hbk, hbf⟩ :=
      compare_bank right left hr hl input tape ys xs hlen.symm a
        (word_of_eq (hak right (by omega)) hys)
        (word_of_eq (hak left (by omega)) hxs) has
    let t := resultStore b (!b.val.registers 2)
    have et := Executes.bitNot input tape b 2 2
    have ebranch := Executes.no (yes := Code.atom (.literal 2 false)) hafalse (eb.seq et)
    have keep (i : ℕ) (hi : 3 ≤ i) : t.val.tapes i = s.val.tapes i :=
      (hbk i hi).trans (hak i hi)
    refine ⟨160*xs.length+151, t, le_rfl, ?_, ?_,
      word_of_eq (keep left (by omega)) hxs, word_of_eq (keep right (by omega)) hys,
      hbs, hbm.trans ham, keep, haf.trans (hbf.trans (resultStore_frame b _))⟩
    · convert ea.seq ebranch using 1 <;> first | rfl | omega
    · change (!b.val.registers 2) = true ↔ addressValue xs = addressValue ys
      cases hbit : b.val.registers 2 with
      | false =>
        have hn : ¬ addressValue ys < addressValue xs := by
          intro hh
          have htrue := hb2.mpr hh
          rw [hbit] at htrue
          contradiction
        have heq : addressValue xs = addressValue ys := by omega
        simp [heq]
      | true =>
        have hreverse := hb2.mp hbit
        have hne : addressValue xs ≠ addressValue ys := by omega
        simp [hne]

/-- A fixed finite conjunction of word comparisons, stopping at the first
unequal component. The recursion constructs finite code before execution. -/
def equalWordChainCode : (n : ℕ) → (Fin n → ℕ) → (Fin n → ℕ) → Code
  | 0, _, _ => Code.atom (.literal 2 true)
  | n+1, left, right => .seq (equalWordCode (left 0) (right 0))
      (.branch 2 (equalWordChainCode n (fun i => left i.succ) (fun i => right i.succ)) .skip)

theorem equal_word_chain (n width : ℕ) (left right : Fin n → ℕ)
    (hl : ∀ i, 10 ≤ left i) (hr : ∀ i, 10 ≤ right i)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : Fin n → List Bool)
    (hxl : ∀ i, (xs i).length ≤ width) (hyl : ∀ i, (xs i).length = (ys i).length)
    (s : Store) (hxs : ∀ i, Word s.val (left i) (xs i))
    (hys : ∀ i, Word s.val (right i) (ys i)) (hs : Scratch s.val) :
    ∃ cost t, cost ≤ n*(160*width+152)+2 ∧
      Executes input tape (equalWordChainCode n left right) cost s t ∧
      (t.val.registers 2 = true ↔ ∀ i, addressValue (xs i) = addressValue (ys i)) ∧
      (∀ i, Word t.val (left i) (xs i) ∧ Word t.val (right i) (ys i)) ∧
      Scratch t.val ∧ t.val.memory = s.val.memory ∧
      (∀ i, 3 ≤ i → t.val.tapes i = s.val.tapes i) ∧ BankArray.Frame s.val t.val := by
  induction n generalizing s with
  | zero =>
    refine ⟨2, resultStore s true, by simp, Executes.literal input tape s 2 true, ?_,
      (fun i => Fin.elim0 i), hs, rfl, (fun _ _ => rfl), resultStore_frame s true⟩
    change true = true ↔ ∀ i : Fin 0, _
    simp
  | succ n ih =>
    obtain ⟨cost, a, hc, ea, ha2, _, _, has, ham, hak, haf⟩ :=
      equal_word_bank (left 0) (right 0) (hl 0) (hr 0) input tape (xs 0) (ys 0)
        (hyl 0) s (hxs 0) (hys 0) hs
    have hcwidth : cost ≤ 160*width+151 := by have hb := hxl 0; omega
    cases hbit : a.val.registers 2 with
    | false =>
      refine ⟨cost+2, a, ?_, ea.seq (Executes.no hbit (Executes.skip a)), ?_, ?_, has, ham, hak, haf⟩
      · rw [Nat.succ_mul]
        omega
      · rw [hbit]
        simp only [Bool.false_eq_true, false_iff]
        intro hall
        have hb := ha2.mpr (hall 0)
        rw [hbit] at hb
        contradiction
      · intro i
        exact ⟨word_of_eq (hak (left i) (by have hh := hl i; omega)) (hxs i),
          word_of_eq (hak (right i) (by have hh := hr i; omega)) (hys i)⟩
    | true =>
      obtain ⟨tailCost, t, htc, et, ht2, _, hts, htm, htk, htf⟩ :=
        ih (fun i => left i.succ) (fun i => right i.succ)
          (fun i => hl i.succ) (fun i => hr i.succ)
          (fun i => xs i.succ) (fun i => ys i.succ)
          (fun i => hxl i.succ) (fun i => hyl i.succ) a
          (fun i => word_of_eq (hak (left i.succ) (by have hh := hl i.succ; omega)) (hxs i.succ))
          (fun i => word_of_eq (hak (right i.succ) (by have hh := hr i.succ; omega)) (hys i.succ)) has
      have keep (i : ℕ) (hi : 3 ≤ i) : t.val.tapes i = s.val.tapes i :=
        (htk i hi).trans (hak i hi)
      refine ⟨cost+(1+tailCost), t, ?_, ea.seq (Executes.yes hbit et), ?_, ?_,
        hts, htm.trans ham, keep, haf.trans htf⟩
      · rw [Nat.succ_mul]
        omega
      · constructor
        · intro ht i
          refine Fin.cases (ha2.mp hbit) (fun j => (ht2.mp ht) j) i
        · intro hall
          exact ht2.mpr (fun i => hall i.succ)
      · intro i
        exact ⟨word_of_eq (keep (left i) (by have hh := hl i; omega)) (hxs i),
          word_of_eq (keep (right i) (by have hh := hr i; omega)) (hys i)⟩

def equalFourWordCode (left right : Fin 4 → ℕ) : Code := equalWordChainCode 4 left right

/-- Direction and three coordinate words can be compared together with
six operations beyond four worst-case word-comparison charges. -/
theorem equal_four_words (width : ℕ) (left right : Fin 4 → ℕ)
    (hl : ∀ i, 10 ≤ left i) (hr : ∀ i, 10 ≤ right i)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : Fin 4 → List Bool)
    (hxl : ∀ i, (xs i).length ≤ width) (hyl : ∀ i, (xs i).length = (ys i).length)
    (s : Store) (hxs : ∀ i, Word s.val (left i) (xs i))
    (hys : ∀ i, Word s.val (right i) (ys i)) (hs : Scratch s.val) :
    ∃ cost t, cost ≤ 4*(160*width+151)+6 ∧
      Executes input tape (equalFourWordCode left right) cost s t ∧
      (t.val.registers 2 = true ↔ ∀ i, addressValue (xs i) = addressValue (ys i)) ∧
      (∀ i, Word t.val (left i) (xs i) ∧ Word t.val (right i) (ys i)) ∧
      Scratch t.val ∧ t.val.memory = s.val.memory ∧
      (∀ i, 3 ≤ i → t.val.tapes i = s.val.tapes i) ∧ BankArray.Frame s.val t.val := by
  obtain ⟨cost, t, hc, ht⟩ := equal_word_chain 4 width left right hl hr input tape xs ys hxl hyl s hxs hys hs
  exact ⟨cost, t, by omega, ht⟩

end Maxwell.Cost.CalibrationMatrix
