import Maxwell.Cost.PhysicalDecoder.ModeEntry
import Maxwell.Cost.EmitLiteral

/-! The local support is fixed platform data. This finite program enumerates
its indices, loads every coefficient from the runtime shared-mode arrays, and
emits one decoder row in the exact codec order. -/
namespace Maxwell.Cost.PhysicalDecoder.LocalEntries
open Structured RationalAccumulator

def work : Finset ℕ := ModeEntry.work ∪ {359}
def Ready (s : BitRAMState) : Prop := ModeEntry.Ready s ∧ Blank s 359

structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  tapes : ∀ j ∉ work, t.tapes j = s.tapes j

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.memory.trans h.memory, k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor, fun j hj => (k.tapes j hj).trans (h.tapes j hj)⟩

theorem Frame.stored {n : ℕ} {d : ModeRead.Data n} {s t : BitRAMState}
    (hf : Frame s t) (h : ModeRead.Stored ModeEntry.layout d s) :
    ModeRead.Stored ModeEntry.layout d t := by
  refine ⟨BankArray.word_of_eq (hf.tapes 514 (by decide)) h.width,
    BankArray.word_of_eq (hf.tapes 515 (by decide)) h.clock, ?_,
    word_of_eq (hf.tapes 512 (by decide)) h.denominator, ?_⟩
  · intro a
    exact BankArray.word_of_eq (hf.tapes (ModeEntry.layout.base a)
      (by fin_cases a <;> decide)) (h.bases a)
  · intro a
    simpa only [hf.memory] using h.arrays a

theorem Frame.fields {n : ℕ} {xs : Fin n → Arithmetic.Data} {s t : BitRAMState}
    (hf : Frame s t) (h : ∀ i j, 2 ≤ j.val → Word s (350+j.val) (xs i j)) :
    ∀ i j, 2 ≤ j.val → Word t (350+j.val) (xs i j) := by
  intro i j hj
  apply word_of_eq (hf.tapes _ _) (h i j hj)
  have := j.isLt
  simp only [work, ModeEntry.work, Entry.work, Samples.work, Coefficient.work,
    Arithmetic.work, PhysicalMaterial.ArithmeticBank.work, Finset.mem_union, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton, not_or, not_lt]
  omega

def oneCode (j : ℕ) : Code := .seq (BinaryPrecision.literalCode 359 j)
  (.seq (ModeEntry.code j) (.call (TapeOps.clear 359)))
def oneCost (j B : ℕ) : ℕ := ModeEntry.costBound j B + 16*B+11

theorem one {n : ℕ} (d : ModeRead.Data n) (i : Fin n) (rowBase B : ℕ)
    (hd : d.Sized B) (hrow : rowBase.bits.length ≤ B) (hib : i.val.bits.length ≤ B)
    (x : Arithmetic.Data) (hx0 : x 0 = (((d.value i 0 : ℕ):ℤ)-d.value i 1).natAbs)
    (hx1 : x 1 = d.denominator) (hv : Arithmetic.Valid x) (hB : Arithmetic.Bounded x B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready s.val)
    (hst : ModeRead.Stored ModeEntry.layout d s.val) (hbase : Word s.val 345 rowBase)
    (hfields : ∀ j : Fin 8, 2 ≤ j.val → Word s.val (350+j.val) (x j)) :
    ∃ cost t, cost ≤ oneCost i.val B ∧ Executes input tape (oneCode i.val) cost s t ∧
      t.val.output = (Codec.nat (rowBase+i.val) ++
        Codec.rat (Arithmetic.fraction x (decide (d.value i 0 < d.value i 1)))).reverse ++
          s.val.output ∧ Ready t.val ∧ ModeRead.Stored ModeEntry.layout d t.val ∧ Frame s.val t.val := by
  obtain ⟨a, ea, wa, fa⟩ := BinaryPrecision.literal 359 i.val input tape s hs.2
  have af : Frame s.val a.val := ⟨fa.memory, fa.inputHead, fa.randomCursor, fun j hj =>
    fa.tapes j (fun h => hj (Finset.mem_union_right _ h))⟩
  have ar : ModeEntry.Ready a.val := by
    intro j hj
    apply blank_of_eq (fa.tapes j _) (hs.1 j hj)
    have hn : j≠359 := by intro he; subst j; exact (by decide : 359∉ModeEntry.work) hj
    simpa only [Finset.mem_singleton] using hn
  have aw : BankArray.Word a.val 359 i.val.bits := wa
  obtain ⟨c, b, hc, eb, bo, br, bd, _, fb⟩ := ModeEntry.executes d i rowBase B hd hrow x hx0 hx1
    hv hB input tape i.val.bits (address_bits i.val) hib a ar (af.stored hst) aw
    (word_of_eq (fa.tapes 345 (by decide)) hbase) (by
      intro j hj
      apply word_of_eq (fa.tapes _ _) (hfields j hj)
      have := j.isLt
      simp only [Finset.mem_singleton]
      omega)
  have bw : Word b.val 359 i.val := word_of_eq (fb.tapes 359 (by decide)) wa
  obtain ⟨t, et, tz, ft⟩ := RationalCanonical.clear_word 359 i.val input tape b bw
  have bf : Frame a.val b.val := ⟨fb.memory, fb.inputHead, fb.randomCursor,
    fun j hj => fb.tapes j (fun h => hj (Finset.mem_union_left _ h))⟩
  have tf : Frame b.val t.val := by
    refine ⟨ft.2.2.1, ft.2.1, ft.2.2.2.1, ?_⟩
    intro j hj
    have hn : j≠359 := by intro he; subst j; exact hj (by simp [work])
    exact ft.2.2.2.2.2.1 j hn hn
  have tr : Ready t.val := by
    refine ⟨?_, (zero_word_iff_blank _ _).mp tz⟩
    intro j hj
    have hn : j≠359 := by intro he; subst j; exact (by decide : 359∉ModeEntry.work) hj
    exact blank_of_eq (ft.2.2.2.2.2.1 j hn hn) (br j hj)
  refine ⟨(10*i.val.bits.length+7)+(c+(6*i.val.bits.length+4)), t,
    by unfold oneCost; omega, ea.seq (eb.seq et), ?_, tr, tf.stored bd, af.trans (bf.trans tf)⟩
  rw [ft.2.2.2.2.1, bo, fa.output]

def code {n : ℕ} : List (Fin n) → Code
  | [] => .skip
  | i::rest => .seq (oneCode i.val) (code rest)
def costBound {n : ℕ} (is : List (Fin n)) (B : ℕ) : ℕ :=
  (is.map fun i => oneCost i.val B).sum + 1
def record {n : ℕ} (d : ModeRead.Data n) (rowBase : ℕ) (x : Fin n → Arithmetic.Data)
    (i : Fin n) : List Bool :=
  Codec.nat (rowBase+i.val) ++ Codec.rat (Arithmetic.fraction (x i)
    (decide (d.value i 0 < d.value i 1)))

theorem executes {n : ℕ} (d : ModeRead.Data n) (is : List (Fin n)) (rowBase B : ℕ)
    (hd : d.Sized B) (hrow : rowBase.bits.length ≤ B) (hib : ∀ i : Fin n, i.val.bits.length ≤ B)
    (x : Fin n → Arithmetic.Data)
    (hx0 : ∀ i, x i 0 = (((d.value i 0 : ℕ):ℤ)-d.value i 1).natAbs)
    (hx1 : ∀ i, x i 1 = d.denominator) (hv : ∀ i, Arithmetic.Valid (x i))
    (hB : ∀ i, Arithmetic.Bounded (x i) B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready s.val)
    (hst : ModeRead.Stored ModeEntry.layout d s.val) (hbase : Word s.val 345 rowBase)
    (hfields : ∀ i j, 2 ≤ j.val → Word s.val (350+j.val) (x i j)) :
    ∃ cost t, cost ≤ costBound is B ∧ Executes input tape (code is) cost s t ∧
      t.val.output = (is.flatMap (record d rowBase x)).reverse ++ s.val.output ∧
      Ready t.val ∧ ModeRead.Stored ModeEntry.layout d t.val ∧ Frame s.val t.val := by
  induction is generalizing s with
  | nil =>
    exact ⟨1, s, by simp [costBound], .skip s, by simp, hs, hst,
      ⟨rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  | cons i rest ih =>
    obtain ⟨c, a, hc, ea, ao, ar, ad, af⟩ := one d i rowBase B hd hrow (hib i)
      (x i) (hx0 i) (hx1 i) (hv i) (hB i) input tape s hs hst hbase (hfields i)
    obtain ⟨e, t, he, et, tout, tr, td, tf⟩ := ih a ar ad
      (word_of_eq (af.tapes 345 (by decide)) hbase) (af.fields hfields)
    refine ⟨c+e, t, ?_, ea.seq et, ?_, tr, td, af.trans tf⟩
    · simp only [costBound, List.map_cons, List.sum_cons] at he ⊢
      omega
    · rw [tout, ao]
      simp only [List.flatMap_cons, List.reverse_append, List.append_assoc, record]

def rowCode (n : ℕ) : Code := .seq (EmitLiteral.code 29 (Codec.rat 0 ++ Codec.nat n))
  (code (List.finRange n))

theorem row_executes {n : ℕ} (d : ModeRead.Data n) (rowBase B : ℕ)
    (hd : d.Sized B) (hrow : rowBase.bits.length ≤ B) (hib : ∀ i : Fin n, i.val.bits.length ≤ B)
    (x : Fin n → Arithmetic.Data)
    (hx0 : ∀ i, x i 0 = (((d.value i 0 : ℕ):ℤ)-d.value i 1).natAbs)
    (hx1 : ∀ i, x i 1 = d.denominator) (hv : ∀ i, Arithmetic.Valid (x i))
    (hB : ∀ i, Arithmetic.Bounded (x i) B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready s.val)
    (hst : ModeRead.Stored ModeEntry.layout d s.val) (hbase : Word s.val 345 rowBase)
    (hfields : ∀ i j, 2 ≤ j.val → Word s.val (350+j.val) (x i j)) :
    ∃ cost t, cost ≤ 4*(Codec.rat 0 ++ Codec.nat n).length+1+costBound (List.finRange n) B ∧
      Executes input tape (rowCode n) cost s t ∧
      t.val.output = (Codec.rat 0 ++ Codec.nat n ++
        ((List.finRange n).flatMap (record d rowBase x))).reverse ++ s.val.output ∧
      Ready t.val ∧ ModeRead.Stored ModeEntry.layout d t.val ∧ Frame s.val t.val := by
  let header := Codec.rat 0 ++ Codec.nat n
  let a := EmitLiteral.finish 29 header s
  have ea := EmitLiteral.executes 29 header input tape s
  have fa := EmitLiteral.finish_frame 29 header s
  have af : Frame s.val a.val := ⟨fa.2.2.1, fa.2.1, fa.2.2.2.1,
    fun j _ => congrFun fa.2.2.2.2.1 j⟩
  have ar : Ready a.val := ⟨fun j hj => blank_of_eq (congrFun fa.2.2.2.2.1 j) (hs.1 j hj),
    blank_of_eq (congrFun fa.2.2.2.2.1 359) hs.2⟩
  obtain ⟨c, t, hc, et, tout, tr, td, tf⟩ := executes d (List.finRange n) rowBase B hd hrow hib
    x hx0 hx1 hv hB input tape a ar (af.stored hst)
    (word_of_eq (congrFun fa.2.2.2.2.1 345) hbase) (af.fields hfields)
  refine ⟨4*header.length+1+c, t, by dsimp [header]; omega, ea.seq et, ?_, tr, td, af.trans tf⟩
  rw [tout, EmitLiteral.finish_output]
  simp only [header, List.reverse_append, List.append_assoc]

end Maxwell.Cost.PhysicalDecoder.LocalEntries
