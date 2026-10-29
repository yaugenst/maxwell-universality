import Maxwell.Cost.CalibrationMatrix.BooleanKey
import Maxwell.Cost.BankArray.Common

/-! The stencil case is selected by reading the actual column direction. -/
namespace Maxwell.Cost.CalibrationMatrix.DirectionSelect
open Structured BankArray
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private def readState (source value present : ℕ) (s : Store) : Store :=
  Store.ofState {s.val with
    registers := Function.update
      (Function.update s.val.registers value ((s.val.tapes source).read.getD false))
      present ((s.val.tapes source).read.isSome)}

private theorem read_executes (source value present : ℕ)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.atom (.readTape source value present)) 3 s
      (readState source value present s) := by
  apply Executes.atom (extra := 1) (t := {s.val.setRegister value
    ((s.val.tapes source).read.getD false) with
    registers := Function.update
      (Function.update s.val.registers value ((s.val.tapes source).read.getD false))
        present ((s.val.tapes source).read.isSome)})
  · simp [BitRAM.next,s.property]
  · simp [BitRAMState.setRegister,s.property]

def readCode : Code := .seq (.atom (.readTape 170 222 223))
  (.seq (.atom (.tapeRight 170))
    (.seq (.atom (.readTape 170 224 225)) (.atom (.tapeLeft 170))))

private theorem direction_bits (word : List Bool) (d : Direction)
    (h : addressValue word = d.val) :
    word.head?.getD false = decide (d = 1) ∧
      word.tail.head?.getD false = decide (d = 2) := by
  cases word with
  | nil => fin_cases d <;> simp_all [addressValue]
  | cons b rest =>
    cases rest with
    | nil => cases b <;> fin_cases d <;> simp_all [addressValue]
    | cons c rest =>
      cases b <;> cases c <;> fin_cases d <;> simp_all [addressValue] <;> omega

theorem read_direction (input : List Bool) (tape : ℕ → Bool) (word : List Bool)
    (d : Direction) (hd : addressValue word = d.val) (s : Store)
    (hw : Word s.val 170 word) :
    ∃ t, Executes input tape readCode 10 s t ∧
      t.val.registers 222 = decide (d = 1) ∧ t.val.registers 224 = decide (d = 2) ∧
      BinaryPrecision.Frame ∅ s.val t.val ∧
      (∀ i, i ≠ 222 → i ≠ 223 → i ≠ 224 → i ≠ 225 → t.val.registers i = s.val.registers i) := by
  obtain ⟨origin,hw⟩ := hw
  let a := readState 170 222 223 s
  let b := Store.ofState (a.val.setTape 170 {a.val.tapes 170 with head := (a.val.tapes 170).head+1})
  let c := readState 170 224 225 b
  let t := Store.ofState (c.val.setTape 170 {c.val.tapes 170 with head := (c.val.tapes 170).head-1})
  have ea := read_executes 170 222 223 input tape s
  have eb : Executes input tape (.atom (.tapeRight 170)) 2 a b := Executes.tapeRight _ _ _ _
  have ec := read_executes 170 224 225 input tape b
  have et : Executes input tape (.atom (.tapeLeft 170)) 2 c t := Executes.tapeLeft _ _ _ _
  have htapes : t.val.tapes = s.val.tapes := by
    funext i
    by_cases hi : i = 170
    · subst i
      simp [t,c,b,a,readState,Store.ofState,BitRAMState.setTape]
    · simp [t,c,b,a,readState,Store.ofState,BitRAMState.setTape]
  have hlow : t.val.registers 222 = word.head?.getD false := by
    simp [t,c,b,a,readState,Store.ofState,BitRAMState.setTape,hw,BitTape.read,
      BitTape.shifted,List.head?_eq_getElem?]
  have hhigh : t.val.registers 224 = word.tail.head?.getD false := by
    simp [t,c,b,a,readState,Store.ofState,BitRAMState.setTape,hw,BitTape.read,
      BitTape.shifted,List.head?_eq_getElem?,List.getElem?_tail]
  refine ⟨t,ea.seq (eb.seq (ec.seq et)),hlow.trans (direction_bits word d hd).1,
    hhigh.trans (direction_bits word d hd).2,⟨rfl,rfl,rfl,rfl,rfl,fun i _ => congrFun htapes i⟩,?_⟩
  intro i hi hj hk hl
  simp [t,c,b,a,readState,Store.ofState,BitRAMState.setTape,hi,hj,hk,hl]

def emitCode (keyTape : ℕ) : Code :=
  .branch 224 (BooleanKey.emitManyCode keyTape 220 (BooleanKey.stencilTests 2))
    (.branch 222 (BooleanKey.emitManyCode keyTape 220 (BooleanKey.stencilTests 1))
      (BooleanKey.emitManyCode keyTape 220 (BooleanKey.stencilTests 0)))

def code (keyTape : ℕ) : Code := .seq readCode (emitCode keyTape)

/-- One fixed program handles all three directions. Its branch conditions
are derived from the stored word and cannot be supplied as an oracle. -/
theorem executes (keyTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (word : List Bool) (R : ℕ) (rd cd : Direction) (row column : Direction → ℕ)
    (origin : ℤ) (s : Store) (hw : Word s.val 170 word)
    (hvalue : addressValue word = cd.val)
    (hd : ∀ j, s.val.registers (200+j.val) = directionTests rd j)
    (hc : ∀ j delta, s.val.registers (203+3*j.val+delta.val) = coordinateTests row column j delta)
    (hkey : s.val.tapes keyTape = BitTape.shiftedEnd
      (BooleanKey.materialHeader (entryKey (unsignedEdge R rd row) (unsignedEdge R cd column))) origin) :
    ∃ cost t, cost ≤ 268 ∧ Executes input tape (code keyTape) cost s t ∧
      t.val.tapes keyTape = BitTape.shiftedEnd
        (TableKey.encode (entryKey (unsignedEdge R rd row) (unsignedEdge R cd column))) origin ∧
      BinaryPrecision.Frame {keyTape} s.val t.val := by
  obtain ⟨a,ea,hal,hah,hf,hg⟩ := read_direction input tape word cd hvalue s hw
  have hda (j : Direction) : a.val.registers (200+j.val) = directionTests rd j := by
    rw [hg _ (by have := j.isLt; omega) (by have := j.isLt; omega)
      (by have := j.isLt; omega) (by have := j.isLt; omega)]
    exact hd j
  have hca (j delta : Direction) : a.val.registers (203+3*j.val+delta.val) =
      coordinateTests row column j delta := by
    have hj := j.isLt
    have hk := delta.isLt
    rw [hg _ (by omega) (by omega) (by omega) (by omega)]
    exact hc j delta
  have hka := (hf.tapes keyTape (by simp)).trans hkey
  obtain ⟨t,et,ht,ft,_⟩ := BooleanKey.emit_stencil keyTape input tape R rd cd row column origin a hda hca hka
  have selected : ∃ cost, cost ≤ 258 ∧ Executes input tape (emitCode keyTape) cost a t := by
    fin_cases cd
    · exact ⟨258,by decide,.no (by simpa using hah) (.no (by simpa using hal) et)⟩
    · exact ⟨258,by decide,.no (by simpa using hah) (.yes (by simpa using hal) et)⟩
    · exact ⟨257,by decide,.yes (by simpa using hah) et⟩
  obtain ⟨cost,hcost,he⟩ := selected
  exact ⟨10+cost,t,by omega,ea.seq he,ht,(hf.mono (by simp)).trans ft⟩

end Maxwell.Cost.CalibrationMatrix.DirectionSelect
