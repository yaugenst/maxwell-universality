import Maxwell.Cost.BinaryPrecision
import Maxwell.Green.CalibrationTests
import Maxwell.Cost.CalibrationMatrix.TableKey

/-! Actual Boolean conjunctions and key-bit writes for the fixed stencil. -/
namespace Maxwell.Cost.CalibrationMatrix.BooleanKey
open Structured
set_option maxHeartbeats 800000

structure RegisterFrame (acc : ℕ) (s t : Store) : Prop where
  address : t.val.address = s.val.address
  inputHead : t.val.inputHead = s.val.inputHead
  memory : t.val.memory = s.val.memory
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : t.val.tapes = s.val.tapes
  registers : ∀ i, i ≠ acc → t.val.registers i = s.val.registers i

theorem RegisterFrame.refl (acc : ℕ) (s : Store) : RegisterFrame acc s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem RegisterFrame.trans {acc : ℕ} {s t u : Store}
    (h : RegisterFrame acc s t) (k : RegisterFrame acc t u) : RegisterFrame acc s u :=
  ⟨k.address.trans h.address, k.inputHead.trans h.inputHead, k.memory.trans h.memory,
   k.randomCursor.trans h.randomCursor, k.output.trans h.output, k.tapes.trans h.tapes,
   fun i hi => (k.registers i hi).trans (h.registers i hi)⟩

private def set (acc : ℕ) (b : Bool) (s : Store) : Store :=
  Store.ofState (s.val.setRegister acc b)

private theorem set_frame (acc : ℕ) (b : Bool) (s : Store) : RegisterFrame acc s (set acc b s) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  simp [set, Store.ofState, BitRAMState.setRegister, hi]

def foldCode (acc : ℕ) : List ℕ → Code
  | [] => .skip
  | r :: rs => .seq (Code.atom (.bitAnd acc acc r)) (foldCode acc rs)

def foldState (acc : ℕ) : List ℕ → Store → Store
  | [], s => s
  | r :: rs, s => foldState acc rs (set acc (s.val.registers acc && s.val.registers r) s)

theorem fold_executes (acc : ℕ) (rs : List ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (foldCode acc rs) (2 * rs.length + 1) s (foldState acc rs s) := by
  induction rs generalizing s with
  | nil => exact .skip s
  | cons r rs ih =>
    have e := Executes.bitAnd input tape s acc acc r
    convert e.seq (ih (set acc (s.val.registers acc && s.val.registers r) s)) using 1 <;>
      first | rfl | simp only [List.length_cons]; omega

theorem fold_frame (acc : ℕ) (rs : List ℕ) (s : Store) : RegisterFrame acc s (foldState acc rs s) := by
  induction rs generalizing s with
  | nil => exact RegisterFrame.refl _ _
  | cons r rs ih => exact (set_frame acc _ s).trans (ih _)

theorem fold_value (acc : ℕ) (rs : List ℕ) (hacc : ∀ r ∈ rs, r ≠ acc) (s : Store) :
    (foldState acc rs s).val.registers acc = (s.val.registers acc && rs.all s.val.registers) := by
  induction rs generalizing s with
  | nil => simp [foldState]
  | cons r rs ih =>
    have htail : ∀ r ∈ rs, r ≠ acc := fun r hr => hacc r (by simp [hr])
    rw [foldState, ih htail]
    have hall : rs.all (set acc (s.val.registers acc && s.val.registers r) s).val.registers =
        rs.all s.val.registers := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      apply forall_congr'
      intro j
      apply forall_congr'
      intro hj
      rw [(set_frame acc _ s).registers j (htail j hj)]
    rw [hall]
    simp [set, Store.ofState, BitRAMState.setRegister, Bool.and_assoc]

def emitCode (key acc : ℕ) (rs : List ℕ) : Code :=
  .seq (Code.atom (.literal acc true))
    (.seq (foldCode acc rs)
      (.seq (Code.atom (.writeTape key acc)) (Code.atom (.tapeRight key))))

/-- A compile-time list of register names becomes real Boolean gates and
one appended key bit. Only the key tape and accumulator register change. -/
theorem emit (key acc : ℕ) (rs : List ℕ) (hacc : ∀ r ∈ rs, r ≠ acc)
    (input : List Bool) (tape : ℕ → Bool) (preceding : List Bool) (origin : ℤ) (s : Store)
    (hkey : s.val.tapes key = BitTape.shiftedEnd preceding origin) :
    ∃ t, Executes input tape (emitCode key acc rs) (2 * rs.length + 7) s t ∧
      t.val.tapes key = BitTape.shiftedEnd (preceding ++ [rs.all s.val.registers]) origin ∧
      BinaryPrecision.Frame {key} s.val t.val ∧
      (∀ i, i ≠ acc → t.val.registers i = s.val.registers i) := by
  let a := set acc true s
  let b := foldState acc rs a
  let w := Store.ofState (b.val.setTape key ((b.val.tapes key).write (some (b.val.registers acc))))
  let t := Store.ofState (w.val.setTape key {w.val.tapes key with head := (w.val.tapes key).head + 1})
  have ea : Executes input tape (Code.atom (.literal acc true)) 2 s a := Executes.literal _ _ _ _ _
  have eb := fold_executes acc rs input tape a
  have ew : Executes input tape (Code.atom (.writeTape key acc)) 2 b w := Executes.writeTape _ _ _ _ _
  have et : Executes input tape (Code.atom (.tapeRight key)) 2 w t := Executes.tapeRight _ _ _ _
  have fb : RegisterFrame acc s b := (set_frame acc true s).trans (fold_frame acc rs a)
  have hb : b.val.registers acc = rs.all s.val.registers := by
    rw [fold_value acc rs hacc]
    have hall : rs.all a.val.registers = rs.all s.val.registers := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      apply forall_congr'
      intro j
      apply forall_congr'
      intro hj
      rw [(set_frame acc true s).registers j (hacc j hj)]
    simpa [a, set, Store.ofState, BitRAMState.setRegister] using hall
  have hbk : b.val.tapes key = BitTape.shiftedEnd preceding origin := by rw [fb.tapes]; exact hkey
  refine ⟨t, ?_, ?_, ?_, fb.registers⟩
  · convert ea.seq (eb.seq (ew.seq et)) using 1 <;> first | rfl | omega
  · simpa [t, w, Store.ofState, BitRAMState.setTape, hbk, hb, BitTape.write,
      BitTape.shiftedEnd, BitTape.shifted] using
      BitTape.shiftedEnd_append_write preceding origin (rs.all s.val.registers)
  · refine ⟨fb.address, fb.inputHead, fb.memory, fb.randomCursor, fb.output, ?_⟩
    intro i hi
    have hi' : i ≠ key := by simpa using hi
    simpa [t, w, Store.ofState, BitRAMState.setTape, hi'] using congrFun fb.tapes i

private theorem all_congr_mem (rs : List ℕ) (a b : ℕ → Bool)
    (h : ∀ r ∈ rs, a r = b r) : rs.all a = rs.all b := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  apply forall_congr'
  intro r
  apply forall_congr'
  intro hr
  rw [h r hr]

def emitManyCode (key acc : ℕ) : List (List ℕ) → Code
  | [] => .skip
  | rs :: rest => .seq (emitCode key acc rs) (emitManyCode key acc rest)

/-- A fixed finite circuit emits every local test bit while retaining all
input test registers for the later conjunctions. -/
theorem emit_many (key acc : ℕ) (tests : List (List ℕ))
    (hacc : ∀ rs ∈ tests, ∀ r ∈ rs, r ≠ acc)
    (input : List Bool) (tape : ℕ → Bool) (preceding : List Bool) (origin : ℤ) (s : Store)
    (hkey : s.val.tapes key = BitTape.shiftedEnd preceding origin) :
    ∃ t, Executes input tape (emitManyCode key acc tests)
        ((tests.map fun rs => 2 * rs.length + 7).sum + 1) s t ∧
      t.val.tapes key = BitTape.shiftedEnd
        (preceding ++ tests.map (fun rs => rs.all s.val.registers)) origin ∧
      BinaryPrecision.Frame {key} s.val t.val ∧
      (∀ i, i ≠ acc → t.val.registers i = s.val.registers i) := by
  induction tests generalizing preceding s with
  | nil => exact ⟨s, .skip s, by simpa using hkey, BinaryPrecision.Frame.refl _ _, fun _ _ => rfl⟩
  | cons rs tests ih =>
    have hhead := hacc rs (by simp)
    have htail : ∀ rs ∈ tests, ∀ r ∈ rs, r ≠ acc := fun rs hrs => hacc rs (by simp [hrs])
    obtain ⟨a, ea, ha, fa, ga⟩ := emit key acc rs hhead input tape preceding origin s hkey
    obtain ⟨t, et, ht, ft, gt⟩ := ih htail (preceding ++ [rs.all s.val.registers]) a ha
    have hbits : tests.map (fun rs => rs.all a.val.registers) =
        tests.map (fun rs => rs.all s.val.registers) := by
      apply List.map_congr_left
      intro rs hrs
      exact all_congr_mem rs _ _ (fun r hr => ga r (htail rs hrs r hr))
    refine ⟨t, ?_, ?_, fa.trans ft, fun i hi => (gt i hi).trans (ga i hi)⟩
    · exact ea.seq et
    · simpa only [List.map_cons, hbits, List.append_assoc, List.singleton_append] using ht

open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice

/-- Registers 200--202 store direction equalities; 203--211 store the
three offsets for each of the three coordinate equalities. -/
def hitRegisters (d : Direction) (k : Fin 16) : List ℕ :=
  [200 + (freeTemplate d k).1.1.val,
   203 + (offsetIndex d k 0).val,
   206 + (offsetIndex d k 1).val,
   209 + (offsetIndex d k 2).val]

def diagonalRegisters (d : Direction) : List ℕ := [200 + d.val, 204, 207, 210]

def stencilTests (d : Direction) : List (List ℕ) :=
  List.ofFn (hitRegisters d) ++ [diagonalRegisters d]

theorem stencilTests_safe (d : Direction) :
    ∀ rs ∈ stencilTests d, ∀ r ∈ rs, r ≠ 220 := by
  intro rs hrs r hr
  simp only [stencilTests, List.mem_append, List.mem_ofFn, List.mem_singleton] at hrs
  rcases hrs with ⟨k, rfl⟩ | rfl
  · simp only [hitRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h0 := (freeTemplate d k).1.1.isLt
    have h1 := (offsetIndex d k 0).isLt
    have h2 := (offsetIndex d k 1).isLt
    have h3 := (offsetIndex d k 2).isLt
    omega
  · simp only [diagonalRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h0 := d.isLt
    omega

theorem stencilTests_cost (d : Direction) :
    ((stencilTests d).map fun rs => 2 * rs.length + 7).sum + 1 = 256 := by
  simp only [stencilTests, List.map_append, List.map_ofFn,
    diagonalRegisters, List.length_cons, List.length_nil, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, List.sum_ofFn]
  norm_num [hitRegisters]

theorem hitRegisters_value (d : Direction) (k : Fin 16) (s : Store)
    (direction : Direction → Bool) (coordinates : Direction → Fin 3 → Bool)
    (hd : ∀ j, s.val.registers (200 + j.val) = direction j)
    (hc : ∀ j delta, s.val.registers (203 + 3 * j.val + delta.val) = coordinates j delta) :
    (hitRegisters d k).all s.val.registers = fixedHit d k direction coordinates := by
  simp only [hitRegisters, List.all_cons, List.all_nil, Bool.and_true]
  rw [hd]
  have h0 := hc 0 (offsetIndex d k 0)
  have h1 := hc 1 (offsetIndex d k 1)
  have h2 := hc 2 (offsetIndex d k 2)
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  simp only [fixedHit, h0, h1, h2]

theorem diagonalRegisters_value (d : Direction) (s : Store)
    (direction : Direction → Bool) (coordinates : Direction → Fin 3 → Bool)
    (hd : ∀ j, s.val.registers (200 + j.val) = direction j)
    (hc : ∀ j delta, s.val.registers (203 + 3 * j.val + delta.val) = coordinates j delta) :
    (diagonalRegisters d).all s.val.registers = fixedDiagonal d direction coordinates := by
  simp only [diagonalRegisters, List.all_cons, List.all_nil, Bool.and_true]
  rw [hd]
  have h0 := hc 0 1
  have h1 := hc 1 1
  have h2 := hc 2 1
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  simpa only [fixedDiagonal] using congrArg₂ (fun x y => direction d && (x && y))
    h0 (congrArg₂ (fun x y => x && y) h1 h2)

def materialHeader (key : StencilKey) : List Bool :=
  TableKey.field 2 key.edge.1.val ++ (TableKey.field 5 (key.edge.2 0).val ++
    (TableKey.field 5 (key.edge.2 1).val ++ TableKey.field 5 (key.edge.2 2).val))

theorem materialHeader_length (key : StencilKey) : (materialHeader key).length = 17 := by
  simp [materialHeader]

/-- The saved comparison bits are combined and appended by actual gates,
writes and moves. Together with the material header they form exactly the
34-bit key consumed by the fixed stencil table. -/
theorem emit_stencil (keyTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (R : ℕ) (rd cd : Direction) (row column : Direction → ℕ) (origin : ℤ) (s : Store)
    (hd : ∀ j, s.val.registers (200 + j.val) = directionTests rd j)
    (hc : ∀ j delta, s.val.registers (203 + 3 * j.val + delta.val) = coordinateTests row column j delta)
    (hkey : s.val.tapes keyTape = BitTape.shiftedEnd
      (materialHeader (entryKey (unsignedEdge R rd row) (unsignedEdge R cd column))) origin) :
    ∃ t, Executes input tape (emitManyCode keyTape 220 (stencilTests cd)) 256 s t ∧
      t.val.tapes keyTape = BitTape.shiftedEnd
        (TableKey.encode (entryKey (unsignedEdge R rd row) (unsignedEdge R cd column))) origin ∧
      BinaryPrecision.Frame {keyTape} s.val t.val ∧
      (∀ i, i ≠ 220 → t.val.registers i = s.val.registers i) := by
  let key := entryKey (unsignedEdge R rd row) (unsignedEdge R cd column)
  obtain ⟨t, he, ht, hf, hg⟩ := emit_many keyTape 220 (stencilTests cd) (stencilTests_safe cd)
    input tape (materialHeader key) origin s hkey
  have hbits : (stencilTests cd).map (fun rs => rs.all s.val.registers) =
      List.ofFn key.hit ++ [key.diagonal] := by
    simp only [stencilTests, List.map_append, List.map_cons, List.map_nil, List.map_ofFn]
    congr 1
    · apply congrArg List.ofFn
      funext k
      exact (hitRegisters_value cd k s _ _ hd hc).trans (fixedHit_binding R rd cd row column k)
    · congr 1
      exact (diagonalRegisters_value cd s _ _ hd hc).trans (fixedDiagonal_binding R rd cd row column)
  refine ⟨t, ?_, ?_, hf, hg⟩
  · simpa only [stencilTests_cost] using he
  · rw [hbits] at ht
    simpa only [materialHeader, TableKey.encode, List.append_assoc] using ht

end Maxwell.Cost.CalibrationMatrix.BooleanKey
