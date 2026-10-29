import Maxwell.Cost.DecoderParser.ArchiveRewind
import Maxwell.Cost.Link

namespace Maxwell.Cost.SourceReplay.Archive
open Structured

def permutation (workTape : ℕ) : Equiv.Perm ℕ := Equiv.swap 18 workTape

def program (workTape : ℕ) : BitRAM :=
  DecoderParser.ArchiveRewind.program.renameTapes (permutation workTape)

private theorem rename_twice (workTape : ℕ) (s : BitRAMState) :
    (s.renameTapes (permutation workTape)).renameTapes (permutation workTape) = s := by
  simp [BitRAMState.renameTapes, permutation, Function.comp_def]

structure Frame (workTape : ℕ) (s t : Store) : Prop where
  address : t.val.address = s.val.address
  memory : t.val.memory = s.val.memory
  randomCursor : t.val.randomCursor = s.val.randomCursor
  output : t.val.output = s.val.output
  tapes : ∀ j, j ≠ workTape → t.val.tapes j = s.val.tapes j

/-- A literal tape permutation reuses the verified archive traversal.
Each input-head move is still an executed primitive. -/
theorem executes (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (word : List Bool) (s : Store)
    (hw : s.val.tapes workTape = BitTape.shiftedEnd word 0) :
    ∃ t : Store, Executes input randomTape (.call (program workTape))
      (6*word.length+6) s t ∧
      t.val.inputHead = s.val.inputHead-word.length ∧
      t.val.tapes workTape = BitTape.ofList word ∧ Frame workTape s t := by
  let p := permutation workTape
  let a := s.val.renameTapes p
  have haw : a.tapes 18 = BitTape.shiftedEnd word 0 := by
    simpa [a, p, permutation, BitRAMState.renameTapes] using hw
  have he := DecoderParser.ArchiveRewind.steps input randomTape word.length a s.property
    (by simp [haw, BitTape.shiftedEnd])
    (by simp [haw, BitTape.shiftedEnd, BitTape.shifted])
    (by intro k hk; exact ⟨word[k], by simp [haw, BitTape.shiftedEnd, BitTape.shifted, hk]⟩)
  let b := (DecoderParser.ArchiveRewind.finish word.length a).renameTapes p
  have hrun : PricedSteps ((program workTape).next input randomTape)
      (6*word.length+5) s.val b := by
    simpa only [program, a, p, rename_twice] using he.renameTapes p
  let t := Store.ofState b
  refine ⟨t, ?_, rfl, ?_, ?_⟩
  · exact Executes.call _ _ _ _ hrun (by
      simp [program, b, p, BitRAM.renameTapes, DecoderParser.ArchiveRewind.finish,
        BitRAMState.renameTapes, DecoderParser.ArchiveRewind.program,
        BitRAMInstruction.renameTapes])
  · simp [t, b, a, p, Store.ofState, BitRAMState.renameTapes,
      DecoderParser.ArchiveRewind.finish, permutation,
      BitTape.shiftedEnd, BitTape.ofList, BitTape.shifted, hw]
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro j hj
    have hpj : p.symm j ≠ 18 := by
      intro h
      have := congrArg p h
      exact hj (by simpa [p, permutation] using this)
    change Function.update a.tapes 18 {a.tapes 18 with head := 0} (p.symm j) = _
    rw [Function.update_of_ne hpj]
    simp [a, p, permutation, BitRAMState.renameTapes]

end Maxwell.Cost.SourceReplay.Archive
