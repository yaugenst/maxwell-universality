import Maxwell.Cost.Structured.Rename
import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.BankArray.Frame

/-! Tape renaming preserves both stored words and the exact set of tapes
changed by a checked program. -/
namespace Maxwell.Cost

theorem BankArray.Word.renameTapes {s : BitRAMState} {i : ℕ} {bits : List Bool}
    (h : BankArray.Word s i bits) (p : Equiv.Perm ℕ) :
    BankArray.Word (s.renameTapes p) (p i) bits := by
  obtain ⟨origin,word⟩:=h
  refine ⟨origin,?_⟩
  simpa only [BitRAMState.renameTapes,Function.comp_apply,Equiv.symm_apply_apply] using word

theorem BinaryPrecision.Frame.renameTapes {changed : Finset ℕ} {s t : BitRAMState}
    (h : BinaryPrecision.Frame changed s t) (p : Equiv.Perm ℕ) :
    BinaryPrecision.Frame (changed.image p) (s.renameTapes p) (t.renameTapes p) := by
  refine ⟨h.address,h.inputHead,h.memory,h.randomCursor,h.output,?_⟩
  intro i hi
  apply h.tapes
  intro hin
  apply hi
  exact Finset.mem_image.mpr ⟨p.symm i,hin,Equiv.apply_symm_apply p i⟩

#print axioms BinaryPrecision.Frame.renameTapes
end Maxwell.Cost
