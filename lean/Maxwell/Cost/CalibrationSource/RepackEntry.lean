import Maxwell.Cost.CalibrationSource.RepackStep
import Maxwell.Cost.CalibrationMatrix.EraseWords

namespace Maxwell.Cost.CalibrationSource.Repack
open Structured CalibrationMatrix
open RationalAccumulator (Blank)
set_option maxHeartbeats 1200000

def entryCode (i : ℕ) : Code := .seq (BinaryPrecision.literalCode 104 i)
  (.seq stepCode (EraseWords.code [104]))

theorem entry {m : ℕ} (c : Data) (d : ModeRead.Data m) (i : Fin m) (B : ℕ)
    (hc : c.Sized B) (hd : d.Sized B) (hsep : c.Separated d)
    (hfit : ∀ a, (d.value i a).bits.length ≤ addressValue c.width)
    (hi : i.val.bits.length ≤ B) (out : Fin 2 → Vector (List Bool) m)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Stored c out s.val) (hm : ModeRead.Stored readLayout d s.val) (hw : Workspace s.val) :
    ∃ cost t, cost ≤ 122000*(B+2)^2 ∧ Executes input tape (entryCode i.val) cost s t ∧
      Stored c (fun a => (out a).set i ((words c d a).get i)) t.val ∧
      ModeRead.Stored readLayout d t.val ∧ Workspace t.val ∧ Frame s.val t.val ∧
      OutputOutside c.output m (addressValue c.width) s.val t.val := by
  obtain ⟨a,ea,ai,fa⟩ := BinaryPrecision.literal 104 i.val input tape s hw.2.2.2
  have fra := Frame.of_literal fa
  have ar : Ready a.val (dotValues 0 0) := hw.1.of_tapes (by
    intro j hj; exact fa.tapes j (by simp; omega))
  have a4 := RationalAccumulator.blank_of_eq (fa.tapes 4 (by decide)) hw.2.1
  have a37 := RationalAccumulator.blank_of_eq (fa.tapes 37 (by decide)) hw.2.2.1
  obtain ⟨sc,b,hsc,eb,br,b4,b37,bs,bm,fb,bo,bi⟩ := step c d i B hc hd hsep hfit out input tape
    i.val.bits (addressValue_bits _) hi a ar a4 a37 (hs.of_frame fra fa.memory)
    (modeStored_of_frame hm fra fa.memory) ai
  obtain ⟨cc,t,hcc,ec,ct,fc⟩ := EraseWords.executes [104] B (fun _ => i.val.bits)
    (by intro j hj; exact hi) input tape b (by intro j hj; simpa only [List.mem_singleton.mp hj] using bi)
  have frc : Frame b.val t.val := Frame.of_literal (by simpa using fc)
  refine ⟨10*i.val.bits.length+7+(sc+cc),t,?_,ea.seq (eb.seq ec),bs.of_frame frc fc.memory,
    modeStored_of_frame bm frc fc.memory,?_,(fra.trans fb).trans frc,?_⟩
  · simp only [List.length_singleton] at hcc
    nlinarith
  · refine ⟨br.of_tapes (by intro j hj; exact fc.tapes j (by simp;omega)),
      RationalAccumulator.blank_of_eq (fc.tapes 4 (by decide)) b4,
      RationalAccumulator.blank_of_eq (fc.tapes 37 (by decide)) b37,ct 104 (by simp)⟩
  · exact ((OutputOutside.of_memory fa.memory).trans bo).trans (OutputOutside.of_memory fc.memory)

end Maxwell.Cost.CalibrationSource.Repack
