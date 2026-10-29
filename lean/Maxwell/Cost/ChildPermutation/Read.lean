import Maxwell.Cost.ChildPermutation.ReadOne
import Maxwell.Cost.ChildPermutation.Upper

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing.Coloring.NumericSplit

def readCode : Code := .seq (BankArray.readBankCode 86 81 128 87 88)
  (.seq (BankArray.readBankCode 80 81 100 83 89)
  (.seq upperCode (.seq (BankArray.readBankCode 80 37 100 83 91) (.call (TapeOps.clear 37)))))

/-- Fetch both parent occurrences and their shared split bit from saved arrays. -/
theorem read_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : Data k) (out : Outputs k) (index clock childClock : List Bool)
    (i : Fin (2^k)) (hw : layout.parentWidth=k+2) (hi : addressValue index=i.val)
    (hlen : index.length≤layout.parentWidth) (hc : clock.length=layout.parentWidth)
    (s : Store) (cfg : Config layout index clock childClock s.val) (work : Workspace s.val)
    (rep : Represents layout s.val.memory data out) :
    ∃ cost t, cost≤120000*(budget layout index+1)^2 ∧ Executes input tape readCode cost s t ∧
      Word t.val 88 [data.colors.get (lower i)] ∧
      Word t.val 89 (IncidenceEncoding.word layout.parentWidth (data.target (lower i)).val) ∧
      Word t.val 91 (IncidenceEncoding.word layout.parentWidth (data.target (upper i)).val) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧ Blank t.val 90 ∧ Blank t.val 92 ∧
      t.val.memory=s.val.memory ∧ Config layout index clock childClock t.val ∧ Frame s.val t.val := by
  have priv (j : ℕ) (h : j=88 ∨ j=89 ∨ j=90 ∨ j=91 ∨ j=92) : Private j := by
    simp only [Private,DoublingInit.Private,DoublingPass.Private]
    omega
  obtain ⟨ac,a,hac,ea,a88,ass,a7,am,acfg,af⟩ := read_color input tape layout data index clock childClock i hi s cfg
    work.1.1 work.1.2.1 (work.1.2.2 88 (by simp [DoublingPass.Private])) rep.colors
  obtain ⟨bc,b,hbc,eb,b89,bss,b7,bm,bcfg,bf⟩ := read_parent input tape layout data index clock childClock index
    81 89 (lower i) (by omega) (priv 89 (by omega)) (by omega) hi hc (by dsimp [budget]; omega)
    a acfg ass a7 (RationalAccumulator.blank_of_eq (af.2.2.2.1 89 (by omega) (by omega))
      (work.1.2.2 89 (by simp [DoublingPass.Private]))) acfg.index (by simpa only [am] using rep.parent)
  obtain ⟨uc,u,huc,eu,u37,uss,u7,um,ucfg,uf⟩ := upper_executes k input tape layout index clock childClock i hw hi hlen hc
    b bcfg bss b7 (RationalAccumulator.blank_of_eq ((bf.2.2.2.1 37 (by omega) (by omega)).trans
      (af.2.2.2.1 37 (by omega) (by omega))) work.2)
  have hindex : addressValue (IncidenceEncoding.word layout.parentWidth (upper i).val)=(upper i).val := by
    apply IncidenceEncoding.word_value
    have hn : 2*(2^k)≤2^layout.parentWidth := by rw [hw,pow_succ,pow_succ]; omega
    exact lt_of_lt_of_le (upper i).isLt hn
  obtain ⟨vc,v,hvc,ev,v91,vss,v7,vm,vcfg,vf⟩ := read_parent input tape layout data index clock childClock
    (IncidenceEncoding.word layout.parentWidth (upper i).val) 37 91 (upper i) (by omega)
    (priv 91 (by omega)) (by omega) hindex hc
    (by simp only [IncidenceEncoding.word_length]; dsimp [budget]; omega) u ucfg uss u7
    (RationalAccumulator.blank_of_eq ((uf.2.2.2.1 91 (by omega) (by omega)).trans
      ((bf.2.2.2.1 91 (by omega) (by omega)).trans (af.2.2.2.1 91 (by omega) (by omega))))
      (work.1.2.2 91 (by simp [DoublingPass.Private]))) u37
    (by simpa only [um,bm,am] using rep.parent)
  obtain ⟨uo,huo⟩ := u37
  obtain ⟨t,et,tt,tf⟩ := WordCall.clear 37 input tape (IncidenceEncoding.word layout.parentWidth (upper i).val)
    uo v ((vf.2.2.2.1 37 (by omega) (by omega)).trans huo)
  have keepT (j : ℕ) (hj : j≠37) := tf.2.2.2.2.2.1 j hj hj
  have keepAll (j : ℕ) (hj : j=90 ∨ j=92) : t.val.tapes j=s.val.tapes j :=
    (keepT j (by omega)).trans ((vf.2.2.2.1 j (by omega) (by omega)).trans
      ((uf.2.2.2.1 j (by omega) (by omega)).trans
        ((bf.2.2.2.1 j (by omega) (by omega)).trans (af.2.2.2.1 j (by omega) (by omega)))))
  have tframe : Frame v.val t.val := Frame.of_transfer (Or.inl rfl) (Or.inl rfl) (WordTransfer.frame_of_copy tf)
  refine ⟨ac+(bc+(uc+(vc+(6*(IncidenceEncoding.word layout.parentWidth (upper i).val).length+4)))),t,?_,
    ea.seq (eb.seq (eu.seq (ev.seq et))),
    BankArray.word_of_eq ((keepT 88 (by omega)).trans ((vf.2.2.2.1 88 (by omega) (by omega)).trans
      ((uf.2.2.2.1 88 (by omega) (by omega)).trans (bf.2.2.2.1 88 (by omega) (by omega))))) a88,
    BankArray.word_of_eq ((keepT 89 (by omega)).trans ((vf.2.2.2.1 89 (by omega) (by omega)).trans
      (uf.2.2.2.1 89 (by omega) (by omega)))) b89,
    BankArray.word_of_eq (keepT 91 (by omega)) v91,
    scratch_of_tapes (fun j hj => keepT j (by omega)) vss,
    RationalAccumulator.blank_of_eq (keepT 7 (by omega)) v7,
    ⟨uo+(IncidenceEncoding.word layout.parentWidth (upper i).val).length,by simp [tt]⟩,
    RationalAccumulator.blank_of_eq (keepAll 90 (by omega)) (work.1.2.2 90 (by simp [DoublingPass.Private])),
    RationalAccumulator.blank_of_eq (keepAll 92 (by omega)) (work.1.2.2 92 (by simp [DoublingPass.Private])),
    tf.2.2.1.trans (vm.trans (um.trans (bm.trans am))),vcfg.of_frame tframe,?_⟩
  · have hp : layout.parentWidth≤budget layout index := by dsimp [budget]; omega
    simp only [IncidenceEncoding.word_length]
    nlinarith
  · exact (Frame.of_except (priv 88 (by omega)) af).trans ((Frame.of_except (priv 89 (by omega)) bf).trans
      ((Frame.of_except (Or.inl rfl) uf).trans ((Frame.of_except (priv 91 (by omega)) vf).trans tframe)))

end Maxwell.Cost.ChildPermutation
