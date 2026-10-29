import Maxwell.Cost.DoublingInit.Common
import Maxwell.Cost.SourceCircuit.TraceBinding

namespace Maxwell.Cost.DoublingInit
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

def packCode : Code := BankArray.packCanonicalCode 81 83

theorem pack_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (i : Fin n) (index clock : List Bool)
    (hw : 0<layout.route.width) (hi : addressValue index=i.val)
    (hlen : index.length≤layout.route.width) (hc : clock.length=layout.route.width)
    (s : Store) (cfg : Config layout index clock s.val) (ss : BankArray.Scratch s.val)
    (h7 : Blank s.val 7) (h37 : Blank s.val 37) :
    ∃ cost t, cost≤80*layout.route.width+90 ∧ Executes input tape packCode cost s t ∧
      Word t.val 37 (IncidenceEncoding.word layout.route.width i.val) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ t.val.memory=s.val.memory ∧
      Config layout index clock t.val ∧ BankArray.FrameExcept 37 s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht,hs,t7,control,tf⟩ := BankArray.pack_canonical 81 83 (by omega) (by omega)
    input tape index clock (by omega) (by omega) s ss h7 h37 cfg.route.index cfg.route.clock
  have hword : FixedWidth.bits clock.length index = IncidenceEncoding.word layout.route.width i.val := by
    apply SourceCircuit.fixedWidth_eq
    · simp [hc]
    · rw [FixedWidth.bits_value _ _ (by omega),hi]
  exact ⟨cost,t,by omega,he,by simpa only [hword] using ht,hs,t7,control.2.2.2.1,
    cfg.of_frame (Frame.of_except (Or.inl rfl) tf),tf⟩

end Maxwell.Cost.DoublingInit
