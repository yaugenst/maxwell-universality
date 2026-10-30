import Maxwell.Continuum.ChebyshevWaveSelectedFrame
import Maxwell.Continuum.ChebyshevWaveProducerReset
import Maxwell.Continuum.RationalDataflowPartsCopy

/-! The represented workspace used between the three tensor factors. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

structure FactorReady {n D : ℕ} (a : Table n) (Q N : ℕ) (b : Table (2*D))
    (v : ℕ→Parts) (s : Store) : Prop where
  ready : Ready tensorBank v s
  phase : Phase.Runtime.Clean s.val
  floor : DyadicFloor.Clean s.val
  setup : NatAssign.Bank setupIds (initialSetup Q N) s.val
  source : a.Ready s
  output : b.OutputReady s
  power : Blank s.val 144
  powerCount : Blank s.val 146
  inner : Blank s.val 680
  saved : ∀i∈savedPorts,Blank s.val i

theorem output_tensor_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.OutputReady s)
    (f : BinaryPrecision.Frame (RationalDataflow.workspace tensorBank) s.val t.val)
    (hz : NatAssign.Scratch t.val) : a.OutputReady t := by
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,37,210,212,213,214,215}:Finset ℕ)) :=
    f.tapes i (by
      have hd : Disjoint ({5,6,7,8,9,37,210,212,213,214,215}:Finset ℕ)
          (RationalDataflow.workspace tensorBank) := by decide
      exact fun hm => Finset.disjoint_left.mp hd hi hm)
  have scratch : BankArray.Scratch t.val :=
    ⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
      blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,
      blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
      blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  apply h.transfer f.memory _ scratch (blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  apply keep
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem tensor_setup_ready_frame {v : ℕ→Parts} {s t : Store} (h : Ready tensorBank v s)
    (f : BinaryPrecision.Frame setupWorkspace s.val t.val) (hz : NatAssign.Scratch t.val) :
    Ready tensorBank v t := by
  refine ⟨?_,hz⟩
  intro i hi
  have hd : Disjoint (RationalDataflow.ids tensorBank) setupWorkspace := by decide
  exact word_of_eq (f.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)) (h.1 i hi)

def factorSaveValues (target : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (Function.update v target (v 8)) (target+1) (v 9)
def factorValues (target : ℕ) (v : ℕ→Parts) : ℕ→Parts := cacheResetValues (factorSaveValues target v)
def factorSaveCode (target : ℕ) : Code := .seq (partsCopyCode 8 target) (partsCopyCode 9 (target+1))
def factorFinishCode (target : ℕ) : Code := .seq (factorSaveCode target)
  (.seq (program cacheResetInstructions) resetCode)
def factorFinishCost (Q N W B : ℕ) : ℕ := 2*RationalDataflow.stageCost B+
  (12*operationCost (B+1)+1)+RationalDataflow.stageCost (resetWidth Q N W)

theorem factorValues_saved (target : ℕ) (ht : 17 ≤ target) (v : ℕ→Parts) :
    factorValues target v target=v 8 ∧ factorValues target v (target+1)=v 9 := by
  simp [factorValues,cacheResetValues_eq,factorSaveValues,show ¬target<10 by omega,
    show target≠12 by omega,show target≠13 by omega,show ¬target+1<10 by omega,
    show target+1≠12 by omega,show target+1≠13 by omega]

theorem factorValues_high (target : ℕ) (v : ℕ→Parts) (i : ℕ) (hi : 17 ≤ i)
    (hit : i≠target) (hit' : i≠target+1) : factorValues target v i=v i := by
  simp [factorValues,cacheResetValues_eq,factorSaveValues,show ¬i<10 by omega,
    show i≠12 by omega,show i≠13 by omega,hit,hit']

theorem factorValues_width (target W : ℕ) (ht : 17 ≤ target) (hW : 1 ≤ W)
    (v base : ℕ→Parts) (hm : SameMetadata v base) (hb : WidthBank ids W base)
    (h8 : (v 8).Width W) (h9 : (v 9).Width W)
    (hh : ∀i∈Finset.Ico 17 32,(v i).Width W) : WidthBank tensorBank W (factorValues target v) := by
  intro i hi
  rw [factorValues,cacheResetValues_eq]
  split_ifs with hclear
  · exact (show (Parts.literal 0).Width 1 by unfold Parts.Width Parts.literal;decide).mono hW
  · by_cases hit : i=target
    · subst i;simpa [factorSaveValues] using h8
    · by_cases hit' : i=target+1
      · subst i;simpa [factorSaveValues] using h9
      · simp only [factorSaveValues,Function.update_of_ne hit,Function.update_of_ne hit']
        rcases Finset.mem_union.mp hi with hsmall|hlarge
        · have hil : i<16 := Finset.mem_range.mp hsmall
          rw [hm i (by simp only [cacheMetadata,Finset.mem_insert,Finset.mem_singleton];omega)]
          exact hb i hsmall
        · exact hh i hlarge

#print axioms factorValues_width
end Maxwell.Continuum.Profile.WaveMachine.Runtime
