import Maxwell.Continuum.ChebyshevWaveCacheSetupExecution
import Maxwell.Continuum.ChebyshevWaveCacheFrame

/-! The setup changes its explicit runtime metadata and preserves the
stored input/output arrays and the frequency bank. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem setup_ready_frame {v : ℕ→Parts} {s t : Store} (h : Ready ids v s)
    (f : BinaryPrecision.Frame setupWorkspace s.val t.val) (hz : NatAssign.Scratch t.val) :
    Ready ids v t := by
  refine ⟨?_,hz⟩
  intro i hi
  have hd : Disjoint (RationalDataflow.ids ids) setupWorkspace := by decide
  exact word_of_eq (f.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)) (h.1 i hi)

theorem setup_phase_frame {s t : Store} (h : Phase.Runtime.Clean s.val)
    (f : BinaryPrecision.Frame setupWorkspace s.val t.val) : Phase.Runtime.Clean t.val := by
  intro i hi
  have hd : Disjoint ((PhaseMachine.Runtime.ids.erase 652).erase 653) setupWorkspace := by decide
  exact blank_of_eq (f.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)) (h i hi)

theorem setup_floor_frame {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BinaryPrecision.Frame setupWorkspace s.val t.val) : DyadicFloor.Clean t.val := by
  refine ⟨blank_of_eq (f.tapes 4 (by decide)) h.1,?_⟩
  intro i hi
  have hd : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) setupWorkspace := by decide
  exact blank_of_eq (f.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)) (h.2 i hi)

def setupTablePreserved : Finset ℕ := {5,6,7,8,9,37,200,202,203,204,205,210,212,213,214,215}
theorem setup_table_preserved (i : ℕ) (hi : i∈setupTablePreserved) : i∉setupWorkspace := by
  have hd : Disjoint setupTablePreserved setupWorkspace := by decide
  exact fun hm => Finset.disjoint_left.mp hd hi hm

theorem setup_table_scratch {s t : Store} (h : BankArray.Scratch s.val)
    (f : BinaryPrecision.Frame setupWorkspace s.val t.val) (hz : NatAssign.Scratch t.val) :
    BankArray.Scratch t.val := by
  have keep (i : ℕ) (hi : i∈setupTablePreserved) := f.tapes i (setup_table_preserved i hi)
  exact ⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
    blank_of_eq (keep 5 (by decide)) h.2.2.2.2.1,
    blank_of_eq (keep 6 (by decide)) h.2.2.2.2.2.1,
    blank_of_eq (keep 8 (by decide)) h.2.2.2.2.2.2.1,
    blank_of_eq (keep 9 (by decide)) h.2.2.2.2.2.2.2⟩

theorem setup_table_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.Ready s)
    (f : BinaryPrecision.Frame setupWorkspace s.val t.val) (hz : NatAssign.Scratch t.val) :
    a.Ready t := by
  have keep (i : ℕ) (hi : i∈setupTablePreserved) := f.tapes i (setup_table_preserved i hi)
  refine ⟨setup_table_scratch h.scratch f hz,blank_of_eq (keep 7 (by decide)) h.seven,
    BankArray.word_of_eq (keep 200 (by decide)) h.width,
    BankArray.word_of_eq (keep 202 (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 203 (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 204 (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 205 (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

theorem setup_output_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.OutputReady s)
    (f : BinaryPrecision.Frame setupWorkspace s.val t.val) (hz : NatAssign.Scratch t.val) :
    a.OutputReady t := by
  apply h.transfer f.memory _ (setup_table_scratch h.scratch f hz)
    (blank_of_eq (f.tapes 7 (by decide)) h.seven)
  intro i hi
  apply f.tapes i
  apply setup_table_preserved
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms setup_ready_frame
#print axioms setup_output_frame
end Maxwell.Continuum.Profile.WaveMachine.Runtime
