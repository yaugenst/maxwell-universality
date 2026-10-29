import Maxwell.Cost.RealSparseOrder.LoadFrom
import Maxwell.Cost.RealSparseOrder.Endpoint

namespace Maxwell.Cost.RealSparseOrder.Endpoint
open RealSimulation.Control

theorem bufferAfter_cases (k : ℕ) (a b : Buffer) : Sort.bufferAfter k a b=a ∨Sort.bufferAfter k a b=b := by
  induction k generalizing a b with
  | zero => exact Or.inl rfl
  | succ k ih => exact (ih b a).symm

theorem result_end (m : ℕ) :
    (resultBuffer m).coordinates+2*m≤100+4*m ∧(resultBuffer m).coefficients+m≤100+2*m := by
  rcases bufferAfter_cases m.size initialBuffer (Initialize.secondaryBuffer m) with h|h
  · unfold resultBuffer
    rw [h]
    simp only [initialBuffer]
    constructor <;> omega
  · unfold resultBuffer
    rw [h]
    simp only [Initialize.secondaryBuffer]
    constructor <;> omega

theorem result_safe (m : ℕ) : (resultBuffer m).Safe := by
  rcases bufferAfter_cases m.size initialBuffer (Initialize.secondaryBuffer m) with h|h
  · unfold resultBuffer
    rw [h]
    simp [Buffer.Safe,initialBuffer]
  · unfold resultBuffer
    rw [h]
    simp [Buffer.Safe,Initialize.secondaryBuffer]

private theorem sort_frame {m : ℕ} {s t : RAMState}
    (h : Sort.Frame initialBuffer (Initialize.secondaryBuffer m) m s t) :
    DataFrame initialBuffer (2*m) s t := by
  constructor
  · intro j hj hout
    apply h.1 j hj
    · simp only [initialBuffer] at hout ⊢
      omega
    · simp only [initialBuffer,Initialize.secondaryBuffer] at hout ⊢
      omega
  · intro j hj hout
    apply h.2 j hj
    · simp only [initialBuffer] at hout ⊢
      omega
    · simp only [initialBuffer,Initialize.secondaryBuffer] at hout ⊢
      omega

/-- The same full literal sorter starts after an earlier machine stage and
preserves memory outside the two actual work buffers. -/
theorem from_state (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool) (s : Store) :
    ∃(cost : ℕ) (t : Store),cost≤bound es.length ∧
      Executes (RealSparse.input es vector) tape code cost s t ∧
      Sort.Config t.val (resultBuffer es.length) (spareBuffer es.length)
        (2^es.length.size) es.length ∧
      Records (resultBuffer es.length) t.val (bottomUpSort es) ∧
      DataFrame initialBuffer (2*es.length) s.val t.val ∧
      Merge.Channels s.val t.val := by
  obtain ⟨loaded,loadRun,stored,loadFrame,lr,lo,li⟩ := Load.from_state es vector tape s
  let start := Store.ofState (Initialize.initialized es.length loaded.val)
  have hi : Sort.Invariant start.val initialBuffer (Initialize.secondaryBuffer es.length) 1
      (singletonRuns es) := (Sort.invariant_ofState _ _ _ _ _).mpr (Initialize.invariant es loaded.val stored)
  obtain ⟨cost,t,hcost,run,inv,frame,channels⟩ := Sort.executes (RealSparse.input es vector)
    tape start initialBuffer (Initialize.secondaryBuffer es.length) es hi
  have lf : DataFrame initialBuffer (2*es.length) s.val loaded.val := by
    constructor
    · intro j hj hout
      apply loadFrame.1 j (by omega)
      simp only [initialBuffer] at hout ⊢
      omega
    · intro j hj hout
      apply loadFrame.2 j hj
      simp only [initialBuffer] at hout ⊢
      omega
  refine ⟨(14*es.length+10)+(11+cost),t,?_,Executes.seq loadRun
    (Executes.seq (Initialize.executes es vector tape loaded) run),?_,inv.records,?_,?_⟩
  · unfold bound
    omega
  · have hc := inv.config
    have hlen : (mergePasses es.length.size (singletonRuns es)).flatten.length=es.length :=
      bottomUpSort_length es
    simpa only [resultBuffer,spareBuffer,hlen] using hc
  · exact (lf.trans ((Initialize.data_frame es.length loaded.val initialBuffer).mono (by omega))).trans
      (sort_frame frame)
  · exact ⟨channels.1.trans lr,channels.2.1.trans lo,channels.2.2.trans li⟩

end Maxwell.Cost.RealSparseOrder.Endpoint
