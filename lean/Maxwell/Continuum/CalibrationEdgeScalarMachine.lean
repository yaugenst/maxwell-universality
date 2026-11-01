import Maxwell.Continuum.CalibrationEdgeScalarEmit

/-! Compute, store, and clean one edge test's scalar inputs. The reusable
boundary returns the Machin workspace blank after charging every clear. -/
namespace Maxwell.Continuum.Calibration.EdgeScalar
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator RationalDataflow
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

def coreCode : Code := .seq machinCode (.seq emitCode (WordCleanup.code machineTapes))
def coreCost (N B : ℕ) : ℕ := machinCost N+emitCost (inputWidth N B)+24*(6*cleanupWidth N+4)+1
def coreWork : Finset ℕ := ({0,1,2,3}∪machineSet)∪outputPorts
def resultWidth (N B : ℕ) : ℕ := emitWidth (inputWidth N B)

theorem core_executes (N B : ℕ) (p : Parts) (old : ℕ→Parts)
    (midWidth : p.Width B) (oldWidth : WidthBank saved B old)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (precision : Word s.val 850 N) (fresh : Fresh s.val) (scratch : NatAssign.Scratch s.val)
    (previous : Cells saved old s.val) (midpoint : StoredParts.Stored (positivePort 2302) p s.val) :
    ∃steps t,Executes input tape coreCode steps s t ∧ steps≤coreCost N B ∧
      Cells saved (result N p) t.val ∧ WidthBank saved (resultWidth N B) (result N p) ∧
      NatAssign.Scratch t.val ∧ Fresh t.val ∧ BinaryPrecision.Frame coreWork s.val t.val := by
  obtain ⟨c,a,e,charge,bank,blank,aux,zero,frame⟩:=machin_executes N input tape s precision fresh scratch
  have retained (i : ℕ) (hi : 1000≤ i) : a.val.tapes i=s.val.tapes i := by
    apply frame.tapes
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
    refine ⟨by omega,?_⟩
    intro member
    have := (machine_member i).mp member
    omega
  have oldA := previous.transfer retained
  have midA : StoredParts.Stored (positivePort 2302) p a.val :=
    ⟨word_of_eq (retained _ (by decide)) midpoint.1,
     word_of_eq (retained _ (by decide)) midpoint.2.1,
     word_of_eq (retained _ (by decide)) midpoint.2.2⟩
  obtain ⟨d,b,eb,db,stored,width,clear,fb⟩:=emit_executes N p old (inputWidth N B)
    (by unfold inputWidth;omega) (emit_input_width N B p old midWidth oldWidth)
    input tape a (emit_input_bank N p old a.val bank oldA midA) blank
  have oldWords:=machin_bounded N a.val bank aux zero
  have cleanable : WordCleanup.Bounded machineTapes (cleanupWidth N) b.val := by
    intro i hi
    obtain ⟨bits,hlen,word⟩:=oldWords i hi
    refine ⟨bits,hlen,BankArray.word_of_eq (fb.tapes i ?_) word⟩
    have member : i∈machineSet := by simpa only [machineSet,List.mem_toFinset] using hi
    have range := (machine_member i).mp member
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨by omega,fun output=>Finset.disjoint_left.mp output_machine_disjoint output member⟩
  obtain ⟨f,t,et,ft,reset,fc⟩:=WordCleanup.executes machineTapes (cleanupWidth N) input tape b cleanable
  refine ⟨c+(d+f),t,e.seq (eb.seq et),?_,stored.transfer_tapes ?_,width,?_,?_,
    (frame.mono (Finset.subset_union_left)).trans ((fb.mono ?_).trans (fc.mono ?_))⟩
  · have length : machineTapes.length=24 := by decide
    rw [length] at ft
    unfold coreCost
    omega
  · intro i hi
    apply fc.tapes
    exact fun member=>Finset.disjoint_left.mp output_machine_disjoint hi member
  · intro i hi
    apply blank_of_eq (fc.tapes i ?_) (clear i hi)
    intro member
    have := (machine_member i).mp member
    omega
  · intro i hi
    exact reset i (by simpa only [machineSet,List.mem_toFinset] using hi)
  · intro i hi
    rcases Finset.mem_union.mp hi with low|output
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ low)
    · exact Finset.mem_union_right _ output
  · intro i hi
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)

#print axioms core_executes
end Maxwell.Continuum.Calibration.EdgeScalar
