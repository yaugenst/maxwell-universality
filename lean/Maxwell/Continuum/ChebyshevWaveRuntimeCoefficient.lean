import Maxwell.Continuum.ChebyshevWaveRuntimeSum

/-! A fixed runtime Fourier coefficient producer with the actual continuum
plane-wave approximation bound. No sample or execution oracle is supplied. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def coefficientCode : Code := .seq sumCode (program normalizeInstructions)
def coefficientCost (Q P grid W : ℕ) : ℕ :=
  sumCost Q P grid W+2*operationCost (16*(sumBankWidth Q P W grid+1))+1
noncomputable def storedCenter (v : ℕ→Parts) : ℂ := ((v 8).value:ℂ)+((v 9).value:ℂ)*Complex.I

theorem LoopReady.arithmetic_frame {Q P : ℕ} {v w : ℕ→Parts} {s t : Store} (h : LoopReady Q P v s)
    (f : BinaryPrecision.Frame (RationalDataflow.workspace ids) s.val t.val) (hr : Ready ids w t) :
    LoopReady Q P w t :=
  ⟨hr,h.phase.arithmetic_frame f hr,h.floor.arithmetic_frame f,h.parameters.arithmetic_frame f,
    word_of_eq (f.tapes 652 (RationalDataflow.outside_workspace ids 652 (by decide))) h.rangeWord,
    word_of_eq (f.tapes 653 (RationalDataflow.outside_workspace ids 653 (by decide))) h.precisionWord⟩

theorem normalizeInstructions_valid : ∀a∈normalizeInstructions,a.Valid ids := by
  simp [normalizeInstructions,RationalDataflow.Instruction.Valid,ids]

theorem normalize_program_width (B : ℕ) : programWidth normalizeInstructions (fun _ => B)≤16*(B+1) := by
  simp [normalizeInstructions,programWidth,RationalDataflow.Instruction.widthUpdate,RationalDataflow.Instruction.resultWidth]
  omega

theorem coefficient_executes (Q P grid W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) (hg : Good ids v)
    (hW : 1≤W) (hgrid : grid.bits.length≤W) (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s) (hn : Word s.val 680 grid) :
    ∃cost t,Executes input tape coefficientCode cost s t ∧ cost≤coefficientCost Q P grid W ∧
      LoopReady Q P (coefficientValues Q P grid v) t ∧ Blank t.val 680 ∧
      BinaryPrecision.Frame sumWorkspace s.val t.val := by
  obtain ⟨c0,s0,e0,hc0,r0,z0,f0⟩ := sum_executes Q P grid W v hw hg hW hgrid hcount hone input tape s hs hn
  have hw0 := sumValues_width Q P grid W v hw hW hgrid hcount hone grid le_rfl
  have htrace := inferred_widthTrace ids normalizeInstructions normalizeInstructions_valid
    (fun _ => sumBankWidth Q P W grid) (sumValues Q P v grid) hw0 _
    (hw0.mono (by omega : sumBankWidth Q P W grid≤16*(sumBankWidth Q P W grid+1)))
    (normalize_program_width _)
  obtain ⟨c1,t,e1,hc1,r1,f1⟩ := program_executes ids normalizeInstructions normalizeInstructions_valid
    (sumValues Q P v grid) _ htrace input tape s0 r0.ready
  have hc1' : c1≤2*operationCost (16*(sumBankWidth Q P W grid+1))+1 := by
    simpa only [show normalizeInstructions.length=2 by rfl] using hc1
  refine ⟨c0+c1,t,e0.seq e1,?_,r0.arithmetic_frame f1 r1,
    blank_of_eq (f1.tapes 680 (RationalDataflow.outside_workspace ids 680 (by decide))) z0,
    f0.trans (f1.mono (arithmetic_subset_evaluation.trans (Finset.subset_insert _ _)))⟩
  unfold coefficientCost
  omega

theorem storedCenter_eq (grid : ℕ) [NeZero grid] (q : ℚ) (n : ℤ) (Q P : ℕ) (v : ℕ→Parts)
    (hg : Good ids v) (hi : SumInput grid q n 0 v) (hz0 : (v 8).value=0) (hz1 : (v 9).value=0) :
    storedCenter (coefficientValues Q P grid v)=
      Calibration.rectangleCenter (rationalWaveCoefficient grid q Q P n) := by
  have h := coefficientValues_correct grid q n Q P v hg hi hz0 hz1
  simp only [storedCenter,Calibration.rectangleCenter,h.1,h.2]

theorem coefficient_computes (grid D K Q P W : ℕ) [NeZero grid] (q : ℚ) (n : ℤ)
    (hq : |q|≤Q) (hk : |2*Real.pi*(q:ℝ)|≤K) (hindex : |n|≤(D:ℤ))
    (hresolution : waveDegree K P+D≤grid) (v : ℕ→Parts) (hw : WidthBank ids W v) (hg : Good ids v)
    (hW : 1≤W) (hgrid : grid.bits.length≤W) (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩)
    (hi : SumInput grid q n 0 v) (hz0 : (v 8).value=0) (hz1 : (v 9).value=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s) (hn : Word s.val 680 grid) :
    ∃t : Store,
      (runPriced (coefficientCode.compile.next input tape) (coefficientCost Q P grid W+1) s.val).finished=
        some (t.place coefficientCode.size) ∧
      (runPriced (coefficientCode.compile.next input tape) (coefficientCost Q P grid W+1) s.val).instructions≤
        coefficientCost Q P grid W ∧
      LoopReady Q P (coefficientValues Q P grid v) t ∧ Blank t.val 680 ∧
      ‖waveCoefficient (2*Real.pi*(q:ℝ)) n-storedCenter (coefficientValues Q P grid v)‖≤9*(1/2:ℝ)^P := by
  obtain ⟨c,t,e,hc,rt,zt,_⟩ := coefficient_executes Q P grid W v hw hg hW hgrid hcount hone input tape s hs hn
  obtain ⟨hrun,hsteps⟩ := e.compiled_run (coefficientCost Q P grid W+1) (by omega)
  refine ⟨t,hrun,hsteps ▸ hc,rt,zt,?_⟩
  rw [storedCenter_eq grid q n Q P v hg hi hz0 hz1]
  exact rationalWaveCoefficient_full_error grid D K P q Q hq hk n hindex hresolution

#print axioms coefficient_computes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
