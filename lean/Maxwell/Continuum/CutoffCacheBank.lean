import Maxwell.Continuum.CutoffMonomialCache
import Maxwell.Continuum.RationalDataflowTraceResult

/-! The cache arithmetic starts from an executed constant-size reset,
independently of the preceding profile transform's register values. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def cacheBankInitial : Control := Control.prepend
  [.literal 0 0,.literal 1 0,
   .literal 2 0,.literal 3 0,
   .literal 4 0,.literal 5 2,
   .literal 6 0,.literal 7 0] .done

def cacheInitialValues (v : ℕ→Parts) (i : ℕ) : Parts :=
  if i<8 then if i=5 then Parts.literal 2 else Parts.literal 0 else v i

theorem cacheBankInitial_valid : cacheBankInitial.Valid (Finset.range 8) := by
  simp [cacheBankInitial,Control.prepend,Control.Valid,Instruction.Valid]

theorem cacheBankInitial_evaluate (v : ℕ→Parts) : cacheBankInitial.evaluate v=cacheInitialValues v := by
  funext i
  by_cases hi : i<8
  · interval_cases i <;>
      simp [cacheBankInitial,Control.prepend,Control.evaluate,Instruction.update,cacheInitialValues]
  · have h0 : i≠0 := by omega
    have h1 : i≠1 := by omega
    have h2 : i≠2 := by omega
    have h3 : i≠3 := by omega
    have h4 : i≠4 := by omega
    have h5 : i≠5 := by omega
    have h6 : i≠6 := by omega
    have h7 : i≠7 := by omega
    simp [cacheBankInitial,Control.prepend,Control.evaluate,Instruction.update,cacheInitialValues,
      hi,h0,h1,h2,h3,h4,h5,h6,h7]

theorem cacheInitialValues_width (v : ℕ→Parts) : WidthBank (Finset.range 8) 2 (cacheInitialValues v) := by
  intro i hi
  simp only [cacheInitialValues,ite_eq_left (Finset.mem_range.mp hi)]
  split_ifs
  · unfold Parts.Width Parts.literal
    decide
  · exact (Parts.literal_width RationalWords.width_zero').mono (by decide)

theorem cacheInitialValues_good (v : ℕ→Parts) : Good (Finset.range 8) (cacheInitialValues v) := by
  intro i hi
  simp only [cacheInitialValues,ite_eq_left (Finset.mem_range.mp hi)]
  split_ifs <;> exact Parts.literal_valid _

theorem cacheBankInitial_executes (v : ℕ→Parts) (W : ℕ)
    (hv : WidthBank (Finset.range 8) W v) (hg : Good (Finset.range 8) v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : RationalDataflow.Ready (Finset.range 8) v s) :
    ∃cost t,Executes input tape cacheBankInitial.code cost s t ∧
      cost≤8*operationCost (256*(W+3))+1 ∧
      RationalDataflow.Ready (Finset.range 8) (cacheInitialValues v) t ∧
      BinaryPrecision.Frame (workspace (Finset.range 8)) s.val t.val := by
  have lit : cacheBankInitial.LiteralsFit 2 := by
    norm_num [cacheBankInitial,Control.prepend,Control.LiteralsFit,Instruction.LiteralFits,Parts.Width,Parts.literal]
    decide
  have trace : cacheBankInitial.WidthTrace (Finset.range 8) (256*(W+3)) v := by
    apply (cacheBankInitial.automatic_widthTrace (Finset.range 8) cacheBankInitial_valid v (W+2)
      (hv.mono (by omega)) (lit.mono (by omega))).mono
    change 2^8*(W+2+1)≤256*(W+3)
    omega
  obtain ⟨cost,t,e,hc,ht,f⟩ := cacheBankInitial.executes (Finset.range 8) cacheBankInitial_valid v
    (256*(W+3)) trace hg (by trivial) input tape s hs
  exact ⟨cost,t,e,hc,by simpa only [cacheBankInitial_evaluate] using ht,f⟩

#print axioms cacheBankInitial_executes
end Maxwell.Continuum.Calibration.RawCutoff
