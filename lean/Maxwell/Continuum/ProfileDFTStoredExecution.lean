import Maxwell.Continuum.ProfileDFTNormalization

/-! One complete profile DFT: fixed register reset, stored index/grid
loading, all sample evaluations, and exact final normalization. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalTaylor Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def dftCode (negative : Bool) : Code := .seq (dftInitializeCode negative)
  (.seq dftLoopCode dftNormalizeCode)
def dftWorkspace : Finset ℕ := insert 201 (angularWorkspace dftRegisters)
def dftCost (grid D P U W indexLength oldLength : ℕ) : ℕ :=
  dftInitializeCost W grid indexLength oldLength+
    ((grid+1)*(13*grid.bits.length+15)+grid*dftBodyCost grid D P U grid.bits.length)+
      dftNormalizeCost grid U

theorem dft_external (i : ℕ) (hi : 658 ≤ i ∧ i < 1000) : i∉dftWorkspace := by
  simp only [dftWorkspace,Finset.mem_insert]
  exact not_or_intro (by omega) (scalar_external dftRegisters i (Or.inr hi))

theorem dft_executes (negative : Bool) (grid D P U j W : ℕ)
    (hg0 : 0<grid) (hg : grid≤U) (hD : D≤U) (hP : P≤U) (hj : j≤U) (hW : 1≤W)
    (v : ℕ→Parts) (hw : WidthBank dftRegisters W v) (jword oldWord : List Bool)
    (hjword : addressValue jword=j) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready dftRegisters v s) (hp : Phase.Runtime.Clean s.val) (hz : Glue.Clean s.val)
    (hm : DFTParameters D P s) (hgrid : Word s.val 664 grid)
    (hindex : BankArray.Word s.val 700 jword) (hc : BankArray.Word s.val 201 oldWord) :
    ∃cost t finalWord,Executes input tape (dftCode negative) cost s t ∧
      Nonempty (DFTResult grid D P U (dftFrequency negative j) t) ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length=grid.bits.length ∧
      BinaryPrecision.Frame dftWorkspace s.val t.val ∧
      cost≤dftCost grid D P U W jword.length oldWord.length := by
  obtain ⟨c0,s0,e0,i0,count0,f0,h0⟩ := dft_initialize_executes negative grid D P U j W hg0 hg hj hW
    v hw jword oldWord hjword input tape s hr hp hz hm hgrid hindex hc
  obtain ⟨origin,count0⟩ := count0
  obtain ⟨c1,s1,finalWord,e1,i1,count1,len1,f1,h1⟩ := dft_loop_executes dftRegisters (by decide)
    grid D P U (dftFrequency negative j) hg0 hg hD hP (by simpa only [dftFrequency_abs] using hj)
    grid.bits origin input tape s0 i0 count0 (addressValue_bits grid)
  have frame01 := f0.trans f1
  have grid1 := word_of_eq (frame01.tapes 664 (dft_external 664 (by decide))) hgrid
  obtain ⟨state1⟩ := i1
  obtain ⟨c2,t,e2,result,frame2,h2⟩ := dft_normalize_executes grid D P U (dftFrequency negative j)
    hg0 hg input tape s1 state1 grid1
  refine ⟨c0+(c1+c2),t,finalWord,e0.seq (e1.seq e2),result,
    ⟨origin,(frame2.tapes 201 (scalar_external dftRegisters 201 (by decide))).trans count1⟩,
    len1,frame01.trans (frame2.mono (Finset.subset_insert _ _)),?_⟩
  unfold dftCost
  omega

#print axioms dft_executes
end Maxwell.Continuum.Profile.Runtime
