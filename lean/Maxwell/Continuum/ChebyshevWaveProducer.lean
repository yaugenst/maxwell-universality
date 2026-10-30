import Maxwell.Continuum.ChebyshevWaveCacheSetupFrame
import Maxwell.Continuum.ChebyshevWaveCacheBase
import Maxwell.Continuum.ChebyshevWaveCacheCompiled

/-! One fixed wave-cache producer from stored Q, N and frequency. Dimension
selection, grid reciprocals, scale generation, sampling and table writes
all execute inside this program. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open RationalDataflow.PartArray
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def producerWidth (Q N W : ℕ) : ℕ := dimensionWidth W+waveWorkBits (8*Q) N+W+8
def producerCode : Code := .seq cacheSetupCode (.seq baseCode cacheCode)
def producerBound (Q N W : ℕ) : ℕ :=
  2^160*(W+waveWorkBits (8*Q) N+4)^2+baseCost W (waveGrid (8*Q) N)+
    cacheBound Q N (waveDegree (8*Q) N+1) (producerWidth Q N W)

theorem producer_executes {n : ℕ} (a : Table n) (Q N W : ℕ)
    (b : Table (2*(waveDegree (8*Q) N+1)))
    (hm : b.MetadataWidth (producerWidth Q N W)) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hfit : waveWorkBits (8*Q) N+7≤addressValue b.width)
    (v : ℕ→Parts) (hw : WidthBank ids W v) (hv : (v 10).Valid) (hq : |(v 10).value|≤Q)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (hW : 6≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready ids v s) (hp : Phase.Runtime.Clean s.val) (hf : DyadicFloor.Clean s.val)
    (hsetup : NatAssign.Bank setupIds (initialSetup Q N) s.val)
    (ha : a.Ready s) (hb : b.OutputReady s)
    (hpower : Blank s.val 144) (hpowerCount : Blank s.val 146) (hinner : Blank s.val 680)
    (hsaved : ∀i∈savedPorts,Blank s.val i) :
    ∃cost t,Executes input tape producerCode cost s t ∧ cost≤producerBound Q N W ∧
      Nonempty (CacheState a (v 10).value Q N (waveDegree (8*Q) N+1) (producerWidth Q N W)
        (baseValues (waveGrid (8*Q) N) v) b 0 t) ∧ Blank t.val 201 := by
  obtain ⟨c0,s0,e0,h0,_,z0,parameters0,range0,precision0,grid0,count0,power0,_,f0⟩ :=
    cacheSetup_executes Q N W hQ hN hW input tape s hsetup hs.2 hpower hpowerCount
  have ready0 := setup_ready_frame hs f0 z0
  have loop0 : LoopReady Q (waveWorkBits (8*Q) N) v s0 :=
    ⟨ready0,setup_phase_frame hp f0,setup_floor_frame hf f0,parameters0,range0,precision0⟩
  have a0 := setup_table_frame ha f0 z0
  have b0 := setup_output_frame hb f0 z0
  have inner0 := blank_of_eq (f0.tapes 680 (by decide)) hinner
  have saved0 : ∀i∈savedPorts,Blank s0.val i := by
    intro i hi
    have hd : Disjoint savedPorts setupWorkspace := by decide
    exact blank_of_eq (f0.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)) (hsaved i hi)
  obtain ⟨c1,s1,e1,h1,r1,f1⟩ := base_executes (waveGrid (8*Q) N) W v hw input tape s0 ready0 grid0
  have loop1 := loop0.arithmetic_frame f1 r1
  have a1 := a0.arithmetic_frame ids f1 r1.2
  have f1' : BinaryPrecision.Frame encodedWorkspace s0.val s1.val :=
    f1.mono (arithmetic_subset_cosine.trans (Finset.subset_insert _ _))
  have b1 := Table.OutputReady.wave_frame b0 f1' r1.2
  have inner1 := blank_of_eq (f1.tapes 680 (RationalDataflow.outside_workspace ids 680 (by decide))) inner0
  have grid1 := word_of_eq (f1.tapes 681 (RationalDataflow.outside_workspace ids 681 (by decide))) grid0
  have count1 := word_of_eq (f1.tapes 201 (RationalDataflow.outside_workspace ids 201 (by decide))) count0
  have power1 := word_of_eq (f1.tapes 144 (RationalDataflow.outside_workspace ids 144 (by decide))) power0
  have saved1 : ∀i∈savedPorts,Blank s1.val i := by
    intro i hi
    have hr := savedPorts_range i hi
    exact blank_of_eq (f1.tapes i (RationalDataflow.outside_workspace ids i (by omega))) (saved0 i hi)
  have hB : 1≤producerWidth Q N W := by unfold producerWidth;omega
  have hWB : W≤producerWidth Q N W := by unfold producerWidth;omega
  have hgrid : (waveGrid (8*Q) N).bits.length≤producerWidth Q N W := by
    have hd := finalDimensions_width Q N W hQ hN hW 715 (by decide)
    rw [finalDimensions_grid] at hd
    exact hd.trans (by unfold producerWidth;omega)
  have hcount : (waveDegree (8*Q) N+1).bits.length≤producerWidth Q N W := by
    have hd := finalDimensions_width Q N W hQ hN hW 716 (by decide)
    rw [finalDimensions_count] at hd
    exact hd.trans (by unfold producerWidth;omega)
  have hgridpos : 0<waveGrid (8*Q) N := by unfold waveGrid;omega
  have baseWidth := baseValues_width (waveGrid (8*Q) N) (producerWidth Q N W) v
    ((hw 10 (by decide)).mono hWB) hgrid hB
  obtain ⟨c2,t,e2,h2,state,hblank⟩ := cache_executes a (v 10).value Q N (waveDegree (8*Q) N+1)
    (producerWidth Q N W) b hm hsep hdisjoint hq le_rfl hfit
    (baseValues (waveGrid (8*Q) N) v) baseWidth (baseValues_good _ hgridpos v hv) hB hgrid hcount
    (baseValues_one _ v) (baseValues_input _ v) input tape s1 loop1 a1 b1 count1 inner1 grid1 saved1 power1
  have hc0 := h0.trans (cacheSetupCost_polynomial W (waveWorkBits (8*Q) N))
  have hc2 : c2≤cacheBound Q N (waveDegree (8*Q) N+1) (producerWidth Q N W) :=
    h2.trans (cache_cost_polynomial Q (waveWorkBits (8*Q) N) (producerWidth Q N W)
      (waveGrid (8*Q) N) (waveDegree (8*Q) N+1) hgrid hcount)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,state,hblank⟩
  unfold producerBound
  omega

#print axioms producer_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
