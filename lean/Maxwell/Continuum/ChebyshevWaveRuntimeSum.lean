import Maxwell.Continuum.ChebyshevWaveRuntimeSumStep
import Maxwell.Cost.Structured.CountedShifted
import Maxwell.Continuum.RuntimeCounterClear

/-! One fixed counted Fourier loop, including cleanup of its actual countdown
word. Every sample and width invariant is discharged by the concrete wave code. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
open scoped BigOperators
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

structure LoopReady (Q P : ℕ) (v : ℕ→Parts) (s : Store) : Prop where
  ready : Ready ids v s
  phase : Phase.Runtime.Clean s.val
  floor : DyadicFloor.Clean s.val
  parameters : Parameters Q P s
  rangeWord : Word s.val 652 1
  precisionWord : Word s.val 653 P

def sumWorkspace : Finset ℕ := insert 680 evaluationWorkspace
def sumCode : Code := .seq (CountedShifted.code 680 sumStepCode) (.call (TapeOps.clear 680))
def sumCost (Q P grid W : ℕ) : ℕ :=
  (grid+1)*(13*grid.bits.length+15)+grid*sumStepCost Q P W (sumBankWidth Q P W grid) 1 P+
    6*grid.bits.length+4

theorem count_outside_evaluation : 680∉evaluationWorkspace := by
  exact fun h => (Finset.mem_union.mp h).elim
    (Phase.Runtime.metadata_outside_workspace ids 680 (by decide))
    (DyadicFloor.high_outside_workspace ids 680 (by decide))

theorem LoopReady.counter_frame {Q P : ℕ} {v : ℕ→Parts} {s t : Store} (h : LoopReady Q P v s)
    (f : BinaryPrecision.Frame {680} s.val t.val) : LoopReady Q P v t := by
  have keep (i : ℕ) (hi : i≠680) : t.val.tapes i=s.val.tapes i := f.tapes i (by simpa using hi)
  refine ⟨⟨?_,?_⟩,?_,⟨?_,?_⟩,?_,word_of_eq (keep 652 (by decide)) h.rangeWord,
    word_of_eq (keep 653 (by decide)) h.precisionWord⟩
  · intro i hi
    have hout := RationalDataflow.outside_workspace ids 680 (by decide)
    have hn : i≠680 := fun he => hout (he ▸ Finset.mem_union_right _ hi)
    exact word_of_eq (keep i hn) (h.ready.1 i hi)
  · intro i hi
    exact blank_of_eq (keep i (by omega)) (h.ready.2 i hi)
  · intro i hi
    have hp : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hn : i≠680 := by intro he;subst i;exact (by decide : 680∉PhaseMachine.Runtime.ids) hp
    exact blank_of_eq (keep i hn) (h.phase i hi)
  · exact blank_of_eq (keep 4 (by decide)) h.floor.1
  · intro i hi
    have hn : i≠680 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact blank_of_eq (keep i hn) (h.floor.2 i hi)
  · intro i hi
    have hr := parameterIds_range i hi
    exact word_of_eq (keep i (by omega)) (h.parameters i hi)

theorem count_frame {s t : Store} (f : CountedShifted.Frame 680 s t) :
    BinaryPrecision.Frame {680} s.val t.val := by
  refine ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,?_⟩
  intro i hi
  exact f.2.2.2.2.2.1 i (by simpa using hi)

theorem sum_executes (Q P grid W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) (hg : Good ids v)
    (hW : 1≤W) (hgrid : grid.bits.length≤W) (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s)
    (hn : Word s.val 680 grid) :
    ∃cost t,Executes input tape sumCode cost s t ∧ cost≤sumCost Q P grid W ∧
      LoopReady Q P (sumValues Q P v grid) t ∧ Blank t.val 680 ∧
      BinaryPrecision.Frame sumWorkspace s.val t.val := by
  obtain ⟨origin,hn⟩ := hn
  let B := sumBankWidth Q P W grid
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤grid ∧
    LoopReady Q P (sumValues Q P v (grid-remaining)) st ∧
      BinaryPrecision.Frame sumWorkspace s.val st.val
  have stable : ∀remaining a b,CountedShifted.Frame 680 a b → inv remaining a → inv remaining b := by
    intro remaining a b f h
    exact ⟨h.1,h.2.1.counter_frame (count_frame f),h.2.2.trans
      ((count_frame f).mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)))⟩
  have body : ∀remaining xs a,inv (remaining+1) a →
      a.val.tapes 680=BitTape.shifted xs origin → addressValue xs=remaining →
      ∃cost b,Executes input tape sumStepCode cost a b ∧ inv remaining b ∧
        b.val.tapes 680=BitTape.shifted xs origin ∧ cost≤sumStepCost Q P W B 1 P := by
    intro remaining xs a ha haWord _
    let k := grid-(remaining+1)
    have hk : k<grid := by have := ha.1;dsimp [k];omega
    have he : k+1=grid-remaining := by have := ha.1;dsimp [k];omega
    have hwb := sumValues_width Q P grid W v hw hW hgrid hcount hone k hk.le
    have hB : sumBankWidth Q P W k≤B := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.add_le_add_right hk.le 1)) W
    have hm := sumValues_metadata_width Q P grid W v hw hW hgrid hcount hone k hk.le
    obtain ⟨c,b,e,hc,rb,pb,fb,mb,qb,nb,ft⟩ := sumStep_executes Q P W B 1 P
      (sumValues Q P v k) (hwb.mono hB) hm (sumValues_good Q P v hg k)
      input tape a ha.2.1.ready ha.2.1.phase ha.2.1.floor ha.2.1.parameters
      ha.2.1.rangeWord ha.2.1.precisionWord
    have hb : LoopReady Q P (sumValues Q P v (k+1)) b := ⟨rb,pb,fb,mb,qb,nb⟩
    rw [he] at hb
    exact ⟨c,b,e,⟨by have := ha.1;omega,hb,ha.2.2.trans (ft.mono (Finset.subset_insert _ _))⟩,
      (ft.tapes 680 count_outside_evaluation).trans haWord,hc⟩
  obtain ⟨c0,s0,finalWord,e0,h0,w0,len0,_,hc0⟩ := CountedShifted.executes 680 origin sumStepCode input tape
    inv (fun _ => sumStepCost Q P W B 1 P) stable body grid grid.bits s (by simp) hn
      ⟨le_rfl,by simpa [sumValues] using hs,BinaryPrecision.Frame.refl _ _⟩
  have ready0 : LoopReady Q P (sumValues Q P v grid) s0 := by simpa only [Nat.sub_zero] using h0.2.1
  obtain ⟨t,e1,z1,f1⟩ := RuntimeCounter.clear_executes 680 input tape finalWord origin s0 w0
  refine ⟨c0+(6*finalWord.length+4),t,e0.seq e1,?_,ready0.counter_frame f1,z1,
    h0.2.2.trans (f1.mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)))⟩
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hc0
  unfold sumCost
  dsimp [B] at hc0
  omega

#print axioms sum_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
