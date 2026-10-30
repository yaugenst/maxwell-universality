import Maxwell.Continuum.ChebyshevWaveRuntimeCosine
import Maxwell.Continuum.DyadicFloorStoredPowerCost

/-! Fixed stored-scale rounding of the two actual Fourier channels. The scale
is an ordinary runtime word and is preserved for every coefficient in a table. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def roundPairCode : Code := .seq (DyadicFloor.StoredPower.code 8 8) (DyadicFloor.StoredPower.code 9 9)
def roundPairValues (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (Function.update v 8 (DyadicFloor.result P (v 8))) 9 (DyadicFloor.result P (v 9))
def roundPairCost (P B : ℕ) : ℕ := DyadicFloor.costBound P B+DyadicFloor.costBound P (2*B+P+3)

theorem LoopReady.floor_frame {Q P : ℕ} {v w : ℕ→Parts} {s t : Store} (h : LoopReady Q P v s)
    (f : BinaryPrecision.Frame (DyadicFloor.workspace ids) s.val t.val)
    (hr : Ready ids w t) (hf : DyadicFloor.Clean t.val) : LoopReady Q P w t :=
  ⟨hr,DyadicFloor.runtimePhase_clean h.phase f hr,hf,h.parameters.floor_frame f,
    word_of_eq (f.tapes 652 (DyadicFloor.high_outside_workspace ids 652 (by decide))) h.rangeWord,
    word_of_eq (f.tapes 653 (DyadicFloor.high_outside_workspace ids 653 (by decide))) h.precisionWord⟩

theorem LoopReady.stored_floor_frame {Q P : ℕ} {v w : ℕ→Parts} {s t : Store} (h : LoopReady Q P v s)
    (f : BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace ids) s.val t.val)
    (hr : Ready ids w t) (hf : DyadicFloor.Clean t.val) : LoopReady Q P w t := by
  have keep (i : ℕ) (hi : 600 ≤ i ∧ i<1000) : t.val.tapes i=s.val.tapes i :=
    f.tapes i (by
      simp only [DyadicFloor.StoredPower.workspace,Finset.mem_insert]
      exact not_or_intro (by omega) (DyadicFloor.high_outside_workspace ids i hi))
  refine ⟨hr,?_,hf,?_,word_of_eq (keep 652 (by decide)) h.rangeWord,
    word_of_eq (keep 653 (by decide)) h.precisionWord⟩
  · intro i hi
    have hp : i∈PhaseMachine.Runtime.ids := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)
    by_cases hm : i∈RationalDataflow.ids ids
    · have hw := hr.1 i hm
      rw [dataValues_small w (Phase.Runtime.ids_small i hp)] at hw
      exact (zero_word_iff_blank _ _).mp hw
    · have hg := PhaseMachine.Runtime.ids_ge i hp
      have hx : i∉DyadicFloor.extraIds∪NaturalQuotient.workPorts ∧ i≠144 := by
        simp only [PhaseMachine.Runtime.ids,PhaseMachine.Runtime.extras,PhaseMachine.allIds,
          PhaseMachine.ids,Machin.allIds,RationalArctan.ids,RationalMagnitude.ids,RationalTaylor.ids,
          Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hp
        simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton]
        omega
      have h4 : i≠4 := by intro he;subst i;exact (by decide : 4∉PhaseMachine.Runtime.ids) hp
      apply blank_of_eq (f.tapes i _) (h.phase i hi)
      intro hc
      rcases Finset.mem_insert.mp hc with he|hc
      · exact hx.2 he
      rcases Finset.mem_union.mp hc with hz|hc
      · simp only [Finset.mem_insert,Finset.mem_singleton] at hz
        omega
      rcases Finset.mem_union.mp hc with hc|hq
      · rcases Finset.mem_union.mp hc with hc|he
        · exact hm hc
        · exact hx.1 (Finset.mem_union_left _ he)
      · exact hx.1 (Finset.mem_union_right _ hq)
  · intro i hi
    have hh := parameterIds_range i hi
    exact word_of_eq (keep i (by omega)) (h.parameters i hi)

theorem roundPair_width (P B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v) :
    WidthBank ids (2*B+P+3) (roundPairValues P v) :=
  ((hw.mono (by omega)).update 8 (DyadicFloor.result_width P B (v 8) (hw 8 (by decide)))).update
    9 (DyadicFloor.result_width P B (v 9) (hw 9 (by decide)))

theorem roundPair_good (P : ℕ) (v : ℕ→Parts) (hg : Good ids v) : Good ids (roundPairValues P v) :=
  (hg.update 8 (DyadicFloor.result_valid P _)).update 9 (DyadicFloor.result_valid P _)

theorem round_pair_executes (Q P B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v) (hg : Good ids v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s)
    (hpower : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape roundPairCode cost s t ∧ cost ≤ roundPairCost P B ∧
      LoopReady Q P (roundPairValues P v) t ∧ Word t.val 144 (2^P) ∧
      BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace ids) s.val t.val := by
  obtain ⟨c0,s0,e0,hc0,r0,z0,p0,f0⟩ := DyadicFloor.StoredPower.executes ids P 8 8 (by decide) (by decide)
    v B hw (hg 8 (by decide)) input tape s hs.ready hs.floor hpower
  have lr0 := hs.stored_floor_frame f0 r0 z0
  have hw0 : WidthBank ids (2*B+P+3) (Function.update v 8 (DyadicFloor.result P (v 8))) :=
    (hw.mono (by omega)).update 8 (DyadicFloor.result_width P B _ (hw 8 (by decide)))
  obtain ⟨c1,t,e1,hc1,r1,z1,p1,f1⟩ := DyadicFloor.StoredPower.executes ids P 9 9 (by decide) (by decide)
    _ (2*B+P+3) hw0 (by simpa using hg 9 (by decide)) input tape s0 lr0.ready lr0.floor p0
  have rt : LoopReady Q P (roundPairValues P v) t := by
    simpa only [roundPairValues,Function.update_of_ne (by decide : (9:ℕ)≠8)] using lr0.stored_floor_frame f1 r1 z1
  exact ⟨c0+c1,t,e0.seq e1,by unfold roundPairCost;omega,rt,p1,f0.trans f1⟩

theorem roundPairValues_correct (P : ℕ) (v : ℕ→Parts) (hg : Good ids v) :
    (roundPairValues P v 8).value=((roundDyadic P (v 8).value).numerator:ℚ) ∧
    (roundPairValues P v 9).value=((roundDyadic P (v 9).value).numerator:ℚ) := by
  simp only [roundPairValues,Function.update_self,Function.update_of_ne (by decide : (8:ℕ)≠9)]
  exact ⟨DyadicFloor.result_value P _ (hg 8 (by decide)),DyadicFloor.result_value P _ (hg 9 (by decide))⟩

theorem roundPairValues_denominator (P : ℕ) (v : ℕ→Parts) :
    (roundPairValues P v 8).denominator=1 ∧ (roundPairValues P v 9).denominator=1 := by
  simp [roundPairValues,DyadicFloor.result]

theorem roundedCosine_correct (grid : ℕ) [NeZero grid] (q : ℚ) (j Q P : ℕ) (v : ℕ→Parts)
    (hv : Good ids v) (hi : SumInput grid q (j:ℤ) 0 v) (hz0 : (v 8).value=0) (hz1 : (v 9).value=0) :
    (roundPairValues P (cosineValues Q P grid v) 8).value=
      ((roundComplex P (rationalWaveCosineCoefficient grid q Q P j)).1.numerator:ℚ) ∧
    (roundPairValues P (cosineValues Q P grid v) 9).value=
      ((roundComplex P (rationalWaveCosineCoefficient grid q Q P j)).2.numerator:ℚ) := by
  have hc := cosineValues_correct grid q j Q P v hv hi hz0 hz1
  simpa only [roundComplex,hc.1,hc.2] using
    roundPairValues_correct P _ (cosineValues_good Q P grid v hv)

#print axioms round_pair_executes
#print axioms roundedCosine_correct
end Maxwell.Continuum.Profile.WaveMachine.Runtime
