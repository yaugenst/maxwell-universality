import Maxwell.Continuum.ProfileEndpointData

/-! The executed descending recurrence computes the exact two endpoint
corrections used by the encoded profile. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow
set_option maxHeartbeats 2500000

theorem endpointStep_good (v : ℕ→Parts) (hv : Good dftRegisters v) :
    Good dftRegisters (endpointStep v) :=
  evaluate_good dftRegisters endpointBody endpointBody_valid v hv (by
    simp [endpointBody,AdmissibleTrace,Instruction.Admissible])

theorem endpointValues_moments {n : ℕ} (a : PartArray.Table n) (v : ℕ→Parts)
    (ha : ∀i,(a.get i).Valid) (hv : Good dftRegisters v)
    (hz : (v 0).value=0 ∧ (v 2).value=0 ∧ (v 3).value=0)
    (k : ℕ) (hk : k≤n) :
    Good dftRegisters (endpointValues a v k) ∧
    (endpointValues a v k 0).value=suffixMoment (fun j => (a.getD j).value) n (n-k) 0 ∧
    (endpointValues a v k 2).value=suffixMoment (fun j => (a.getD j).value) n (n-k) 1 ∧
    (endpointValues a v k 3).value=suffixMoment (fun j => (a.getD j).value) n (n-k) 2 := by
  induction k with
  | zero => simpa only [endpointValues,PartArray.programIterate,Nat.sub_zero,suffixMoment_empty] using
      And.intro hv hz
  | succ k ih =>
    obtain ⟨hg,h0,h2,h3⟩ := ih (by omega)
    let r := n-1-k
    have hr : r<n := by dsimp [r];omega
    have he : a.getD r=a.get ⟨r,hr⟩ := by simp only [PartArray.Table.getD,dite_eq_left hr]
    have loadedGood : Good dftRegisters (endpointLoaded a v k) := hg.update 1 (by
      change (a.getD r).Valid
      rw [he]
      exact ha _)
    have hremain : n-k=r+1 := by dsimp [r];omega
    have hnext : n-(k+1)=r := by dsimp [r];omega
    obtain ⟨he0,he2,he3⟩ := endpointStep_values _ loadedGood
    have hv0 : (endpointLoaded a v k 0).value=(endpointValues a v k 0).value := by
      simp [endpointLoaded,PartArray.programLoaded,endpointValues]
    have hv1 : (endpointLoaded a v k 1).value=(a.getD r).value := by
      simp [endpointLoaded,PartArray.programLoaded,r]
    have hv2 : (endpointLoaded a v k 2).value=(endpointValues a v k 2).value := by
      simp [endpointLoaded,PartArray.programLoaded,endpointValues]
    have hv3 : (endpointLoaded a v k 3).value=(endpointValues a v k 3).value := by
      simp [endpointLoaded,PartArray.programLoaded,endpointValues]
    rw [hv0,hv1,h0,hremain] at he0
    rw [hv2,hv0,h2,h0,hremain] at he2
    rw [hv3,hv2,hv0,h3,h2,h0,hremain] at he3
    obtain ⟨s0,s1,s2⟩ := suffixMoment_step (fun j => (a.getD j).value) n r hr
    refine ⟨endpointStep_good _ loadedGood,?_,?_,?_⟩
    · change (endpointStep (endpointLoaded a v k) 0).value=_
      simpa only [hnext] using he0.trans s0.symm
    · change (endpointStep (endpointLoaded a v k) 2).value=_
      simpa only [hnext] using he2.trans s1.symm
    · change (endpointStep (endpointLoaded a v k) 3).value=_
      simpa only [hnext] using he3.trans s2.symm

theorem endpointValues_final {n : ℕ} (a : PartArray.Table n) (v : ℕ→Parts)
    (ha : ∀i,(a.get i).Valid) (hv : Good dftRegisters v)
    (hz : (v 0).value=0 ∧ (v 2).value=0 ∧ (v 3).value=0) :
    (endpointValues a v n 0).value=∑j∈Finset.range n,(a.getD j).value ∧
    (endpointValues a v n 3).value=∑j∈Finset.range n,(j:ℚ)^2*(a.getD j).value := by
  obtain ⟨_,h0,_,h3⟩ := endpointValues_moments a v ha hv hz n le_rfl
  simpa only [Nat.sub_self,suffixMoment_final,pow_zero,one_mul] using And.intro h0 h3

theorem endpointValues_profile (N : ℕ) (a : PartArray.Table (profileDegree N)) (v : ℕ→Parts)
    (ha : ∀i,(a.get i).Valid)
    (he : ∀i,(a.get i).value=((roundedCoefficient N i.val).numerator:ℚ))
    (hv : Good dftRegisters v) (hz : (v 0).value=0 ∧ (v 2).value=0 ∧ (v 3).value=0) :
    (endpointValues a v (profileDegree N) 0).value=(endpointInteger N).value ∧
    (endpointValues a v (profileDegree N) 3).value=(slopeInteger N).value := by
  obtain ⟨h0,h3⟩ := endpointValues_final a v ha hv hz
  rw [h0,h3,endpointInteger_value,slopeInteger_value]
  simp only [endpointValueNumerator,endpointSlopeNumerator,Int.cast_sum,Int.cast_mul,
    Int.cast_pow,Int.cast_natCast]
  constructor
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simpa only [PartArray.Table.getD,dite_eq_left hj'] using he ⟨j,hj'⟩
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show (a.getD j).value=((roundedCoefficient N j).numerator:ℚ) by
      simpa only [PartArray.Table.getD,dite_eq_left hj'] using he ⟨j,hj'⟩]
    ring

#print axioms endpointValues_profile
end Maxwell.Continuum.Profile.Runtime
