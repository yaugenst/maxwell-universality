import Maxwell.Continuum.CalibrationSeedRootTerms

/-! Exact meaning of the executed eight-term cache computation. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow FreeFiber PeriodicSampling
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def contribution (M D N : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (u : Fin 3→ℕ) (j : Fin 3) (part : Fin 2) (parity : Corner.Parity) : ℚ :=
  if h : inside M D parity u then
    (a.get ⟨index M D parity u (cachePart part),index_lt M D parity u (cachePart part) h⟩).value*
      seedComponent N j*sign parity j part
  else 0

theorem guarded_good (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (u : Fin 3→ℕ) (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) (v : ℕ→Parts)
    (good : Good slots v) (entryValid : ∀i,(a.get i).Valid) :
    Good slots (guardedValues M D a u parity j part v) := by
  unfold guardedValues
  split_ifs
  · exact (termControl parity j part).evaluate_good slots (term_valid parity j part) _
      (good.update 24 (entryValid _)) (term_admissible parity j part _)
  · exact good

theorem guarded_seed_keep (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (u : Fin 3→ℕ) (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) (v : ℕ→Parts)
    (k : Fin 3) : guardedValues M D a u parity j part v (28+k.val)=v (28+k.val) := by
  have hk := k.isLt
  unfold guardedValues
  split_ifs
  · rw [term_keep parity j part _ _ (by omega),Function.update_of_ne (by omega : 28+k.val≠24)]
  · rfl

theorem guarded_value (M D N : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (u : Fin 3→ℕ) (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) (v : ℕ→Parts)
    (good : Good slots v) (entryValid : ∀i,(a.get i).Valid)
    (seed : (v (28+j.val)).value=seedComponent N j) :
    (guardedValues M D a u parity j part v 27).value=
      (v 27).value+contribution M D N a u j part parity := by
  unfold guardedValues contribution
  split_ifs with h
  · rw [term_value parity j part _ (good.update 24 (entryValid _))]
    have hj := j.isLt
    simp [show 28+j.val≠24 by omega,seed]
  · simp

theorem terms_value (M D N : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (u : Fin 3→ℕ) (ps : List Corner.Parity) (j : Fin 3) (part : Fin 2) (v : ℕ→Parts)
    (good : Good slots v) (entryValid : ∀i,(a.get i).Valid)
    (seed : (v (28+j.val)).value=seedComponent N j) :
    (termsValues M D a u j part ps v 27).value=
      (v 27).value+(ps.map (contribution M D N a u j part)).sum := by
  induction ps generalizing v with
  | nil => simp [termsValues]
  | cons parity rest ih =>
    rw [termsValues,ih _ (guarded_good M D a u parity j part v good entryValid)
      (by rw [guarded_seed_keep];exact seed),guarded_value M D N a u parity j part v good entryValid seed]
    simp [add_assoc]

theorem parities_sum (f : Corner.Parity→ℚ) : (parities.map f).sum=∑s,f s := by
  rw [parities,List.map_ofFn,List.sum_ofFn]
  exact parityFinEight.symm.sum_comp f

def CacheCorrect (D : ℕ) (a : PartArray.Table (2*(2*D+1)^3)) (c : Alias→RationalComplex) : Prop :=
  ∀i,(a.get i).value=if i.val%2=0 then (c (RootFrequency.frequency (2*D+1) i.val)).1
    else (c (RootFrequency.frequency (2*D+1) i.val)).2

theorem contribution_correct (M D N : ℕ) [NeZero M] (a : PartArray.Table (2*(2*D+1)^3))
    (c : Alias→RationalComplex) (correct : CacheCorrect D a c)
    (u : Fin 3→ℕ) (parity : Corner.Parity) (j : Fin 3) (part : Fin 2) :
    contribution M D N a u j part parity=
      scalarPart (if outputAlias M D u-Supercell.seedAlias M parity∈Product.frequencyCube D then
        rationalComplexMul (c (outputAlias M D u-Supercell.seedAlias M parity))
          (Supercell.seedCoefficient N parity j) else 0) part := by
  by_cases h : inside M D parity u
  · have member := (inside_iff M D parity u).mp h
    rw [contribution,dite_eq_left h,ite_eq_left member]
    rw [correct,index_part,index_frequency M D parity u (cachePart part) h]
    have same : (if (cachePart part).val=0 then
        (c (outputAlias M D u-Supercell.seedAlias M parity)).1 else
        (c (outputAlias M D u-Supercell.seedAlias M parity)).2)=
        scalarPart (c (outputAlias M D u-Supercell.seedAlias M parity)) (cachePart part) := rfl
    rw [same,scalar_contribution]
  · have outside : outputAlias M D u-Supercell.seedAlias M parity∉Product.frequencyCube D :=
      fun hm=>h ((inside_iff M D parity u).mpr hm)
    simp [contribution,h,outside,scalarPart]

theorem scalarPart_sum (f : Corner.Parity→RationalComplex) (part : Fin 2) :
    scalarPart (∑s,f s) part=∑s,scalarPart (f s) part := by
  unfold scalarPart
  split_ifs <;> simp [Prod.fst_sum,Prod.snd_sum]

theorem terms_rootApply (M N : ℕ) [NeZero M] (scale : ℚ) (W ell : ℕ)
    (a : PartArray.Table (2*(2*rootDegree scale W ell+1)^3))
    (correct : CacheCorrect (rootDegree scale W ell) a
      (fun ν=>rectangleRational (computedRootCoefficient scale W ell ν)))
    (entryValid : ∀i,(a.get i).Valid) (u : Fin 3→ℕ) (j : Fin 3) (part : Fin 2)
    (v : ℕ→Parts) (good : Good slots v) (seed : (v (28+j.val)).value=seedComponent N j)
    (zero : (v 27).value=0) :
    (termsValues M (rootDegree scale W ell) a u j part parities v 27).value=
      scalarPart ((FourierData.rootApply scale W ell (Supercell.finiteSeed M N)).field
        (outputAlias M (rootDegree scale W ell) u) j) part := by
  rw [terms_value M (rootDegree scale W ell) N a u parities j part v good entryValid seed,
    zero,zero_add,parities_sum,Supercell.rootApply_sparse,scalarPart_sum]
  apply Finset.sum_congr rfl
  intro parity _
  exact contribution_correct M (rootDegree scale W ell) N a _ correct u parity j part

#print axioms terms_rootApply
end Maxwell.Continuum.Calibration.SeedRoot
