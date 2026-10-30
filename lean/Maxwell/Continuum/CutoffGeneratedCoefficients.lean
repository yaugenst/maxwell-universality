import Maxwell.Continuum.CutoffMonomialCache
import Maxwell.Continuum.CutoffAntiderivativePreparation

/-! The executed cache and conversion depend only on the values of the
generated profile coefficients. Their unreduced channels need not equal the
canonical dyadic representation. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Profile
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem monomialState_generated_value (N : ℕ) (a : ℕ→Parts)
    (ha : ∀k<profileDegree N,(a k).Valid)
    (hc : ∀k<profileDegree N,(a k).value=(coefficient N k).value)
    (i : Fin (profileDegree N)) :
    ((monomialState (profileDegree N) a (profileDegree N)).total.get i).value=
      (monomialCoefficient N i).value := by
  rw [monomialState_total_value _ _ _ ha,monomialCoefficient_value]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hc k (Finset.mem_range.mp hk),coefficient_value]

theorem MonomialStored.generated_total {N W : ℕ}
    {a : Table (4*(profileDegree N+1))} {coeff : ℕ→Parts}
    (hs : MonomialStored a (monomialState (profileDegree N) coeff (profileDegree N)))
    (hw : ∀k<profileDegree N,(coeff k).Width W)
    (hv : ∀k<profileDegree N,(coeff k).Valid)
    (hc : ∀k<profileDegree N,(coeff k).value=(coefficient N k).value)
    (i : Fin (profileDegree N)) :
    (a.getD (4*i.val+6)).Width (profileDegree N*(W+2*profileDegree N+3)+1) ∧
    (a.getD (4*i.val+6)).Valid ∧
    (a.getD (4*i.val+6)).value=(monomialCoefficient N i).value := by
  rw [(hs.2 i).2.2]
  exact ⟨monomialState_total_width _ W coeff hw _ le_rfl i,
    monomialState_total_valid _ coeff _ hv i,monomialState_generated_value N coeff hv hc i⟩

theorem MonomialStored.generated_antiderivative {N W : ℕ}
    {a : Table (4*(profileDegree N+1))} {coeff : ℕ→Parts}
    (hs : MonomialStored a (monomialState (profileDegree N) coeff (profileDegree N)))
    (hw : ∀k<profileDegree N,(coeff k).Width W)
    (hv : ∀k<profileDegree N,(coeff k).Valid)
    (hc : ∀k<profileDegree N,(coeff k).value=(coefficient N k).value)
    (b : Table (profileDegree N))
    (hslot : scaleStateWidth (profileDegree N)
      (profileDegree N*(W+2*profileDegree N+3)+1)≤addressValue b.width)
    (i : Fin (profileDegree N)) :
    ((b.filled (monomialAntiderivativeValues a) 0).get i).Width
      (scaleStateWidth (profileDegree N) (profileDegree N*(W+2*profileDegree N+3)+1)) ∧
    ((b.filled (monomialAntiderivativeValues a) 0).get i).Valid ∧
    ((b.filled (monomialAntiderivativeValues a) 0).get i).value=(antiderivativeCoefficient N i).value := by
  have ht := hs.generated_total hw hv hc
  have hout := monomialAntiderivative_output a b _ (fun i => (ht i).1)
    (fun i => (ht i).2.1) hslot i
  refine ⟨hout.1,hout.2.1,?_⟩
  rw [hout.2.2]
  exact monomialAntiderivativeValues_value N a (fun i => (ht i).2.2) i

#print axioms MonomialStored.generated_antiderivative
end Maxwell.Continuum.Calibration.RawCutoff
