import Maxwell.Continuum.CutoffAntiderivativeMapWidths

/-! Executed antiderivative-table conversion, with all recurrence and inverse
width premises proved from the stored input words. Initial scalar setup and
construction of the monomial table are separate charged stages. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
attribute [local irreducible] Profile.profileDegree scaleInitial antiderivativeScaleControl
  iterate mapValues

def antiderivativeMapCost (n W wordLength : ℕ) : ℕ :=
  (n+1)*(13*wordLength+15)+n*mapStepCost antiderivativeScaleControl (scaleWorkingWidth n W)

theorem antiderivativeMap_computes (N : ℕ) (a b : Table (Profile.profileDegree N))
    (hcoeff : ∀ i, (a.get i).value=(monomialCoefficient N i).value)
    (W : ℕ) (hwidth : ∀ i, (a.get i).Width W) (hvalid : ∀ i, (a.get i).Valid)
    (haMeta : a.MetadataWidth (scaleWorkingWidth (Profile.profileDegree N) W))
    (hbMeta : b.MetadataWidth (scaleWorkingWidth (Profile.profileDegree N) W))
    (hslot : scaleWorkingWidth (Profile.profileDegree N) W≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤scaleWorkingWidth (Profile.profileDegree N) W)
    (s : Store) (hn : addressValue xs=Profile.profileDegree N)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : SharedConversion.Ready scaleSlots (scaleInitial (Profile.profileDegree N)) s)
    (ha : a.Ready s) (hb : b.OutputReady s) :
    ∃ t,
      (runPriced ((mapCode antiderivativeScaleControl 0).compile.next input tape)
        (antiderivativeMapCost (Profile.profileDegree N) W xs.length+1) s.val).finished=
          some (t.place (mapCode antiderivativeScaleControl 0).size) ∧
      (runPriced ((mapCode antiderivativeScaleControl 0).compile.next input tape)
        (antiderivativeMapCost (Profile.profileDegree N) W xs.length+1) s.val).instructions≤
          antiderivativeMapCost (Profile.profileDegree N) W xs.length ∧
      a.Ready t ∧
      (b.filled (mapValues a antiderivativeScaleControl 0 (scaleInitial (Profile.profileDegree N))) 0).OutputReady t ∧
      (∀ i, ((b.filled (mapValues a antiderivativeScaleControl 0
        (scaleInitial (Profile.profileDegree N))) 0).get i).value=(antiderivativeCoefficient N i).value) := by
  have hSB : scaleStateWidth (Profile.profileDegree N) W≤scaleWorkingWidth (Profile.profileDegree N) W := by
    unfold scaleWorkingWidth
    omega
  obtain ⟨cost,t,_,he,hcost,_,harray,houtput,_,_⟩ := map_executes a b scaleSlots (by decide)
    antiderivativeScaleControl antiderivativeScaleControl_valid 0 (by decide) (scaleInitial _)
    (scaleWorkingWidth (Profile.profileDegree N) W) (by
      unfold scaleWorkingWidth
      exact Nat.mul_pos (by decide) (Nat.succ_pos _))
    haMeta hbMeta hslot hsep hdisjoint
    (fun k hk => (scale_iterate_width a W hwidth k hk.le).mono hSB)
    (scale_loaded_widthTrace a W hwidth) (scale_loaded_good a hvalid) (scale_loaded_admissible a)
    input tape xs origin hlen s hn hcount hs ha hb
  obtain ⟨hrun,hsteps⟩ := he.compiled_run
    (antiderivativeMapCost (Profile.profileDegree N) W xs.length+1) (by
      unfold antiderivativeMapCost
      omega)
  refine ⟨t,hrun,hsteps ▸ hcost,harray,houtput,?_⟩
  intro i
  have fit (j : Fin (Profile.profileDegree N)) :
      (mapValues a antiderivativeScaleControl 0 (scaleInitial (Profile.profileDegree N)) j).Width
        (addressValue b.width) := by
    unfold mapValues
    apply ((scale_iterate_width a W hwidth (Profile.profileDegree N-j.val) (Nat.sub_le _ _))
      0 (by decide)).mono (hSB.trans hslot)
  rw [Table.filled_get b _ fit]
  exact scale_map_value N a hcoeff i

theorem antiderivativeMapCost_polynomial (n W wordLength : ℕ)
    (hlen : wordLength≤scaleWorkingWidth n W) :
    antiderivativeMapCost n W wordLength≤2^130*(n+1)^3*(W+2)^2 := by
  let B := scaleWorkingWidth n W
  have hB : B≤2^11*(n+1)*(W+2) := by
    dsimp [B,scaleWorkingWidth,scaleStateWidth]
    nlinarith
  have hp : 1≤(n+1)*(W+2) := Nat.succ_le_of_lt (by positivity)
  have hB5 : B+5≤2^12*(n+1)*(W+2) := by nlinarith
  have hb : 1≤(B+5)^2 := one_le_pow₀ (by omega)
  have hC : mapStepCost antiderivativeScaleControl B≤2^104*(B+5)^2 := by
    unfold mapStepCost operationCost
    rw [antiderivativeScaleControl_steps]
    have hm := Nat.pow_le_pow_left (by omega : B+3≤B+5) 2
    nlinarith
  have hcounter : (n+1)*(13*wordLength+15)≤32*(n+1)*(B+5)^2 := by
    have hlen' : wordLength≤B := hlen
    have hs : B+1≤(B+5)^2 := by nlinarith
    nlinarith only [hlen',hs]
  have hcost : antiderivativeMapCost n W wordLength≤2^105*(n+1)*(B+5)^2 := by
    unfold antiderivativeMapCost
    have hm := Nat.mul_le_mul_left n hC
    nlinarith only [hm,hcounter,Nat.zero_le ((B+5)^2)]
  have hm := Nat.mul_le_mul_left (2^105*(n+1)) (Nat.pow_le_pow_left hB5 2)
  calc
    _ ≤ 2^105*(n+1)*(B+5)^2 := hcost
    _ ≤ 2^105*(n+1)*(2^12*(n+1)*(W+2))^2 := hm
    _ ≤ 2^130*(n+1)^3*(W+2)^2 := by ring_nf; omega

#print axioms antiderivativeMap_computes
#print axioms antiderivativeMapCost_polynomial
end Maxwell.Continuum.Calibration.RawCutoff
