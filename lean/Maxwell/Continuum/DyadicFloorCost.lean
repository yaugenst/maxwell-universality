import Maxwell.Continuum.DyadicFloorExecution

/-! Polynomial cost and exact compiled output of floor dyadic rounding. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem costBound_polynomial (P W : ℕ) : costBound P W≤2^140*(P+W+4)^2 := by
  have hwork : workWidth P W+2≤2^13*(P+W+4) := by unfold workWidth;omega
  have hsquare := Nat.pow_le_pow_left hwork 2
  have hsmall : (P+W+1+2)^2≤(P+W+4)^2 := Nat.pow_le_pow_left (by omega) 2
  have hlinear : P+W+4≤(P+W+4)^2 := Nat.le_self_pow (by decide) _
  have h1 : 1≤(P+W+4)^2 := one_le_pow₀ (by omega)
  unfold costBound stageCost
  nlinarith only [hsquare,hsmall,hlinear,h1]

theorem compiled_run (S : Finset ℕ) (P target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v) (hx : (v source).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) (hz : Clean s.val) :
    ∃ t, (runPriced ((code P target source).compile.next input tape)
      (2^140*(P+W+4)^2+1) s.val).finished=some (t.place (code P target source).size) ∧
      (runPriced ((code P target source).compile.next input tape)
      (2^140*(P+W+4)^2+1) s.val).instructions≤2^140*(P+W+4)^2 ∧
      Ready S (Function.update v target (result P (v source))) t ∧ Clean t.val ∧
      BinaryPrecision.Frame (workspace S) s.val t.val ∧
      (result P (v source)).value=((roundDyadic P (v source).value).numerator:ℚ) := by
  obtain ⟨cost,t,he,hc,hr,hz',hf⟩ := executes S P target source ht hs' v W hw hx input tape s hs hz
  have hcost := hc.trans (costBound_polynomial P W)
  have hout := he.compiled_run (2^140*(P+W+4)^2+1) (by omega)
  exact ⟨t,hout.1,hout.2 ▸ hcost,hr,hz',hf,result_value P (v source) hx⟩

#print axioms costBound_polynomial
#print axioms compiled_run
end Maxwell.Continuum.RationalDataflow.DyadicFloor
