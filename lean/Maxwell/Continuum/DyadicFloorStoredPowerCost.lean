import Maxwell.Continuum.DyadicFloorStoredPowerExecution

/-! The stored-scale floor has one fixed program and the same quadratic
bit-operation bound as the exact floor arithmetic it implements. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor.StoredPower
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2000000

theorem compiled_run (S : Finset ℕ) (P target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v) (hx : (v source).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s)
    (hz : Clean s.val) (hp : Word s.val 144 (2^P)) :
    ∃ t : Store, (runPriced ((code target source).compile.next input tape)
      (2^140*(P+W+4)^2+1) s.val).finished=some (t.place (code target source).size) ∧
      (runPriced ((code target source).compile.next input tape)
      (2^140*(P+W+4)^2+1) s.val).instructions≤2^140*(P+W+4)^2 ∧
      Ready S (Function.update v target (result P (v source))) t ∧ Clean t.val ∧
      Word t.val 144 (2^P) ∧ BinaryPrecision.Frame (workspace S) s.val t.val ∧
      (result P (v source)).value=((roundDyadic P (v source).value).numerator:ℚ) := by
  obtain ⟨cost,t,he,hc,hr,hz',hp',hf⟩ := executes S P target source ht hs' v W hw hx
    input tape s hs hz hp
  have hcost := hc.trans (DyadicFloor.costBound_polynomial P W)
  have hout := he.compiled_run (2^140*(P+W+4)^2+1) (by omega)
  exact ⟨t,hout.1,hout.2 ▸ hcost,hr,hz',hp',hf,result_value P (v source) hx⟩

#print axioms compiled_run
end Maxwell.Continuum.RationalDataflow.DyadicFloor.StoredPower
