import Maxwell.Cost.CalibrationMatrix.Horner.PairingSetup

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
open RationalAccumulator (Blank Word)
set_option maxHeartbeats 1200000

def pairingCode : Code := .seq pairingSetupCode (Pairing.code 142)
def pairingCost (n B : ℕ) : ℕ := 100*B+110+Pairing.costCap n B

def PairingFrame (s t : BitRAMState) : Prop :=
  t.memory = s.memory ∧ t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧
  (∀ i, 141 ≤ i → t.tapes i = s.tapes i)

theorem pairingCost_le (n B : ℕ) : pairingCost n B ≤ 550000*(n+1)*(B+2)^2 := by
  have h := Pairing.costCap_le n B
  have hb : 100*B+110 ≤ 200*(B+2)^2 := by nlinarith
  dsimp [pairingCost]
  nlinarith only [h,hb,Nat.zero_le ((30000*n+29800)*(B+2)^2)]

/-- Exact rational emission from the final inverse arrays includes actual
replacement of all four descriptors and physical loop-count initialization. -/
theorem pairing_emit {n : ℕ} (r : PairingRow n) (d : Scale.Data n)
    (words : Fin 4 → Vector (List Bool) n) (old : PairingOld) (count : List Bool)
    (B den : ℕ) (hd : d.Sized B) (hn : n < 2^B)
    (hrp : r.positiveBase.length ≤ B) (hrn : r.negativeBase.length ≤ B)
    (hmp : old.mp.length ≤ B) (hmn : old.mn.length ≤ B)
    (hvp : old.vp.length ≤ B) (hvn : old.vn.length ≤ B)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (hden : 0 < den) (hdenBits : den.bits.length ≤ B)
    (hp : (Pairing.positive r.channels (Scale.channels words 2 3)).bits.length ≤ B)
    (hneg : (Pairing.negative r.channels (Scale.channels words 2 3)).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : WorkReady count B s.val) (hdata : Scale.Stored d words s.val)
    (hr : r.Stored (addressValue d.width) s.val) (ho : old.Stored s.val) (h142 : Word s.val 142 den) :
    ∃ cost, ∃ t : Store, cost ≤ pairingCost n B ∧ Executes input tape pairingCode cost s t ∧
      t.val.output = (Pairing.output (Pairing.positive r.channels (Scale.channels words 2 3))
        (Pairing.negative r.channels (Scale.channels words 2 3)) den hden).encode.reverse ++ s.val.output ∧
      CalibrationMatrix.Ready t.val (dotValues (Pairing.positive r.channels (Scale.channels words 2 3))
        (Pairing.negative r.channels (Scale.channels words 2 3))) ∧
      CalibrationMatrix.Stored (pairingData r d words) t.val ∧ Blank t.val 106 ∧ PairingFrame s.val t.val := by
  obtain ⟨a,vi,origin,ea,har,had,hai,hvi,hvl,h106,fa⟩ := pairing_setup r d words old count B
    input tape s hw hdata hr ho
  have hsize : (pairingData r d words).Sized B :=
    ⟨hd.1,hd.2.1,hrp,hrn,hd.2.2.1 2,hd.2.2.1 3⟩
  obtain ⟨cost,t,hcost,et,hto,htr,htd,ht106,ft⟩ := Pairing.executes (pairingData r d words)
    r.channels (Scale.channels words 2 3) (pairingData_decodes r d words) 142 B den (by omega)
    hden hsize hn hp hneg hdenBits input tape [] vi count rfl hvi (by simp) hvl hcount hcl origin a
    h106 har had hai (RationalAccumulator.word_of_eq (fa.2.2.2.2 142 (by omega) (by omega)
      (by omega) (by omega) (by omega)) h142)
  refine ⟨pairingSetupCost r d old count+cost,t,?_,ea.seq et,?_,htr,htd,ht106,
    ft.1.trans fa.1,ft.2.1.trans fa.2.1,ft.2.2.1.trans fa.2.2.1,
    fun i hi => (ft.2.2.2 i (by omega) (by omega) (by omega) (by omega)).trans
      (fa.2.2.2.2 i (by omega) (by omega) (by omega) (by omega) (by omega))⟩
  · have hh := pairingSetupCost_le r d old count B hd hrp hrn hmp hmn hvp hvn hcl
    dsimp [pairingCost]
    omega
  · rw [hto,fa.2.2.2.1]

theorem pairing_compiled_run {n : ℕ} (r : PairingRow n) (d : Scale.Data n)
    (words : Fin 4 → Vector (List Bool) n) (old : PairingOld) (count : List Bool)
    (B den : ℕ) (hd : d.Sized B) (hn : n < 2^B)
    (hrp : r.positiveBase.length ≤ B) (hrn : r.negativeBase.length ≤ B)
    (hmp : old.mp.length ≤ B) (hmn : old.mn.length ≤ B)
    (hvp : old.vp.length ≤ B) (hvn : old.vn.length ≤ B)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (hden : 0 < den) (hdenBits : den.bits.length ≤ B)
    (hp : (Pairing.positive r.channels (Scale.channels words 2 3)).bits.length ≤ B)
    (hneg : (Pairing.negative r.channels (Scale.channels words 2 3)).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : WorkReady count B s.val) (hdata : Scale.Stored d words s.val)
    (hr : r.Stored (addressValue d.width) s.val) (ho : old.Stored s.val) (h142 : Word s.val 142 den) :
    ∃ t : Store,
      (runPriced (pairingCode.compile.next input tape) (pairingCost n B+1) s.val).finished = some (t.place pairingCode.size) ∧
      (runPriced (pairingCode.compile.next input tape) (pairingCost n B+1) s.val).instructions ≤ 550000*(n+1)*(B+2)^2 ∧
      t.val.output = (Pairing.output (Pairing.positive r.channels (Scale.channels words 2 3))
        (Pairing.negative r.channels (Scale.channels words 2 3)) den hden).encode.reverse ++ s.val.output ∧
      CalibrationMatrix.Ready t.val (dotValues (Pairing.positive r.channels (Scale.channels words 2 3))
        (Pairing.negative r.channels (Scale.channels words 2 3))) ∧
      CalibrationMatrix.Stored (pairingData r d words) t.val ∧ Blank t.val 106 ∧ PairingFrame s.val t.val := by
  obtain ⟨cost,t,hc,he,ht⟩ := pairing_emit r d words old count B den hd hn hrp hrn hmp hmn hvp hvn
    hcount hcl hden hdenBits hp hneg input tape s hw hdata hr ho h142
  have hr := he.compiled_run (pairingCost n B+1) (by omega)
  exact ⟨t,hr.1,hr.2 ▸ hc.trans (pairingCost_le n B),ht⟩

end Maxwell.Cost.CalibrationMatrix.Horner
