import Maxwell.Continuum.CalibrationStoredPairingSetup

/-! A uniform program computes the exact signed scalar pairing from the
final stored calibration arrays. No dot-product values or width traces
are supplied as inputs. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.StoredPairing

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Word Blank)
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

def code (p q : Fin 12) : Code := .seq (setupCode p q) dotCode

def costBound (n B : ℕ) : ℕ := 2^20*(n+1)*(workWidth n B+2)^2

def Frame (s t : BitRAMState) : Prop :=
  t.memory=s.memory ∧ t.inputHead=s.inputHead ∧ t.randomCursor=s.randomCursor ∧
    t.output=s.output ∧ ∀ i, 10 ≤ i → (i < 30 ∨ 36 < i) →
      i≠102 → i≠103 → i≠106 → i≠110 → i≠111 → t.tapes i=s.tapes i

theorem executes {n B : ℕ} (a : Snapshot n) (p q : Fin 12) (count : List Bool)
    (hsize : a.data.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (ha : a.Ready count B s.val) :
    ∃ cost t, Executes input tape (code p q) cost s t ∧ cost≤costBound n B ∧
      CalibrationMatrix.Ready t.val
        (dotValues (Pairing.positive (left a p q) (right a))
          (Pairing.negative (left a p q) (right a))) ∧
      CalibrationMatrix.Stored (data a p q) t.val ∧ Blank t.val 106 ∧
      Frame s.val t.val := by
  have hc : B≤workWidth n B := by unfold workWidth; omega
  have bounds := represented_width a p q hsize ha.2.1
  have decode := decodes a p q
  obtain ⟨u,vi,origin,run0,cal0,stored0,idx0,hvi,hvl,count0,frame0⟩ :=
    setup a p q count input tape s ha
  obtain ⟨c,t,fi,fj,hcost,run,hfi,hfj,hfil,hfjl,idx,stored,cal,blank,frame⟩ :=
    dot (data a p q) 0 (workWidth n B) (by omega) (sized a p q hsize)
      (dimension_lt n B) (by simpa only [Pairing.decoded_positive decode] using bounds.1)
      (by simpa only [Pairing.decoded_negative decode] using bounds.2)
      input tape [] vi count rfl hvi (by simp) (hvl.trans hc) hcount origin u count0
        cal0 stored0 idx0
  refine ⟨setupCost a p q count+c,t,run0.seq run,?_,?_,stored,blank,?_⟩
  · have hsetup := setupCost_le a p q count hsize hcl
    have hdot : c≤Pairing.costCap n (workWidth n B) := by
      apply hcost.trans
      dsimp [dotCost,Pairing.costCap]
      have hcl' := hcl.trans hc
      nlinarith only [Nat.mul_le_mul_left (n+1) (Nat.mul_le_mul_left 13 hcl'),
        Nat.mul_le_mul_left 6 hcl',Nat.zero_le (500*(3*workWidth n B+4))]
    have bound := Pairing.costCap_le n (workWidth n B)
    have hb : 57*B+59≤100*(workWidth n B+2)^2 := by nlinarith
    have hn : 100*(workWidth n B+2)^2≤100*(n+1)*(workWidth n B+2)^2 := by
      nlinarith only [Nat.zero_le (100*n*(workWidth n B+2)^2)]
    unfold costBound
    nlinarith only [hsetup,hdot,bound,hb,hn,Nat.zero_le ((n+1)*(workWidth n B+2)^2)]
  · simpa only [Pairing.decoded_positive decode,Pairing.decoded_negative decode] using cal
  · exact ⟨frame.1.trans frame0.1,frame.2.1.trans frame0.2.1,
      frame.2.2.1.trans frame0.2.2.1,frame.2.2.2.1.trans frame0.2.2.2.1,
      fun i hi hacc h102 h103 h106 h110 h111 =>
        (frame.2.2.2.2.1 i (Or.inr hi) hacc h102 h103 h106).trans
          (frame0.2.2.2.2 i h106 h110 h111)⟩

theorem compiled_run {n B : ℕ} (a : Snapshot n) (p q : Fin 12) (count : List Bool)
    (hsize : a.data.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (ha : a.Ready count B s.val) :
    ∃ t : Store, (runPriced ((code p q).compile.next input tape) (costBound n B+1) s.val).finished=
        some (t.place (code p q).size) ∧
      (runPriced ((code p q).compile.next input tape) (costBound n B+1) s.val).instructions≤
        costBound n B ∧
      CalibrationMatrix.Ready t.val
        (dotValues (Pairing.positive (left a p q) (right a))
          (Pairing.negative (left a p q) (right a))) ∧
      CalibrationMatrix.Stored (data a p q) t.val ∧ Blank t.val 106 ∧ Frame s.val t.val := by
  obtain ⟨cost,t,run,hcost,out⟩ := executes a p q count hsize hcount hcl input tape s ha
  have hr := run.compiled_run (costBound n B+1) (by omega)
  exact ⟨t,hr.1,hr.2 ▸ hcost,out⟩

theorem norm_executes {n B : ℕ} (a : Snapshot n) (count : List Bool)
    (hsize : a.data.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (ha : a.Ready count B s.val) :
    ∃ cost t, Executes input tape (code 10 11) cost s t ∧ cost≤costBound n B ∧
      Word t.val 30 (Pairing.positive (right a) (right a)) ∧
      Word t.val 31 (Pairing.negative (right a) (right a)) ∧
      ((Pairing.positive (right a) (right a):ℤ)-Pairing.negative (right a) (right a)=
        ∑ i, ((right a).value i)^2) ∧
      CalibrationMatrix.Ready t.val
        (dotValues (Pairing.positive (right a) (right a))
          (Pairing.negative (right a) (right a))) ∧
      CalibrationMatrix.Stored (data a 10 11) t.val ∧ Frame s.val t.val := by
  obtain ⟨cost,t,run,hcost,cal,stored,_,frame⟩ :=
    executes a 10 11 count hsize hcount hcl input tape s ha
  exact ⟨cost,t,run,hcost,by simpa [dotValues,left,right] using cal.1 30 (by omega) (by omega),
    by simpa [dotValues,left,right] using cal.1 31 (by omega) (by omega),
    norm_value a,cal,stored,frame⟩

#print axioms executes
#print axioms norm_executes

end Maxwell.Continuum.Calibration.NeumannMachine.StoredPairing
