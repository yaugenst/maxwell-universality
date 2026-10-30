import Maxwell.Continuum.CalibrationBufferNormSetup
import Maxwell.Continuum.CalibrationStoredPairing

/-! A fixed program computes the exact squared norm of the actual current
matrix-power buffer, including the case where its descriptors have swapped. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Word Blank)
open NeumannMachine.StoredPairing (workWidth)
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

def code : Code := .seq setupCode dotCode
def costBound (n B : ℕ) : ℕ := 2^20*(n+1)*(workWidth n B+2)^2
def Frame (s t : BitRAMState) : Prop :=
  t.memory=s.memory ∧ t.inputHead=s.inputHead ∧ t.randomCursor=s.randomCursor ∧
    t.output=s.output ∧ ∀ i, (i=4 ∨ 10 ≤ i) → (i < 30 ∨ 36 < i) →
      i≠102 → i≠103 → i≠106 → i≠110 → i≠111 → t.tapes i=s.tapes i

theorem executes {n B : ℕ} (b : Buffers n) (count : List Bool)
    (hsize : b.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hb : b.Ready count B s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost≤costBound n B ∧
      CalibrationMatrix.Ready t.val
        (dotValues (Pairing.positive (bufferChannels b) (bufferChannels b))
          (Pairing.negative (bufferChannels b) (bufferChannels b))) ∧
      CalibrationMatrix.Stored (data b) t.val ∧ Blank t.val 106 ∧
      Frame s.val t.val := by
  have hc : B≤workWidth n B := by unfold workWidth; omega
  obtain ⟨vi0,hvi0,hvl0,cal0,stored0,idx0,more0⟩ := hb
  have bounds := represented_width b hsize stored0
  have decode := decodes b
  obtain ⟨u,vi,origin,run0,cal,stored,idx,hvi,hvl,count0,frame0⟩ :=
    setup b count input tape s ⟨vi0,hvi0,hvl0,cal0,stored0,idx0,more0⟩
  obtain ⟨c,t,fi,fj,hcost,run,hfi,hfj,hfil,hfjl,idx1,stored1,cal1,blank,frame⟩ :=
    dot (data b) 0 (workWidth n B) (by omega) (sized b hsize)
      (NeumannMachine.StoredPairing.dimension_lt n B)
      (by simpa only [Pairing.decoded_positive decode] using bounds.1)
      (by simpa only [Pairing.decoded_negative decode] using bounds.2)
      input tape [] vi count rfl hvi (by simp) (hvl.trans hc) hcount origin u count0
        cal stored idx
  refine ⟨setupCost b count+c,t,run0.seq run,?_,?_,stored1,blank,?_⟩
  · have hsetup := setupCost_le b count hsize hcl
    have hdot : c≤Pairing.costCap n (workWidth n B) := by
      apply hcost.trans
      dsimp [dotCost,Pairing.costCap]
      have hcl' := hcl.trans hc
      nlinarith only [Nat.mul_le_mul_left (n+1) (Nat.mul_le_mul_left 13 hcl'),
        Nat.mul_le_mul_left 6 hcl',Nat.zero_le (500*(3*workWidth n B+4))]
    have bound := Pairing.costCap_le n (workWidth n B)
    have hb' : 57*B+59≤100*(workWidth n B+2)^2 := by nlinarith
    have hn : 100*(workWidth n B+2)^2≤100*(n+1)*(workWidth n B+2)^2 := by
      nlinarith only [Nat.zero_le (100*n*(workWidth n B+2)^2)]
    unfold costBound
    nlinarith only [hsetup,hdot,bound,hb',hn,Nat.zero_le ((n+1)*(workWidth n B+2)^2)]
  · simpa only [Pairing.decoded_positive decode,Pairing.decoded_negative decode] using cal1
  · exact ⟨frame.1.trans frame0.1,frame.2.1.trans frame0.2.1,
      frame.2.2.1.trans frame0.2.2.1,frame.2.2.2.1.trans frame0.2.2.2.1,
      fun i hi hacc h102 h103 h106 h110 h111 =>
        (frame.2.2.2.2.1 i hi hacc h102 h103 h106).trans
          (frame0.2.2.2.2 i h106 h110 h111)⟩

theorem compiled_run {n B : ℕ} (b : Buffers n) (count : List Bool)
    (hsize : b.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hb : b.Ready count B s.val) :
    ∃ t : Store, (runPriced (code.compile.next input tape) (costBound n B+1) s.val).finished=
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costBound n B+1) s.val).instructions≤
        costBound n B ∧
      CalibrationMatrix.Ready t.val
        (dotValues (Pairing.positive (bufferChannels b) (bufferChannels b))
          (Pairing.negative (bufferChannels b) (bufferChannels b))) ∧
      CalibrationMatrix.Stored (data b) t.val ∧ Blank t.val 106 ∧
      Frame s.val t.val := by
  obtain ⟨cost,t,run,hcost,out⟩ := executes b count hsize hcount hcl input tape s hb
  have hr := run.compiled_run (costBound n B+1) (by omega)
  exact ⟨t,hr.1,hr.2 ▸ hcost,out⟩

#print axioms executes
#print axioms compiled_run

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm
