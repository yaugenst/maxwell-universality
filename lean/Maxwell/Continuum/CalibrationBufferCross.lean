import Maxwell.Continuum.CalibrationBufferCrossSetup
import Maxwell.Continuum.CalibrationStoredPairing
import Maxwell.Continuum.CalibrationBufferNorm

/-! Exact signed quadratic-pair numerator from the actual alternating
buffers. All dot-product write widths follow from their stored word width. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferCross

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Word Blank)
open NeumannMachine.StoredPairing (workWidth)
set_option maxHeartbeats 2800000
set_option maxRecDepth 16384

def code : Code := .seq setupCode dotCode
def costBound (n B : ℕ) : ℕ := 2^20*(n+1)*(workWidth n B+2)^2

theorem executes {n B : ℕ} (b : Buffers n) (count : List Bool)
    (hsize : b.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hb : b.Ready count B s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost≤costBound n B ∧
      Word t.val 30 (Pairing.positive (left b) (bufferChannels b)) ∧
      Word t.val 31 (Pairing.negative (left b) (bufferChannels b)) ∧
      CalibrationMatrix.Ready t.val
        (dotValues (Pairing.positive (left b) (bufferChannels b))
          (Pairing.negative (left b) (bufferChannels b))) ∧
      CalibrationMatrix.Stored (data b) t.val ∧ Blank t.val 106 ∧
      BufferNorm.Frame s.val t.val := by
  have hc : B≤workWidth n B := by unfold workWidth;omega
  obtain ⟨vi0,hvi0,hvl0,cal0,stored0,idx0,out0,more0⟩ := hb
  have bounds := represented_width b hsize stored0 out0
  have decode := decodes b
  obtain ⟨u,vi,origin,run0,cal,stored,idx,hvi,hvl,count0,frame0⟩ :=
    setup b count input tape s ⟨vi0,hvi0,hvl0,cal0,stored0,idx0,out0,more0⟩
  obtain ⟨c,t,fi,fj,hcost,run,hfi,hfj,hfil,hfjl,idx1,stored1,cal1,blank,frame⟩ :=
    dot (data b) 0 (workWidth n B) (by omega) (sized b hsize)
      (NeumannMachine.StoredPairing.dimension_lt n B)
      (by simpa only [Pairing.decoded_positive decode] using bounds.1)
      (by simpa only [Pairing.decoded_negative decode] using bounds.2)
      input tape [] vi count rfl hvi (by simp) (hvl.trans hc) hcount origin u count0 cal stored idx
  have final : CalibrationMatrix.Ready t.val
      (dotValues (Pairing.positive (left b) (bufferChannels b))
        (Pairing.negative (left b) (bufferChannels b))) := by
    simpa only [Pairing.decoded_positive decode,Pairing.decoded_negative decode] using cal1
  refine ⟨setupCost b count+c,t,run0.seq run,?_,?_,?_,final,stored1,blank,?_⟩
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
  · simpa [dotValues] using final.1 30 (by omega) (by omega)
  · simpa [dotValues] using final.1 31 (by omega) (by omega)
  · exact ⟨frame.1.trans frame0.1,frame.2.1.trans frame0.2.1,
      frame.2.2.1.trans frame0.2.2.1,frame.2.2.2.1.trans frame0.2.2.2.1,
      fun i hi hacc h102 h103 h106 h110 h111 =>
        (frame.2.2.2.2.1 i hi hacc h102 h103 h106).trans
          (frame0.2.2.2.2 i h106 h110 h111)⟩

#print axioms executes

end Maxwell.Continuum.Calibration.PowerMachine.BufferCross
