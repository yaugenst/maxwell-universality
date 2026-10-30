import Maxwell.Continuum.CalibrationBufferQuadratic

/-! One fixed program applies a stored rational matrix once and computes
its exact quadratic form using the original vector retained by that step. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.Quadratic

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow NeumannMachine
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ :=
  ∑ i, x i*(A.mulVec x) i
def code : Code := .seq initializedCode BufferCross.quadraticCode
def costBound (n width heap D B : ℕ) : ℕ := initializedCost n width heap D 1 B+
  BufferCross.quadraticCost n (initializedWidth n width heap D 1 B)

theorem executes {n : ℕ} (coeff : CoefficientIndex n → Parts)
    (hvalid : ∀ i, (coeff i).Valid) (W : ℕ) (hwidth : ∀ i, (coeff i).Width W)
    (a b : PartArray.Table (tableSize n)) (heap B : ℕ)
    (hw : 0<addressValue a.width) (hB : 0<B) (hl : TableLayout a b heap)
    (haValues : ∀ i, a.get i=SharedTable.integerParts (paddedCoefficients coeff) i)
    (hbValues : ∀ i, b.get i=a.get i)
    (hslot : rawPowerWidth n W 1≤addressValue a.width)
    (v : ℕ → ℕ) (hi : Descriptors.Inputs v n (addressValue a.width) heap (SharedTable.denominator coeff) 1)
    (hbits : ∀ i∈Descriptors.ids, (v i).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank Descriptors.ids v s.val) (ha : a.Ready s) (hb : b.OutputReady s)
    (h101 : RationalAccumulator.Blank s.val 101) (h576 : RationalAccumulator.Blank s.val 576) :
    ∃ (cost : ℕ) (t : Store) (q : Parts), Executes input tape code cost s t ∧
      cost≤costBound n (addressValue a.width) heap (SharedTable.denominator coeff) B ∧
      RationalAccumulator.Word t.val 30 q.positive ∧ RationalAccumulator.Word t.val 31 q.negative ∧
      RationalAccumulator.Word t.val 576 q.denominator ∧ q.Valid ∧
      q.Width (NeumannMachine.StoredPairing.workWidth n
        (initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) 1 B)+
        3*initializedWidth n (addressValue a.width) heap (SharedTable.denominator coeff) 1 B) ∧
      q.value=form (fun i j => (coeff (.inr (i,j))).value) (fun i => (coeff (.inl i)).value) := by
  obtain ⟨c0,u,out,e0,hc0,ready,size,den,_,_,previous,_,value⟩ := initialized_executes coeff hvalid W hwidth
    a b heap 1 B hw hB hl haValues hbValues hslot v hi hbits input tape s hbank ha hb h101
  let D := SharedTable.denominator coeff
  let C := initializedWidth n (addressValue a.width) heap D 1 B
  have countWidth : n.bits.length≤C := by
    dsimp [C,initializedWidth,setupWidth]
    omega
  have denWidth : D.bits.length≤C := by
    dsimp [C,initializedWidth,setupWidth]
    omega
  have fresh : RationalAccumulator.Blank u.val 576 := RationalAccumulator.blank_of_eq
    (e0.protectsTape 576 (by decide)) h576
  obtain ⟨c1,t,e1,hc1,wp,wm,wd,valid,width,_⟩ := BufferCross.quadratic_executes out D n.bits size
    (addressValue_bits n) countWidth denWidth (SharedTable.denominator_pos coeff hvalid)
    input tape u ready den fresh
  refine ⟨c0+c1,t,BufferCross.quadraticParts out D,e0.seq e1,Nat.add_le_add hc0 hc1,
    wp,wm,wd,valid,width,?_⟩
  rw [BufferCross.quadraticParts_value]
  unfold form
  apply Finset.sum_congr rfl
  intro i _
  have old : (BufferCross.left out).value i=(rawSource coeff).value i := by
    simpa only [Nat.sub_self,matrixPower,BufferCross.left,Channels.value] using previous (by decide) i
  have source : ((BufferCross.left out).value i:ℚ)/(D:ℚ)=(coeff (.inl i)).value := by
    rw [old]
    exact SharedTable.integerValue_sound coeff hvalid (.inl i)
  rw [source]
  have current : ((bufferChannels out).value i:ℚ)/(D:ℚ)^2=
      (Matrix.mulVec (fun i j => (coeff (.inr (i,j))).value) (fun i => (coeff (.inl i)).value)) i := by
    simpa only [rationalPower] using value i
  rw [current]

#print axioms executes

end Maxwell.Continuum.Calibration.PowerMachine.Quadratic
