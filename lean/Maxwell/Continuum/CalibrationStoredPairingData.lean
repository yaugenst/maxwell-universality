import Maxwell.Continuum.CalibrationNeumannStep
import Maxwell.Cost.CalibrationMatrix.Horner.Semantics
import Maxwell.Cost.CalibrationMatrix.Pairing

/-! Literal signed pairings of stored calibration vectors. The word bound
comes from the represented memory, including both unreduced sign channels. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.StoredPairing

open Maxwell.Cost Maxwell.Cost.CalibrationMatrix
open scoped BigOperators
set_option maxHeartbeats 1800000

def data {n : ℕ} (a : Snapshot n) (p q : Fin 12) : CalibrationMatrix.Data n n :=
  ⟨a.data.width,a.data.clock,a.data.bases p,a.data.bases q,a.data.bases 10,
    a.data.bases 11,a.words p,a.words q,a.words 10,a.words 11,
    a.data.width_nonempty,a.data.clock_length⟩

def left {n : ℕ} (a : Snapshot n) (p q : Fin 12) : Channels n :=
  Horner.channels a.words p q

def right {n : ℕ} (a : Snapshot n) : Channels n := Horner.channels a.words 10 11

theorem decodes {n : ℕ} (a : Snapshot n) (p q : Fin 12) :
    Pairing.Decodes (data a p q) (left a p q) (right a) :=
  ⟨fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

def workWidth (n B : ℕ) : ℕ := 2*B+n+4

theorem sized {n B : ℕ} (a : Snapshot n) (p q : Fin 12) (h : a.data.Sized B) :
    (data a p q).Sized (workWidth n B) := by
  obtain ⟨hw,hv,_,_,hb,_,_⟩ := h
  have hp := hb p
  have hq := hb q
  have hr := hb 10
  have hs := hb 11
  exact ⟨by dsimp [data,workWidth]; omega,by dsimp [data,workWidth]; omega,
    by dsimp [data,workWidth]; omega,by dsimp [data,workWidth]; omega,
    by dsimp [data,workWidth]; omega,by dsimp [data,workWidth]; omega⟩

theorem pair_width {n B : ℕ} (x y : Channels n)
    (hx : ∀ i, x.positive i≤2^B ∧ x.negative i≤2^B)
    (hy : ∀ i, y.positive i≤2^B ∧ y.negative i≤2^B) :
    (Pairing.positive x y).bits.length≤workWidth n B ∧
      (Pairing.negative x y).bits.length≤workWidth n B := by
  have term (a b c d : ℕ) (ha : a≤2^B) (hb : b≤2^B) (hc : c≤2^B)
      (hd : d≤2^B) : a*b+c*d≤2^(2*B+1) := by
    calc
      _ ≤ 2^B*2^B+2^B*2^B := Nat.add_le_add (Nat.mul_le_mul ha hb) (Nat.mul_le_mul hc hd)
      _ = _ := by rw [show 2*B+1=(B+B)+1 by omega,pow_succ,pow_add]; omega
  have bound (v : Fin n → ℕ) (hv : ∀ i, v i≤2^(2*B+1)) :
      (∑ i, v i).bits.length≤workWidth n B := by
    have hs : (∑ i, v i)≤n*2^(2*B+1) := by
      calc
        _ ≤ ∑ _i : Fin n, 2^(2*B+1) := Finset.sum_le_sum (fun i _ => hv i)
        _ = _ := by simp
    have hn : n≤2^n := (show n<2^n from Nat.lt_two_pow_self).le
    have hp : (∑ i, v i)≤2^(n+2*B+1) := by
      calc
        _ ≤ n*2^(2*B+1) := hs
        _ ≤ 2^n*2^(2*B+1) := Nat.mul_le_mul_right _ hn
        _ = _ := by rw [←pow_add]; congr 1
    have hb := Nat.size_le_size hp
    simp only [Nat.size_pow] at hb
    rw [Nat.size_eq_bits_len]
    unfold workWidth
    omega
  exact ⟨bound _ (fun i => term _ _ _ _ (hx i).1 (hy i).1 (hx i).2 (hy i).2),
    bound _ (fun i => term _ _ _ _ (hx i).1 (hy i).2 (hx i).2 (hy i).1)⟩

theorem represented_width {n B : ℕ} (a : Snapshot n) (p q : Fin 12)
    {s : BitRAMState} (hsize : a.data.Sized B) (ha : Horner.Stored a.data a.words s) :
    (Pairing.positive (left a p q) (right a)).bits.length≤workWidth n B ∧
      (Pairing.negative (left a p q) (right a)).bits.length≤workWidth n B := by
  have raw (r : Fin 12) (i : Fin n) : addressValue ((a.words r).get i)≤2^B := by
    have hr := IndexedAddress.value_lt_pow_length ((a.words r).get i)
    rw [(ha.arrays r).length i] at hr
    exact hr.le.trans (Nat.pow_le_pow_right (by decide) hsize.2.1)
  exact pair_width _ _ (fun i => ⟨raw p i,raw q i⟩)
    (fun i => ⟨raw 10 i,raw 11 i⟩)

theorem dimension_lt (n B : ℕ) : n<2^(workWidth n B) :=
  (show n<2^n from Nat.lt_two_pow_self).trans_le
    (Nat.pow_le_pow_right (by decide) (by unfold workWidth; omega))

theorem signed_value {n : ℕ} (a : Snapshot n) (p q : Fin 12) :
    (Pairing.positive (left a p q) (right a):ℤ)-
      Pairing.negative (left a p q) (right a)=
        ∑ i, (left a p q).value i*(right a).value i := Pairing.signed_value _ _

theorem norm_value {n : ℕ} (a : Snapshot n) :
    (Pairing.positive (right a) (right a):ℤ)-Pairing.negative (right a) (right a)=
      ∑ i, ((right a).value i)^2 := by
  rw [Pairing.signed_value]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms represented_width
#print axioms norm_value

end Maxwell.Continuum.Calibration.NeumannMachine.StoredPairing
