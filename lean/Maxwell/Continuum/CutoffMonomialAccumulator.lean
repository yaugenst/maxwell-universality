import Maxwell.Continuum.CutoffChebyshevChannels
import Maxwell.Continuum.RationalDataflowFixedWidths

/-! One cached recurrence forms the monomial coefficients from the encoded
Chebyshev coefficients. Its two integer rows and weighted sum are shared. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow Profile
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

structure MonomialState (D : ℕ) where
  older : Vector Parts D
  current : Vector Parts D
  total : Vector Parts D

def monomialState (D : ℕ) (a : ℕ→Parts) : ℕ→MonomialState D
  | 0 => ⟨(rawChebyshevState D 0).1,(rawChebyshevState D 0).2,
      Vector.ofFn (fun _ => Parts.literal 0)⟩
  | j+1 =>
      let v := monomialState D a j
      ⟨v.current,
       Vector.ofFn (fun i => ((Parts.literal 2).mul
         (if hi : i.val=0 then Parts.literal 0 else v.current.get ⟨i.val-1,by omega⟩)).sub (v.older.get i)),
       Vector.ofFn (fun i => (v.total.get i).add ((a j).mul (v.older.get i)))⟩

theorem monomialState_rows (D : ℕ) (a : ℕ→Parts) (j : ℕ) :
    (monomialState D a j).older=(rawChebyshevState D j).1 ∧
    (monomialState D a j).current=(rawChebyshevState D j).2 := by
  induction j with
  | zero => exact ⟨rfl,rfl⟩
  | succ j ih =>
    constructor
    · exact ih.2
    · simp only [monomialState,rawChebyshevState,ih.1,ih.2]

theorem monomialState_total (D : ℕ) (a : ℕ→Parts) (j : ℕ) (i : Fin D) :
    (monomialState D a j).total.get i=
      sum (fun k => (a k).mul ((rawChebyshevState D k).1.get i)) j := by
  induction j with
  | zero => simp only [monomialState,vector_get_ofFn,sum]
  | succ j ih =>
    simp only [monomialState,vector_get_ofFn,sum,ih,(monomialState_rows D a j).1]

theorem monomialState_total_valid (D : ℕ) (a : ℕ→Parts) (j : ℕ)
    (ha : ∀ k<j, (a k).Valid) (i : Fin D) : ((monomialState D a j).total.get i).Valid := by
  rw [monomialState_total]
  exact sum_valid _ _ (fun k hk => Parts.mul_valid (ha k hk) ((rawChebyshevState_valid D k).1 i))

theorem monomialState_total_width (D W : ℕ) (a : ℕ→Parts)
    (ha : ∀ k<D, (a k).Width W) (j : ℕ) (hj : j≤D) (i : Fin D) :
    ((monomialState D a j).total.get i).Width (D*(W+2*D+3)+1) := by
  rw [monomialState_total]
  have hb : ∀ k<j, ((a k).mul ((rawChebyshevState D k).1.get i)).Width (W+2*D+2) := by
    intro k hk
    exact ((ha k (by omega)).mul ((rawChebyshevState_width D k).1 i)).mono (by omega)
  apply (sum_width _ j _ hb).mono
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hj) 1

theorem monomialState_total_value (D : ℕ) (a : ℕ→Parts) (j : ℕ)
    (ha : ∀ k<j, (a k).Valid) (i : Fin D) :
    ((monomialState D a j).total.get i).value=
      ∑ k∈Finset.range j, (a k).value*((chebyshevRow D k).get i : ℚ) := by
  rw [monomialState_total,sum_value _ _
    (fun k hk => Parts.mul_valid (ha k hk) ((rawChebyshevState_valid D k).1 i))]
  apply Finset.sum_congr rfl
  intro k _
  rw [Parts.mul_value,(rawChebyshevState_value D k).1 i]
  rfl

theorem monomialState_encoded_value (N : ℕ) (i : Fin (profileDegree N)) :
    ((monomialState (profileDegree N) (coefficient N) (profileDegree N)).total.get i).value=
      (monomialCoefficient N i).value := by
  rw [monomialState_total_value _ _ _ (fun k _ => coefficient_valid N k),monomialCoefficient_value]
  simp only [coefficient_value]

theorem monomialState_encoded_width (N : ℕ) (i : Fin (profileDegree N)) :
    ((monomialState (profileDegree N) (coefficient N) (profileDegree N)).total.get i).Width
      (2^65*(N+1)^4) := by
  apply (monomialState_total_width (profileDegree N) (272*(N+1)) (coefficient N)
    (fun k hk => coefficient_width N k hk) _ le_rfl i).mono
  have hd := profileDegree_bound N
  have hN : N+1≤(N+1)^2 := le_self_pow₀ (by omega) (by decide : (2:ℕ)≠0)
  have h1 : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hin : 272*(N+1)+2*profileDegree N+3≤2^32*(N+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul hd hin
  have h4 : 1≤(N+1)^4 := one_le_pow₀ (by omega)
  nlinarith only [hm,h4]

def monomialRowControl : Control :=
  .step (.binary .mul 6 5 2) (.step (.binary .sub 6 6 0)
    (.step (.binary .mul 7 4 0) (.step (.binary .add 7 3 7) .done)))

theorem monomialRowControl_valid : monomialRowControl.Valid (Finset.range 8) := by
  simp [monomialRowControl,Control.Valid,Instruction.Valid]

theorem monomialRowControl_admissible (v : ℕ→Parts) : monomialRowControl.AdmissibleTrace v := by
  simp [monomialRowControl,Control.AdmissibleTrace,Instruction.Admissible]

theorem monomialRowControl_result (v : ℕ→Parts) :
    monomialRowControl.evaluate v 1=v 1 ∧
    monomialRowControl.evaluate v 6=((v 5).mul (v 2)).sub (v 0) ∧
    monomialRowControl.evaluate v 7=(v 3).add ((v 4).mul (v 0)) := by
  simp [monomialRowControl,Control.evaluate,Instruction.update,BinaryOp.eval]

theorem monomialRowControl_widthTrace (v : ℕ→Parts) (W : ℕ)
    (hv : WidthBank (Finset.range 8) W v) :
    monomialRowControl.WidthTrace (Finset.range 8) (16*(W+1)) v := by
  have h := monomialRowControl.automatic_widthTrace _ monomialRowControl_valid v W hv
    (by simp [monomialRowControl,Control.LiteralsFit,Instruction.LiteralFits])
  have hs : monomialRowControl.steps=4 := rfl
  simpa only [hs,show (2:ℕ)^4=16 from rfl] using h

#print axioms monomialState_encoded_value
#print axioms monomialState_encoded_width
end Maxwell.Continuum.Calibration.RawCutoff
