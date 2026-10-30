import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Exact scalar-pivot elimination for finite real quadratic forms. -/

namespace Maxwell.Continuum.Calibration

variable {n : ℕ}

def realQuadratic (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i*A i j*x j

def scalarSchur {K : Type*} [Field K] (A : Matrix (Fin (n+1)) (Fin (n+1)) K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => A i.succ j.succ-A i.succ 0*A 0 j.succ/A 0 0

theorem scalarSchur_symmetric {K : Type*} [Field K]
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) (hA : ∀ i j, A i j=A j i) :
    ∀ i j, scalarSchur A i j=scalarSchur A j i := by
  intro i j
  unfold scalarSchur
  rw [hA i.succ j.succ,hA i.succ 0,hA j.succ 0]
  ring

theorem realQuadratic_cons (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ i j, A i j=A j i) (t : ℝ) (y : Fin n → ℝ) :
    realQuadratic A (Fin.cons t y)=A 0 0*t^2+2*t*(∑ j, A 0 j.succ*y j)+
      realQuadratic (fun i j => A i.succ j.succ) y := by
  simp only [realQuadratic,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,
    Finset.sum_add_distrib]
  have h1 : (∑ j, t*A 0 j.succ*y j)=t*(∑ j, A 0 j.succ*y j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : (∑ i, y i*A i.succ 0*t)=t*(∑ i, A 0 i.succ*y i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hA i.succ 0]
    ring
  rw [h1,h2]
  ring

theorem realQuadratic_scalarSchur (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ i j, A i j=A j i) (y : Fin n → ℝ) :
    realQuadratic (scalarSchur A) y=
      realQuadratic (fun i j => A i.succ j.succ) y-(∑ j, A 0 j.succ*y j)^2/A 0 0 := by
  simp only [realQuadratic,scalarSchur,mul_sub,sub_mul,Finset.sum_sub_distrib]
  congr 1
  rw [pow_two,Finset.sum_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [hA i.succ 0]
  ring

theorem realQuadratic_complete_square (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ i j, A i j=A j i) (ha : A 0 0≠0) (t : ℝ) (y : Fin n → ℝ) :
    realQuadratic A (Fin.cons t y)=
      A 0 0*(t+(∑ j, A 0 j.succ*y j)/A 0 0)^2+realQuadratic (scalarSchur A) y := by
  rw [realQuadratic_cons A hA,realQuadratic_scalarSchur A hA]
  field_simp
  ring

def StrictQuadratic (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x≠0 → 0<realQuadratic A x

theorem strictQuadratic_pivot (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ i j, A i j=A j i) :
    StrictQuadratic A ↔ 0<A 0 0 ∧ StrictQuadratic (scalarSchur A) := by
  constructor
  · intro h
    have ht : Fin.cons (α := fun _ : Fin (n+1) => ℝ) (1 : ℝ) (fun _ => 0)≠0 := by
      intro hz
      have hz0 := congrFun hz 0
      simp at hz0
    have ha := h _ ht
    rw [realQuadratic_cons A hA] at ha
    simp only [mul_zero,Finset.sum_const_zero,one_pow,mul_one,add_zero,realQuadratic] at ha
    refine ⟨ha,?_⟩
    intro y hy
    let t := -(∑ j, A 0 j.succ*y j)/A 0 0
    have hx : Fin.cons (α := fun _ : Fin (n+1) => ℝ) t y≠0 := by
      intro hz
      apply hy
      funext i
      have hi := congrFun hz i.succ
      simpa only [Fin.cons_succ,Pi.zero_apply] using hi
    have hh := h _ hx
    rw [realQuadratic_complete_square A hA ha.ne'] at hh
    simpa only [t,neg_div,neg_add_cancel,zero_pow (by decide : (2 : ℕ)≠0),mul_zero,zero_add] using hh
  · rintro ⟨ha,hs⟩ x hx
    have he : x=Fin.cons (x 0) (fun i => x i.succ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    rw [he,realQuadratic_complete_square A hA ha.ne']
    by_cases hy : (fun i : Fin n => x i.succ)=0
    · have hx0 : x 0≠0 := by
        intro hz
        apply hx
        rw [he,hz,hy]
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      have hy' (i : Fin n) : x i.succ=0 := congrFun hy i
      simp only [realQuadratic,hy',mul_zero,zero_mul,Finset.sum_const_zero,zero_div,add_zero]
      exact mul_pos ha (sq_pos_of_ne_zero hx0)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (sq_nonneg _)) (hs _ hy)

#print axioms strictQuadratic_pivot

end Maxwell.Continuum.Calibration
