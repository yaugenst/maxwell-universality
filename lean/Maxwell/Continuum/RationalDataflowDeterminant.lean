import Maxwell.Continuum.RationalDataflowExpression
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Literal Laplace-expansion circuits. Their interpretation and size are
proved for arbitrary finite dimensions, so a fixed central matrix can be
compiled without enumerating its factorial-size circuit in the proof. -/
namespace Maxwell.Continuum.RationalDataflow.PolynomialExpression
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def sum : List PolynomialExpression → PolynomialExpression
  | [] => .literal 0
  | x::xs => .binary .add x (sum xs)

theorem sum_evaluate (xs : List PolynomialExpression) (v : ℕ → ℚ) :
    (sum xs).evaluate v=(xs.map (fun e => e.evaluate v)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sum,evaluate,binaryValue,List.map_cons,List.sum_cons,ih]

theorem sum_scoped (xs : List PolynomialExpression) (base : ℕ)
    (h : ∀e∈xs,e.Scoped base) : (sum xs).Scoped base := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨h x (by simp),ih (fun e he => h e (by simp [he]))⟩

theorem sum_literals (xs : List PolynomialExpression) (B : ℕ) (hB : 1≤B)
    (h : ∀e∈xs,e.LiteralsFit B) : (sum xs).LiteralsFit B := by
  induction xs with
  | nil =>
    exact (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hB
  | cons x xs ih => exact ⟨h x (by simp),ih (fun e he => h e (by simp [he]))⟩

theorem sum_nodes (xs : List PolynomialExpression) (C : ℕ)
    (h : ∀e∈xs,e.nodes≤C) : (sum xs).nodes≤xs.length*(C+1)+1 := by
  induction xs with
  | nil => simp [sum,nodes]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun e he => h e (by simp [he]))
    simp only [sum,nodes,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def determinant : (n : ℕ) → Matrix (Fin n) (Fin n) PolynomialExpression → PolynomialExpression
  | 0,_ => .literal 1
  | n+1,A => sum (List.ofFn (fun j : Fin (n+1) =>
      .binary .mul (.binary .mul (.literal ((-1:ℚ)^j.val)) (A 0 j))
        (determinant n (A.submatrix Fin.succ j.succAbove))))

def determinantNodes : ℕ → ℕ → ℕ
  | 0,_ => 1
  | n+1,C => (n+1)*(4+C+determinantNodes n C)+1

theorem determinant_evaluate (n : ℕ) (A : Matrix (Fin n) (Fin n) PolynomialExpression)
    (v : ℕ → ℚ) : (determinant n A).evaluate v=(A.map (fun e => e.evaluate v)).det := by
  induction n with
  | zero => rw [Matrix.det_isEmpty];rfl
  | succ n ih =>
    rw [determinant,sum_evaluate,List.map_ofFn,List.sum_ofFn,Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Function.comp_apply,evaluate,binaryValue,ih,Matrix.submatrix,Matrix.map_apply]
    rfl

theorem determinant_scoped (n : ℕ) (A : Matrix (Fin n) (Fin n) PolynomialExpression)
    (base : ℕ) (h : ∀i j,(A i j).Scoped base) : (determinant n A).Scoped base := by
  induction n with
  | zero => trivial
  | succ n ih =>
    apply sum_scoped
    intro e he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact ⟨⟨trivial,h 0 j⟩,ih _ (fun i k => h _ _)⟩

theorem sign_literal_width (j B : ℕ) (hB : 1≤B) : (Parts.literal ((-1:ℚ)^j)).Width B := by
  rcases neg_one_pow_eq_or ℚ j with h|h <;> rw [h]
  · exact (show (Parts.literal 1).Width 1 by change 1≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hB
  · exact (show (Parts.literal (-1)).Width 1 by change 0≤1 ∧ 1≤1 ∧ 1≤1;omega).mono hB

theorem determinant_literals (n : ℕ) (A : Matrix (Fin n) (Fin n) PolynomialExpression)
    (B : ℕ) (hB : 1≤B) (h : ∀i j,(A i j).LiteralsFit B) :
    (determinant n A).LiteralsFit B := by
  induction n with
  | zero => exact (show (Parts.literal 1).Width 1 by change 1≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hB
  | succ n ih =>
    apply sum_literals _ B hB
    intro e he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact ⟨⟨sign_literal_width j.val B hB,h 0 j⟩,ih _ (fun i k => h _ _)⟩

theorem determinant_nodes (n : ℕ) (A : Matrix (Fin n) (Fin n) PolynomialExpression)
    (C : ℕ) (h : ∀i j,(A i j).nodes≤C) : (determinant n A).nodes≤determinantNodes n C := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have entries : ∀e∈List.ofFn (fun j : Fin (n+1) =>
        binary .mul (binary .mul (literal ((-1:ℚ)^j.val)) (A 0 j))
          (determinant n (A.submatrix Fin.succ j.succAbove))),
        e.nodes≤3+C+determinantNodes n C := by
      intro e he
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
      have ha := h 0 j
      have hm := ih (A.submatrix Fin.succ j.succAbove) (fun i k => h _ _)
      simp only [nodes]
      omega
    have bound := sum_nodes _ _ entries
    simp only [List.length_ofFn] at bound
    change (sum _).nodes≤(n+1)*(4+C+determinantNodes n C)+1
    convert bound using 1
    ring

#print axioms determinant_evaluate
#print axioms determinant_nodes
end Maxwell.Continuum.RationalDataflow.PolynomialExpression
