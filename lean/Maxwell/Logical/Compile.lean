import Maxwell.Logical.Extension

/-! Actual expression-to-acyclic-circuit compilation. Recursive compilation
allocates exactly one equation per arithmetic node and preserves every prior
coordinate. This is an algebraic compiler component, not yet the complete
bounded-fanout sparse-system normal form.
-/

namespace Maxwell.Logical

inductive Expression (inputIds : ℕ) where
  | var (index : Fin inputIds)
  | zero
  | scale (weight : ℚ) (child : Expression inputIds)
  | add (left right : Expression inputIds)

namespace Expression

def gateCount {v : ℕ} : Expression v → ℕ
  | .var _ => 0
  | .zero => 1
  | .scale _ child => child.gateCount + 1
  | .add left right => left.gateCount + right.gateCount + 1

def evaluate {v : ℕ} : Expression v → (Fin v → ℝ) → ℝ
  | .var i, x => x i
  | .zero, _ => 0
  | .scale w child, x => (w : ℝ) * child.evaluate x
  | .add left right, x => left.evaluate x + right.evaluate x

def BoundedWeights {v : ℕ} : Expression v → Prop
  | .var _ => True
  | .zero => True
  | .scale w child => |(w : ℝ)| ≤ 1 ∧ child.BoundedWeights
  | .add left right => left.BoundedWeights ∧ right.BoundedWeights

theorem scale_error_bound (w x y error E k : ℝ)
    (hw : |w| ≤ 1) (hx : |x - y| ≤ k * E) (he : |error| ≤ E) :
    |w * x + error - w * y| ≤ (k + 1) * E := by
  calc
    _ = |w * (x - y) + error| := by congr 1; ring
    _ ≤ |w * (x - y)| + |error| := abs_add_le _ _
    _ ≤ 1 * (k * E) + E := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul hw hx (abs_nonneg _) (by positivity)) he
    _ = _ := by ring

theorem add_error_bound (x y a b error E k l : ℝ)
    (hx : |x - a| ≤ k * E) (hy : |y - b| ≤ l * E) (he : |error| ≤ E) :
    |x + y + error - (a + b)| ≤ (k + l + 1) * E := by
  calc
    _ = |(x - a) + (y - b) + error| := by congr 1; ring
    _ ≤ |(x - a) + (y - b)| + |error| := abs_add_le _ _
    _ ≤ (|x - a| + |y - b|) + |error| := add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ (k * E + l * E) + E := add_le_add (add_le_add hx hy) he
    _ = _ := by ring

def inputUses {v d : ℕ} : Expression v → (Fin v → Fin d) → Fin d → ℕ
  | .var i, ids, k => Circuit.hit k (ids i)
  | .zero, _, _ => 0
  | .scale _ e, ids, k => e.inputUses ids k
  | .add a b, ids, k => a.inputUses ids k + b.inputUses ids k

theorem inputUses_castLE {v d s : ℕ} (e : Expression v) (ids : Fin v → Fin d)
    (h : d ≤ s) (k : Fin d) :
    e.inputUses (fun i => Fin.castLE h (ids i)) (Fin.castLE h k) = e.inputUses ids k := by
  induction e with
  | var i => exact Circuit.hit_castLE h k (ids i)
  | zero => rfl
  | scale a e ih => exact ih
  | add a b iha ihb => exact congrArg₂ (· + ·) iha ihb

theorem inputUses_zero {v d : ℕ} (e : Expression v) (ids : Fin v → Fin d)
    (k : Fin d) (h : ∀ i, k ≠ ids i) : e.inputUses ids k = 0 := by
  induction e with
  | var i => simp [inputUses, Circuit.hit, h i]
  | zero => rfl
  | scale a e ih => exact ih
  | add a b iha ihb => simp [inputUses, iha, ihb]

end Expression

namespace Circuit

@[simp] theorem evaluate_zero_append_old {n d : ℕ} (c : Circuit n d)
    (a : Fin d → ℝ) (input : Fin n → ℝ) (i : Fin d) :
    (c.append a).evaluate input 0 i.castSucc = c.evaluate input 0 i := by
  simp only [evaluate_append_castSucc]
  rfl

@[simp] theorem evaluate_zero_append_new {n d : ℕ} (c : Circuit n d)
    (a : Fin d → ℝ) (input : Fin n → ℝ) :
    (c.append a).evaluate input 0 (Fin.last d) =
      ∑ i, a i * c.evaluate input 0 i := by
  simp only [evaluate_append_last, Pi.zero_apply, add_zero]
  rfl

end Circuit

/-- A compiled expression carries its actual allocated circuit and proofs
of preservation, semantics, and exact allocation count. -/
structure ExpressionCompilation {n d v : ℕ} (prior : Circuit n d)
    (inputIds : Fin v → Fin d) (expression : Expression v) where
  size : ℕ
  size_le : d ≤ size
  circuit : Circuit n size
  extension : prior.Extends circuit
  output : Fin size
  allocation : size = d + expression.gateCount
  preserves : ∀ (input : Fin n → ℝ) (i : Fin d),
    circuit.evaluate input 0 (Fin.castLE size_le i) = prior.evaluate input 0 i
  correct : ∀ input : Fin n → ℝ,
    circuit.evaluate input 0 output = expression.evaluate (fun i => prior.evaluate input 0 (inputIds i))
  error_bound : expression.BoundedWeights → ∀ (input : Fin n → ℝ)
    (error : Fin size → ℝ) (E : ℝ), 0 ≤ E → (∀ i, |error i| ≤ E) →
    |circuit.evaluate input error output - expression.evaluate
      (fun i => prior.evaluate input (fun j => error (Fin.castLE size_le j)) (inputIds i))| ≤
      (expression.gateCount : ℝ) * E
  charged_old : ∀ k : Fin d,
    circuit.charged output (Fin.castLE size_le k) ≤ prior.uses k + expression.inputUses inputIds k
  charged_new : ∀ k : Fin size, d ≤ k.val → circuit.charged output k ≤ 1

/-- Verified scaling allocation, with the recursive result kept abstract. -/
def compileScale {n d v : ℕ} {child : Expression v} (w : ℚ)
    (prior : Circuit n d) (inputIds : Fin v → Fin d)
    (result : ExpressionCompilation prior inputIds child) :
    ExpressionCompilation prior inputIds (.scale w child) := by
  refine {
    size := result.size + 1
    size_le := result.size_le.trans (Nat.le_succ _)
    circuit := result.circuit.scaledGate result.output w
    extension := result.extension.append _
    output := Fin.last result.size
    allocation := ?_
    preserves := ?_
    correct := ?_
    error_bound := ?_
    charged_old := ?_
    charged_new := ?_ }
  · rw [result.allocation]
    simp only [Expression.gateCount]
    omega
  · intro input i
    have hc : Fin.castLE (result.size_le.trans (Nat.le_succ _)) i =
        (Fin.castLE result.size_le i).castSucc := by apply Fin.ext; rfl
    rw [hc]
    change (result.circuit.append _).evaluate input 0 _ = _
    rw [Circuit.evaluate_zero_append_old]
    exact result.preserves input i
  · intro input
    rw [Circuit.scaledGate_last]
    change (w : ℝ) * result.circuit.evaluate input 0 result.output + 0 = _
    rw [result.correct]
    simp [Expression.evaluate]
  · intro hb input error E hE he
    have hx := result.error_bound hb.2 input (fun i => error i.castSucc) E hE
      (fun i => he i.castSucc)
    rw [Circuit.scaledGate_last]
    change |(w : ℝ) * result.circuit.evaluate input (fun i => error i.castSucc) result.output +
        error (Fin.last result.size) - (w : ℝ) * child.evaluate _| ≤ _
    have hr := Expression.scale_error_bound w _ _ (error (Fin.last result.size)) E
      child.gateCount hb.1 hx (he (Fin.last result.size))
    simpa [Expression.gateCount] using hr
  · intro k
    have hc : Fin.castLE (result.size_le.trans (Nat.le_succ _)) k =
        (Fin.castLE result.size_le k).castSucc := by apply Fin.ext; rfl
    rw [hc]
    exact (result.circuit.charged_scaled_old_le result.output _ w).trans (result.charged_old k)
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · intro _
      simp [Circuit.scaledGate]
    · intro hj
      exact (result.circuit.charged_scaled_old_le result.output j w).trans
        (result.charged_new j hj)

/-- Verified addition allocation with proof terms shared between recursive calls. -/
def compileAdd {n d v : ℕ} {left right : Expression v}
    (prior : Circuit n d) (inputIds : Fin v → Fin d)
    (l : ExpressionCompilation prior inputIds left)
    (r : ExpressionCompilation l.circuit (fun i => Fin.castLE l.size_le (inputIds i)) right) :
    ExpressionCompilation prior inputIds (.add left right) := by
  let newVariables : Fin v → Fin l.size := fun i => Fin.castLE l.size_le (inputIds i)
  let leftOutput : Fin r.size := Fin.castLE r.size_le l.output
  refine {
    size := r.size + 1
    size_le := (l.size_le.trans r.size_le).trans (Nat.le_succ _)
    circuit := r.circuit.additionGate leftOutput r.output
    extension := (l.extension.trans r.extension).append _
    output := Fin.last r.size
    allocation := ?_
    preserves := ?_
    correct := ?_
    error_bound := ?_
    charged_old := ?_
    charged_new := ?_ }
  · rw [r.allocation, l.allocation]
    simp only [Expression.gateCount]
    omega
  · intro input i
    have hc : Fin.castLE ((l.size_le.trans r.size_le).trans (Nat.le_succ _)) i =
        (Fin.castLE r.size_le (Fin.castLE l.size_le i)).castSucc := by
      apply Fin.ext
      rfl
    rw [hc]
    change (r.circuit.append _).evaluate input 0 _ = _
    rw [Circuit.evaluate_zero_append_old, r.preserves, l.preserves]
  · intro input
    rw [Circuit.additionGate_last]
    change r.circuit.evaluate input 0 leftOutput + r.circuit.evaluate input 0 r.output + 0 = _
    rw [show leftOutput = Fin.castLE r.size_le l.output from rfl, r.preserves,
      l.correct, r.correct]
    have hvars : (fun i => l.circuit.evaluate input 0 (newVariables i)) =
        (fun i => prior.evaluate input 0 (inputIds i)) := by
      funext i
      exact l.preserves input (inputIds i)
    rw [hvars]
    simp [Expression.evaluate]
  · intro hb input error E hE he
    let er : Fin r.size → ℝ := fun i => error i.castSucc
    let el : Fin l.size → ℝ := fun i => er (Fin.castLE r.size_le i)
    have hl := l.error_bound hb.1 input el E hE (fun i => he _)
    have hr := r.error_bound hb.2 input er E hE (fun i => he _)
    have hold : r.circuit.evaluate input er leftOutput =
        l.circuit.evaluate input el l.output := r.extension.evaluate_old input er l.output
    have hv : (fun i => l.circuit.evaluate input (fun j => er (Fin.castLE r.size_le j))
        (newVariables i)) =
        (fun i => prior.evaluate input (fun j => el (Fin.castLE l.size_le j)) (inputIds i)) := by
      funext i
      exact l.extension.evaluate_old input el (inputIds i)
    rw [hv] at hr
    rw [Circuit.additionGate_last]
    change |r.circuit.evaluate input er leftOutput + r.circuit.evaluate input er r.output +
        error (Fin.last r.size) - (left.evaluate _ + right.evaluate _)| ≤ _
    rw [hold]
    have hresult := Expression.add_error_bound _ _ _ _ (error (Fin.last r.size)) E
      left.gateCount right.gateCount hl hr (he (Fin.last r.size))
    simpa [Expression.gateCount, el, er, Fin.castLE] using hresult
  · intro k
    let kl := Fin.castLE l.size_le k
    let kr := Fin.castLE r.size_le kl
    have hc : Fin.castLE ((l.size_le.trans r.size_le).trans (Nat.le_succ _)) k =
        kr.castSucc := by apply Fin.ext; rfl
    rw [hc]
    have ha := r.circuit.charged_add_old_le leftOutput r.output kr
    have hr := r.charged_old kl
    have hl := l.charged_old k
    have hright : right.inputUses newVariables kl = right.inputUses inputIds k :=
      right.inputUses_castLE inputIds l.size_le k
    have hleft : Circuit.hit kr leftOutput = Circuit.hit kl l.output :=
      Circuit.hit_castLE r.size_le kl l.output
    change _ ≤ prior.uses k + (left.inputUses inputIds k + right.inputUses inputIds k)
    simp only [Circuit.charged] at hr hl
    rw [hright] at hr
    rw [hleft] at ha
    change r.circuit.uses kr + Circuit.hit kr r.output ≤
      l.circuit.uses kl + right.inputUses inputIds k at hr
    change l.circuit.uses kl + Circuit.hit kl l.output ≤
      prior.uses k + left.inputUses inputIds k at hl
    omega
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · intro _
      simp [Circuit.additionGate]
    · intro hj
      change d ≤ j.val at hj
      have ha := r.circuit.charged_add_old_le leftOutput r.output j
      by_cases hjl : j.val < l.size
      · let jl : Fin l.size := ⟨j.val, hjl⟩
        have he : j = Fin.castLE r.size_le jl := by apply Fin.ext; rfl
        have hr := r.charged_old jl
        have hl := l.charged_new jl hj
        have hright : right.inputUses newVariables jl = 0 := by
          apply Expression.inputUses_zero
          intro i h
          have hv := congrArg (fun k : Fin l.size => k.val) h
          change j.val = (inputIds i).val at hv
          have hi := (inputIds i).isLt
          omega
        rw [hright] at hr
        simp only [Nat.add_zero, Circuit.charged] at hr hl
        rw [he] at ha
        have hleft : Circuit.hit (Fin.castLE r.size_le jl) leftOutput =
            Circuit.hit jl l.output := Circuit.hit_castLE r.size_le jl l.output
        rw [hleft] at ha
        rw [he]
        omega
      · have hr := r.charged_new j (Nat.le_of_not_gt hjl)
        have hleft : Circuit.hit j leftOutput = 0 := by
          have hne : j ≠ leftOutput := by
            intro h
            have hv := congrArg (fun k : Fin r.size => k.val) h
            change j.val = l.output.val at hv
            have ho := l.output.isLt
            omega
          simp [Circuit.hit, hne]
        rw [hleft] at ha
        simp only [Nat.add_zero, Circuit.charged] at ha hr
        exact ha.trans hr

/-- Recursive, executable allocation. Each step uses a separately checked
constructor, so kernel checking does not expand recursive proof fields. -/
def compileExpression {n d v : ℕ} (expression : Expression v)
    (prior : Circuit n d) (inputIds : Fin v → Fin d) :
    ExpressionCompilation prior inputIds expression :=
  match expression with
  | .var i => by
      exact {
        size := d
        size_le := le_refl _
        circuit := prior
        extension := .refl
        output := inputIds i
        allocation := by simp [Expression.gateCount]
        preserves := by intro input j; rfl
        correct := by intro input; rfl
        error_bound := by intro _ input error E _ _; simp [Expression.evaluate, Expression.gateCount]
        charged_old := by intro k; exact le_refl _
        charged_new := by intro k hk; exact False.elim (Nat.not_lt_of_ge hk k.isLt) }
  | .zero => by
      refine {
        size := d + 1
        size_le := Nat.le_succ d
        circuit := prior.append 0
        extension := .append .refl 0
        output := Fin.last d
        allocation := rfl
        preserves := ?_
        correct := ?_
        error_bound := ?_
        charged_old := ?_
        charged_new := ?_ }
      · intro input i
        exact prior.evaluate_zero_append_old 0 input i
      · intro input
        simp [Expression.evaluate]
      · intro _ input error E _ he
        simpa [Expression.evaluate, Expression.gateCount] using he (Fin.last d)
      · intro k
        change (prior.append 0).charged (Fin.last d) k.castSucc ≤ prior.uses k + 0
        simp
      · intro k hk
        have he : k = Fin.last d := by apply Fin.ext; have := k.isLt; simp; omega
        subst k
        simp
  | .scale w child => compileScale w prior inputIds (compileExpression child prior inputIds)
  | .add left right =>
      let l := compileExpression left prior inputIds
      let r := compileExpression right l.circuit (fun i => Fin.castLE l.size_le (inputIds i))
      compileAdd prior inputIds l r

end Maxwell.Logical
