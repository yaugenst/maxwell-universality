import Maxwell.Logical.Compile
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn

namespace Maxwell.Logical.Expression

def rename {v w : ℕ} (f : Fin v → Fin w) : Expression v → Expression w
  | .var i => .var (f i)
  | .zero => .zero
  | .scale a e => .scale a (rename f e)
  | .add a b => .add (rename f a) (rename f b)

theorem rename_evaluate {v w : ℕ} (f : Fin v → Fin w) (e : Expression v)
    (x : Fin w → ℝ) : (e.rename f).evaluate x = e.evaluate (fun i => x (f i)) := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih => simp [rename, evaluate, ih]
  | add a b iha ihb => simp [rename, evaluate, iha, ihb]

@[simp] theorem rename_gateCount {v w : ℕ} (f : Fin v → Fin w) (e : Expression v) :
    (e.rename f).gateCount = e.gateCount := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih => simp [rename, gateCount, ih]
  | add a b iha ihb => simp [rename, gateCount, iha, ihb]

def occurrences {v : ℕ} : Expression v → List (Fin v)
  | .var i => [i]
  | .zero => []
  | .scale _ e => e.occurrences
  | .add a b => a.occurrences ++ b.occurrences

theorem occurrences_rename {v w : ℕ} (f : Fin v → Fin w) (e : Expression v) :
    (e.rename f).occurrences = e.occurrences.map f := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih => exact ih
  | add a b iha ihb => simp [rename, occurrences, iha, ihb]

@[simp] theorem rename_bounded {v w : ℕ} (f : Fin v → Fin w) (e : Expression v) :
    (e.rename f).BoundedWeights ↔ e.BoundedWeights := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih => simp [rename, BoundedWeights, ih]
  | add a b iha ihb => simp [rename, BoundedWeights, iha, ihb]

def leafCount {v : ℕ} : Expression v → ℕ
  | .var _ => 1
  | .zero => 0
  | .scale _ e => e.leafCount
  | .add a b => a.leafCount + b.leafCount

theorem occurrences_length {v : ℕ} (e : Expression v) :
    e.occurrences.length = e.leafCount := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih => exact ih
  | add a b iha ihb => simp [occurrences, leafCount, iha, ihb]

/-- Every variable occurrence receives its own coordinate. -/
def linearized {v : ℕ} : (e : Expression v) → Expression e.leafCount
  | .var _ => .var ⟨0, by simp [leafCount]⟩
  | .zero => .zero
  | .scale a e => .scale a e.linearized
  | .add a b => .add (a.linearized.rename (Fin.castAdd b.leafCount))
      (b.linearized.rename (Fin.natAdd a.leafCount))

def leafSource {v : ℕ} : (e : Expression v) → Fin e.leafCount → Fin v
  | .var i => fun _ => i
  | .zero => Fin.elim0
  | .scale _ e => e.leafSource
  | .add a b => Fin.append a.leafSource b.leafSource

theorem leafSource_list {v : ℕ} (e : Expression v) :
    List.ofFn e.leafSource = e.occurrences := by
  induction e with
  | var i => simp [leafSource, occurrences, leafCount, List.ofFn_succ]
  | zero => rfl
  | scale a e ih => exact ih
  | add a b iha ihb =>
      change List.ofFn (Fin.append a.leafSource b.leafSource) = a.occurrences ++ b.occurrences
      rw [List.ofFn_fin_append, iha, ihb]

theorem linearized_evaluate {v : ℕ} (e : Expression v) (x : Fin v → ℝ) :
    e.linearized.evaluate (fun i => x (e.leafSource i)) = e.evaluate x := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih =>
      change (a : ℝ) * e.linearized.evaluate (fun i => x (e.leafSource i)) =
        (a : ℝ) * e.evaluate x
      rw [ih]
  | add a b iha ihb =>
      change (a.linearized.rename (Fin.castAdd b.leafCount)).evaluate
          (fun i => x (Fin.append a.leafSource b.leafSource i)) +
        (b.linearized.rename (Fin.natAdd a.leafCount)).evaluate
          (fun i => x (Fin.append a.leafSource b.leafSource i)) = _
      rw [rename_evaluate, rename_evaluate]
      simp only [Fin.append_left, Fin.append_right]
      rw [iha, ihb]
      rfl

theorem linearized_gateCount {v : ℕ} (e : Expression v) :
    e.linearized.gateCount = e.gateCount := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih =>
      change e.linearized.gateCount + 1 = e.gateCount + 1
      rw [ih]
  | add a b iha ihb =>
      dsimp only [linearized, leafCount, gateCount]
      rw [rename_gateCount, rename_gateCount, iha, ihb]

theorem linearized_bounded {v : ℕ} (e : Expression v) :
    e.linearized.BoundedWeights ↔ e.BoundedWeights := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih =>
      change (|(a : ℝ)| ≤ 1 ∧ e.linearized.BoundedWeights) ↔
        (|(a : ℝ)| ≤ 1 ∧ e.BoundedWeights)
      rw [ih]
  | add a b iha ihb =>
      dsimp only [linearized, leafCount, BoundedWeights]
      rw [rename_bounded, rename_bounded, iha, ihb]

theorem evaluate_lipschitz {v : ℕ} (e : Expression v) (hb : e.BoundedWeights)
    (x y : Fin v → ℝ) (X : ℝ) (hX : ∀ i, |x i - y i| ≤ X) :
    |e.evaluate x - e.evaluate y| ≤ (e.leafCount : ℝ) * X := by
  induction e with
  | var i => simpa [evaluate, leafCount] using hX i
  | zero => simp [evaluate, leafCount]
  | scale a e ih =>
      change |(a : ℝ) * e.evaluate x - (a : ℝ) * e.evaluate y| ≤ _
      rw [← mul_sub, abs_mul]
      exact (mul_le_mul hb.1 (ih hb.2) (abs_nonneg _) (by norm_num)).trans_eq
        (one_mul _)
  | add a b iha ihb =>
      change |(a.evaluate x + b.evaluate x) - (a.evaluate y + b.evaluate y)| ≤ _
      calc
        _ = |(a.evaluate x - a.evaluate y) + (b.evaluate x - b.evaluate y)| := by congr 1; ring
        _ ≤ |a.evaluate x - a.evaluate y| + |b.evaluate x - b.evaluate y| := abs_add_le _ _
        _ ≤ (a.leafCount : ℝ) * X + (b.leafCount : ℝ) * X :=
          add_le_add (iha hb.1) (ihb hb.2)
        _ = _ := by simp [leafCount, add_mul]

/-- Each allocated occurrence is used exactly once by the expression tree. -/
theorem linearized_occurrences {v : ℕ} (e : Expression v) :
    e.linearized.occurrences = List.finRange e.leafCount := by
  induction e with
  | var i => rfl
  | zero => rfl
  | scale a e ih => exact ih
  | add a b iha ihb =>
      simp only [linearized, occurrences, occurrences_rename, iha, ihb, leafCount]
      rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, ← List.ofFn_fin_append]
      have hf : Fin.append (Fin.castAdd b.leafCount) (Fin.natAdd a.leafCount) = id := by
        funext i
        exact Fin.addCases (fun j => by simp) (fun j => by simp) i
      rw [hf]
      exact List.ofFn_id _

theorem linearized_nodup {v : ℕ} (e : Expression v) : e.linearized.occurrences.Nodup := by
  rw [linearized_occurrences]
  exact List.nodup_finRange _

theorem leafCount_le_gateCount_add_one {v : ℕ} (e : Expression v) :
    e.leafCount ≤ e.gateCount + 1 := by
  induction e with
  | var i => rfl
  | zero => simp [leafCount, gateCount]
  | scale a e ih => simp only [leafCount, gateCount]; omega
  | add a b iha ihb => simp only [leafCount, gateCount]; omega

end Maxwell.Logical.Expression
