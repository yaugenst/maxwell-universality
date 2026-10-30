import Maxwell.Continuum.RationalDataflowTrace
import Maxwell.Continuum.RationalFiniteWidths

/-! Finite rational expression trees for fixed-size calibration circuits.
Input words remain runtime data; every intermediate raw word is bounded. -/

namespace Maxwell.Continuum.Calibration

open RationalDataflow

inductive RationalExpression where
  | input (source : ℕ)
  | zero
  | binary (op : BinaryOp) (left right : RationalExpression)
  | inverse (source : RationalExpression)
  deriving DecidableEq, Repr

namespace RationalExpression

def evaluate : RationalExpression → (ℕ → Parts) → Parts
  | .input i,v => v i
  | .zero,_ => Parts.literal 0
  | .binary op a b,v => op.eval (a.evaluate v) (b.evaluate v)
  | .inverse a,v => (a.evaluate v).inverse

def nodes : RationalExpression → ℕ
  | .input _ => 1
  | .zero => 1
  | .binary _ a b => a.nodes+b.nodes+1
  | .inverse a => a.nodes+1

def Below : RationalExpression → ℕ → Prop
  | .input i,B => i<B
  | .zero,_ => True
  | .binary _ a b,B => a.Below B ∧ b.Below B
  | .inverse a,B => a.Below B

theorem nodes_pos (e : RationalExpression) : 0<e.nodes := by cases e <;> simp [nodes]

theorem Below.mono {e : RationalExpression} {B C : ℕ} (he : e.Below B) (hBC : B≤C) : e.Below C := by
  induction e with
  | input i => exact lt_of_lt_of_le he hBC
  | zero => trivial
  | binary op a b ia ib => exact ⟨ia he.1,ib he.2⟩
  | inverse a ih => exact ih he

theorem evaluate_congr (e : RationalExpression) (B : ℕ) (he : e.Below B)
    (v w : ℕ → Parts) (hvw : ∀ i<B, v i=w i) : e.evaluate v=e.evaluate w := by
  induction e with
  | input i => exact hvw i he
  | zero => rfl
  | binary op a b ia ib => simp only [evaluate,ia he.1,ib he.2]
  | inverse a ih => simp only [evaluate,ih he]

def Safe : RationalExpression → (ℕ → Parts) → Prop
  | .input i,v => (v i).Valid
  | .zero,_ => True
  | .binary _ a b,v => a.Safe v ∧ b.Safe v
  | .inverse a,v => a.Safe v ∧ (a.evaluate v).value≠0

theorem Safe.valid {e : RationalExpression} {v : ℕ → Parts} (he : e.Safe v) : (e.evaluate v).Valid := by
  induction e with
  | input i => exact he
  | zero => exact Parts.literal_valid _
  | binary op a b ia ib => exact BinaryOp.eval_valid op (ia he.1) (ib he.2)
  | inverse a _ih => exact Parts.inverse_valid he.2

theorem safe_congr (e : RationalExpression) (B : ℕ) (he : e.Below B)
    (v w : ℕ → Parts) (hvw : ∀ i<B, v i=w i) : e.Safe v ↔ e.Safe w := by
  induction e with
  | input i => exact congrArg Parts.Valid (hvw i he) |>.to_iff
  | zero => rfl
  | binary op a b ia ib => exact and_congr (ia he.1) (ib he.2)
  | inverse a ih =>
    change a.Safe v ∧ _ ↔ a.Safe w ∧ _
    rw [ih he,a.evaluate_congr B he v w hvw]

theorem evaluate_width (e : RationalExpression) (B W : ℕ) (he : e.Below B)
    (v : ℕ → Parts) (hv : ∀ i<B, (v i).Width W) :
    (e.evaluate v).Width (e.nodes*(W+1)) := by
  induction e with
  | input i => simpa only [evaluate,nodes,one_mul] using (hv i he).mono (show W≤W+1 by omega)
  | zero => simpa only [evaluate,nodes,one_mul] using
      (Parts.literal_width RationalWords.width_zero').mono (show 1≤W+1 by omega)
  | binary op a b ia ib =>
    have ha := ia he.1
    have hb := ib he.2
    have hbound : a.nodes*(W+1)+b.nodes*(W+1)+1≤(a.nodes+b.nodes+1)*(W+1) := by nlinarith
    cases op
    · exact (ha.add hb).mono hbound
    · exact (ha.sub hb).mono hbound
    · exact (ha.mul hb).mono hbound
  | inverse a ih =>
    exact (ih he).inverse.mono (by change a.nodes*(W+1)+1≤(a.nodes+1)*(W+1); nlinarith)

def NodeWidths : RationalExpression → ℕ → (ℕ → Parts) → Prop
  | .input i,W,v => (v i).Width W
  | .zero,W,_ => (Parts.literal 0).Width W
  | .binary op a b,W,v => (op.eval (a.evaluate v) (b.evaluate v)).Width W ∧
      a.NodeWidths W v ∧ b.NodeWidths W v
  | .inverse a,W,v => (a.evaluate v).inverse.Width W ∧ a.NodeWidths W v

theorem NodeWidths.result {e : RationalExpression} {W : ℕ} {v : ℕ → Parts}
    (he : e.NodeWidths W v) : (e.evaluate v).Width W := by
  cases e
  · exact he
  · exact he
  · exact he.1
  · exact he.1

theorem NodeWidths.mono {e : RationalExpression} {B C : ℕ} {v : ℕ → Parts}
    (he : e.NodeWidths B v) (hBC : B≤C) : e.NodeWidths C v := by
  induction e with
  | input i => exact Parts.Width.mono he hBC
  | zero => exact Parts.Width.mono he hBC
  | binary op a b ia ib => exact ⟨Parts.Width.mono he.1 hBC,ia he.2.1,ib he.2.2⟩
  | inverse a ih => exact ⟨Parts.Width.mono he.1 hBC,ih he.2⟩

theorem nodeWidths (e : RationalExpression) (B W : ℕ) (he : e.Below B)
    (v : ℕ → Parts) (hv : ∀ i<B, (v i).Width W) : e.NodeWidths (e.nodes*(W+1)) v := by
  induction e with
  | input i => exact evaluate_width _ B W he v hv
  | zero => exact evaluate_width _ B W he v hv
  | binary op a b ia ib =>
    exact ⟨evaluate_width _ B W he v hv,
      (ia he.1).mono (Nat.mul_le_mul_right (W+1) (by simp only [nodes]; omega)),
      (ib he.2).mono (Nat.mul_le_mul_right (W+1) (by simp only [nodes]; omega))⟩
  | inverse a ih => exact ⟨evaluate_width _ B W he v hv,
      (ih he).mono (Nat.mul_le_mul_right (W+1) (by simp only [nodes]; omega))⟩

theorem nodeWidths_congr (e : RationalExpression) (B W : ℕ) (he : e.Below B)
    (v w : ℕ → Parts) (hvw : ∀ i<B, v i=w i) : e.NodeWidths W v ↔ e.NodeWidths W w := by
  induction e with
  | input i => exact congrArg (fun x : Parts => x.Width W) (hvw i he) |>.to_iff
  | zero => rfl
  | binary op a b ia ib =>
    change _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _
    rw [a.evaluate_congr B he.1 v w hvw,b.evaluate_congr B he.2 v w hvw,ia he.1,ib he.2]
  | inverse a ih =>
    change _ ∧ _ ↔ _ ∧ _
    rw [a.evaluate_congr B he v w hvw,ih he]

#print axioms evaluate_width
#print axioms nodeWidths

end RationalExpression
end Maxwell.Continuum.Calibration
