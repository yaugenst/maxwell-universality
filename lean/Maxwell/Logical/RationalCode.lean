import Maxwell.Logical.CompilerAlphabet
import Maxwell.Logical.SquareSystem

/-! A finite rational gate program emitted by the same allocation recursion
as the real circuit. Its interpretation is exactly the compiled circuit,
with no choice of a rational approximation after compilation. -/

namespace Maxwell.Logical

inductive RationalCode (n : ℕ) : ℕ → Type where
  | input : RationalCode n n
  | zero {d : ℕ} (prior : RationalCode n d) : RationalCode n (d + 1)
  | scale {d : ℕ} (prior : RationalCode n d) (parent : Fin d) (weight : ℚ) :
      RationalCode n (d + 1)
  | add {d : ℕ} (prior : RationalCode n d) (left right : Fin d) : RationalCode n (d + 1)

namespace RationalCode

def realify {n d : ℕ} : RationalCode n d → Circuit n d
  | .input => .input
  | .zero c => c.realify.append 0
  | .scale c p w => c.realify.scaledGate p w
  | .add c l r => c.realify.additionGate l r

def residual {n d : ℕ} : RationalCode n d → (Fin d → ℚ) → Fin d → ℚ
  | .input, state => state
  | .zero c, state => Fin.snoc (c.residual (fun i => state i.castSucc)) (state (Fin.last _))
  | .scale c p w, state =>
      Fin.snoc (c.residual (fun i => state i.castSucc)) (state (Fin.last _) - w * state p.castSucc)
  | .add c l r, state => Fin.snoc (c.residual (fun i => state i.castSucc))
      (state (Fin.last _) - (state l.castSucc + state r.castSucc))

theorem residual_cast {n d : ℕ} (c : RationalCode n d) (state : Fin d → ℚ) (i : Fin d) :
    (c.residual state i : ℝ) = c.realify.residual 0 (fun j => (state j : ℝ)) i := by
  induction c with
  | input => simp [residual, realify, Circuit.residual]
  | @zero d c ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [residual, realify, Circuit.residual]
      · simpa [residual, realify, Circuit.residual] using ih (fun k => state k.castSucc) j
  | @scale d c p w ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [residual, realify, Circuit.residual, Circuit.scaledGate]
      · simpa [residual, realify, Circuit.residual, Circuit.scaledGate] using
          ih (fun k => state k.castSucc) j
  | @add d c l r ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [residual, realify, Circuit.residual, Circuit.additionGate,
          add_mul, Finset.sum_add_distrib]
      · simpa [residual, realify, Circuit.residual, Circuit.additionGate] using
          ih (fun k => state k.castSucc) j

def equationMatrix {n d : ℕ} (c : RationalCode n d) : Matrix (Fin d) (Fin d) ℚ :=
  fun i j => c.residual (Pi.single j 1) i

theorem equationMatrix_cast {n d : ℕ} (c : RationalCode n d) (i j : Fin d) :
    (c.equationMatrix i j : ℝ) = c.realify.equationMatrix i j := by
  rw [equationMatrix, c.residual_cast]
  congr 2
  funext k
  by_cases h : k = j <;> simp [h]

def squareMatrix {n d : ℕ} (c : RationalCode n d) (output : Fin n → Fin d) :
    Matrix (Fin d) (Fin d) ℚ := fun i j =>
  if h : i.val < n then if output ⟨i.val, h⟩ = j then 1 else 0 else c.equationMatrix i j

theorem squareMatrix_cast {n d : ℕ} (c : RationalCode n d)
    (output : Fin n → Fin d) (i j : Fin d) :
    (c.squareMatrix output i j : ℝ) = (c.realify.squareMap output).toMatrix' i j := by
  by_cases h : i.val < n
  · let k : Fin n := ⟨i.val, h⟩
    have hk : c.realify.inputIndex k = i := Fin.ext (c.realify.inputIndex_value k)
    rw [LinearMap.toMatrix'_apply, ← hk, Circuit.squareMap_input]
    simp only [squareMatrix, Circuit.inputIndex_value, h, ↓reduceDIte, Pi.single_apply, k]
    split_ifs <;> norm_num
  · rw [LinearMap.toMatrix'_apply, Circuit.squareMap_noninput _ _ _ _ (Nat.le_of_not_gt h)]
    simp only [squareMatrix, h, ↓reduceDIte]
    exact c.equationMatrix_cast i j

end RationalCode

structure RationalRealization {n d : ℕ} (c : Circuit n d) where
  code : RationalCode n d
  correct : code.realify = c

namespace RationalRealization

def input (n : ℕ) : RationalRealization (.input : Circuit n n) := ⟨.input, rfl⟩

def zero {n d : ℕ} {c : Circuit n d} (r : RationalRealization c) :
    RationalRealization (c.append 0) := ⟨.zero r.code, by simp [RationalCode.realify, r.correct]⟩

def scale {n d : ℕ} {c : Circuit n d} (r : RationalRealization c) (p : Fin d) (w : ℚ) :
    RationalRealization (c.scaledGate p w) :=
  ⟨.scale r.code p w, by simp [RationalCode.realify, r.correct]⟩

def copy {n d : ℕ} {c : Circuit n d} (r : RationalRealization c) (p : Fin d) :
    RationalRealization (c.copyGate p) :=
  ⟨.scale r.code p 1, by simp [RationalCode.realify, r.correct, Circuit.copyGate, Circuit.scaledGate]⟩

def add {n d : ℕ} {c : Circuit n d} (r : RationalRealization c) (l r' : Fin d) :
    RationalRealization (c.additionGate l r') :=
  ⟨.add r.code l r', by simp [RationalCode.realify, r.correct]⟩

end RationalRealization

def compileExpression_rational {n d v : ℕ} (e : Expression v)
    (prior : Circuit n d) (ids : Fin v → Fin d) (r : RationalRealization prior) :
    RationalRealization (compileExpression e prior ids).circuit :=
  match e with
  | .var _ => r
  | .zero => r.zero
  | .scale w child =>
      (compileExpression_rational child prior ids r).scale (compileExpression child prior ids).output w
  | .add left right =>
      let l := compileExpression left prior ids
      let cr := compileExpression right l.circuit (fun i => Fin.castLE l.size_le (ids i))
      let lr := compileExpression_rational left prior ids r
      let rr := compileExpression_rational right l.circuit (fun i => Fin.castLE l.size_le (ids i)) lr
      rr.add (Fin.castLE cr.size_le l.output) cr.output

def compileForest_rational {n d v : ℕ} (es : List (Expression v))
    (prior : Circuit n d) (ids : Fin v → Fin d) (r : RationalRealization prior) :
    RationalRealization (compileForest es prior ids).circuit :=
  match es with
  | [] => r
  | e :: es =>
      let h := compileExpression e prior ids
      compileForest_rational es h.circuit (fun i => Fin.castLE h.size_le (ids i))
        (compileExpression_rational e prior ids r)

def CopyBank.splitRoot_rational {n : ℕ} (bank : CopyBank n)
    (r : RationalRealization bank.circuit) (i : Fin n) :
    RationalRealization (bank.splitRoot i).circuit :=
  (r.copy (bank.root i)).copy (bank.root i).castSucc

def CopyBank.allocate_rational {n : ℕ} (requests : List (Fin n))
    (bank : CopyBank n) (r : RationalRealization bank.circuit) :
    RationalRealization (bank.allocate requests).bank.circuit :=
  match requests with
  | [] => r
  | i :: rest => CopyBank.allocate_rational rest (bank.splitRoot i) (bank.splitRoot_rational r i)

def compileCopiedForest_rational {n : ℕ} (rows : List (Expression n)) :
    RationalRealization (compileCopiedForest rows).circuit :=
  compileForest_rational (linearizedRows rows) (forestCopies rows).bank.circuit (copiedForestInputs rows)
    (CopyBank.allocate_rational (List.ofFn (forestSources rows)) (CopyBank.initial n)
      (RationalRealization.input n))

def sourceCircuit_rational (S : Source.SparseSystem) (precision : ℕ) :
    RationalRealization (sourceCircuit S precision).circuit :=
  compileCopiedForest_rational ((Normalization.sourceRows S precision).map rowExpression)

end Maxwell.Logical
