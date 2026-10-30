import Maxwell.Continuum.RationalDataflowFixedWidths
import Maxwell.Continuum.FourierTensorEncoding

/-! A fixed Boolean-machine arithmetic body computes one literal real
tensor summand.  The inputs are the cached integer numerators of the
Fourier amplitude and the three one-dimensional wave coefficients. -/

namespace Maxwell.Continuum.Profile.TensorMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def ids : Finset ℕ := Finset.range 17

def instructions : List Instruction :=
  [.binary .mul 10 3 5,
   .binary .mul 11 4 6,
   .binary .sub 12 10 11,
   .binary .mul 10 3 6,
   .binary .mul 11 4 5,
   .binary .add 13 10 11,
   .binary .mul 10 12 7,
   .binary .mul 11 13 8,
   .binary .sub 14 10 11,
   .binary .mul 10 12 8,
   .binary .mul 11 13 7,
   .binary .add 15 10 11,
   .binary .mul 10 1 14,
   .binary .mul 11 2 15,
   .binary .sub 16 10 11,
   .binary .add 0 0 16]

def body : Control := Control.done.prepend instructions

def realProduct (a b c d : ℚ×ℚ) : ℚ :=
  a.1*((b.1*c.1-b.2*c.2)*d.1-(b.1*c.2+b.2*c.1)*d.2)-
    a.2*((b.1*c.1-b.2*c.2)*d.2+(b.1*c.2+b.2*c.1)*d.1)

theorem body_steps : body.steps=16 := rfl

theorem body_valid : body.Valid ids := by
  simp [body,instructions,Control.prepend,Control.Valid,Instruction.Valid,ids]

theorem body_literals (W : ℕ) : body.LiteralsFit W := by trivial

theorem body_admissible (v : ℕ→Parts) : body.AdmissibleTrace v := by trivial

theorem body_rational (v : ℕ→ℚ) :
    body.rationalEvaluate v 0=v 0+realProduct (v 1,v 2) (v 3,v 4) (v 5,v 6) (v 7,v 8) := by
  simp [body,instructions,Control.prepend,Control.rationalEvaluate,
    Instruction.rationalUpdate,realProduct]

theorem body_value (v : ℕ→Parts) (hg : Good ids v) :
    (body.evaluate v 0).value=(v 0).value+
      realProduct ((v 1).value,(v 2).value) ((v 3).value,(v 4).value)
        ((v 5).value,(v 6).value) ((v 7).value,(v 8).value) := by
  have h := congrFun (body.evaluate_value ids body_valid v hg (body_admissible v)) 0
  exact h.trans (body_rational (valueBank v))

theorem realProduct_numerators {B P : ℕ} (a : ComplexDyadic B) (b c d : ComplexDyadic P) :
    realProduct ((a.1.numerator:ℚ),(a.2.numerator:ℚ))
      ((b.1.numerator:ℚ),(b.2.numerator:ℚ))
      ((c.1.numerator:ℚ),(c.2.numerator:ℚ))
      ((d.1.numerator:ℚ),(d.2.numerator:ℚ))=
      ((complexDyadicMul a (complexDyadicMul (complexDyadicMul b c) d)).1.numerator : ℚ) := by
  simp only [realProduct,complexDyadicMul]
  push_cast
  ring

def workWidth (W : ℕ) : ℕ := 2^16*(W+1)

def costBound (W : ℕ) : ℕ := 16*operationCost (workWidth W)+1

theorem body_computes (v : ℕ→Parts) (W : ℕ) (hw : WidthBank ids W v) (hg : Good ids v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready ids v s) :
    ∃ (cost : ℕ) (t : Store) (output : ℕ→Parts),
      (runPriced (body.code.compile.next input tape) (costBound W+1) s.val).finished=
        some (t.place body.code.size) ∧
      (runPriced (body.code.compile.next input tape) (costBound W+1) s.val).instructions=cost ∧
      cost≤costBound W ∧ Ready ids output t ∧ Good ids output ∧
      (output 0).value=(v 0).value+
        realProduct ((v 1).value,(v 2).value) ((v 3).value,(v 4).value)
          ((v 5).value,(v 6).value) ((v 7).value,(v 8).value) := by
  have ht := body.automatic_widthTrace ids body_valid v W hw (body_literals W)
  rw [body_steps] at ht
  obtain ⟨cost,t,output,he,hc,hb,ho,hg',hv⟩ :=
    body.computes ids body_valid v (workWidth W) ht hg (body_admissible v) input tape s hs
  refine ⟨cost,t,output,?_,?_,?_,ho,hg',?_⟩
  · simpa only [body_steps,costBound,Nat.add_assoc] using he
  · simpa only [body_steps,costBound,Nat.add_assoc] using hc
  · simpa only [body_steps,costBound] using hb
  · exact (congrFun hv 0).trans (body_rational (valueBank v))

theorem costBound_polynomial (W : ℕ) : costBound W≤2^140*(W+1)^2 := by
  have hw : workWidth W+3≤(2^16+3)*(W+1) := by unfold workWidth; nlinarith
  have hp := Nat.pow_le_pow_left hw 2
  have h1 : 1≤(W+1)^2 := one_le_pow₀ (by omega)
  unfold costBound operationCost
  nlinarith only [hp,h1]

#print axioms body_computes
#print axioms realProduct_numerators
#print axioms costBound_polynomial

end Maxwell.Continuum.Profile.TensorMachine
