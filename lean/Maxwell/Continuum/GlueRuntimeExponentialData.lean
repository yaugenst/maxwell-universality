import Maxwell.Continuum.GlueRuntimeComparison
import Maxwell.Continuum.RationalTaylorRuntimeStep

/-! Literal reciprocal input and output channels for the runtime glue
exponential. These are the same finite Taylor centers as the analytic encoder. -/
namespace Maxwell.Continuum.GlueMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def preparedValues (a b N : ℕ) : ℕ→ℕ := NatAssign.values GlueMachine.prepareExp (comparisonValues a b N)
def preparedWidth (W : ℕ) : ℕ := 2^20*(W+1)
def expResult (a b N : ℕ) : RationalDataflow.Parts :=
  ⟨numerator b a (fun k => (negativeSigns k).positive) (GlueMachine.order N),
   numerator b a (fun k => (negativeSigns k).negative) (GlueMachine.order N),
   denominator a (GlueMachine.order N)⟩
def resultWidth (N W : ℕ) : ℕ := RationalTaylor.width (GlueMachine.order N) (preparedWidth W)+1

theorem preparedValues_core (a b N i : ℕ) (hi : i∈GlueMachine.ids) :
    preparedValues a b N i=GlueMachine.preparedValues a b N i := by
  simp only [preparedValues,GlueMachine.preparedValues,GlueMachine.prepareExp,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]
  simp (disch := decide) only [Function.update_self,Function.update_of_ne]
  simp only [Function.update_apply,comparisonValues_core a b N i hi,
    comparisonValues_core a b N 600 (by decide),comparisonValues_core a b N 601 (by decide)]

theorem preparedValues_inputs (a b N : ℕ) : preparedValues a b N 600=b ∧ preparedValues a b N 601=a := by
  rw [preparedValues_core a b N 600 (by decide),preparedValues_core a b N 601 (by decide)]
  exact GlueMachine.prepared_inputs a b N

theorem preparedValues_saved (a b N : ℕ) :
    preparedValues a b N 640=N ∧ preparedValues a b N 641=GlueMachine.order N ∧ preparedValues a b N 607=0 := by
  simpa [preparedValues,GlueMachine.prepareExp,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value] using comparisonValues_saved a b N

theorem prepareExp_valid : ∀i∈GlueMachine.prepareExp,i.Valid ids := by
  simp [GlueMachine.prepareExp,NatAssign.Instruction.Valid,ids,GlueMachine.ids,
    SelectedParameters.Compare.ids,GlueMachine.extra,RationalTaylor.ids]

theorem preparedValues_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W) (i : ℕ) (hi : i∈ids) :
    (preparedValues a b N i).bits.length≤preparedWidth W := by
  have hh := NatAssign.values_width_bound ids GlueMachine.prepareExp prepareExp_valid
    (comparisonValues a b N) (setupWidth W)
    (comparisonValues_width a b N W ha hb hN hW)
    (by simp [GlueMachine.prepareExp,NatAssign.Instruction.literalWidth]) i hi
  have hlen : GlueMachine.prepareExp.length=4 := rfl
  rw [hlen] at hh
  exact ((Nat.le_succ _).trans hh).trans (by unfold preparedWidth setupWidth;omega)

theorem expResult_valid (a b N : ℕ) (ha : 0<a) : (expResult a b N).Valid :=
  denominator_pos ha _

theorem expResult_value (a b N : ℕ) (ha : 0<a) :
    (expResult a b N).value=(Maxwell.Certificate.Elementary.expApprox (-((b:ℚ)/a)) (N+1) N).center := by
  symm
  exact negative_expApprox_center b a ha (N+1) N

theorem expResult_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) :
    (expResult a b N).Width (resultWidth N W) := by
  have hW : W≤preparedWidth W := by unfold preparedWidth;omega
  exact ⟨(numerator_bits b a _ (GlueMachine.order N) (preparedWidth W)
    (hb.trans hW) (ha.trans hW) _ le_rfl).trans (Nat.le_succ _),
    (numerator_bits b a _ (GlueMachine.order N) (preparedWidth W)
      (hb.trans hW) (ha.trans hW) _ le_rfl).trans (Nat.le_succ _),
    (denominator_bits a (GlueMachine.order N) (GlueMachine.order N) (preparedWidth W)
      le_rfl (ha.trans hW)).trans (Nat.le_succ _)⟩

theorem prepareExp_executes (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (comparisonValues a b N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape (NatAssign.code GlueMachine.prepareExp) cost s t ∧
      cost≤2^50*(setupWidth W+2)^2 ∧ NatAssign.Bank ids (preparedValues a b N) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,ex,hcost,bt,zt,ft⟩ := NatAssign.executes ids ids_ge GlueMachine.prepareExp prepareExp_valid
    (comparisonValues a b N) input tape s hs hz
  have hp := NatAssign.price_bound ids GlueMachine.prepareExp prepareExp_valid
    (comparisonValues a b N) (setupWidth W) (comparisonValues_width a b N W ha hb hN hW)
    (by simp [GlueMachine.prepareExp,NatAssign.Instruction.literalWidth])
  have hlen : GlueMachine.prepareExp.length=4 := rfl
  rw [hlen] at hp
  refine ⟨cost,t,ex,hcost.trans (hp.trans (Nat.mul_le_mul_right _ (by norm_num))),bt,zt,?_⟩
  apply ft.mono
  decide

#print axioms expResult_value
#print axioms prepareExp_executes
end Maxwell.Continuum.GlueMachine.Runtime
