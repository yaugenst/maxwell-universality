import Maxwell.Continuum.ParameterSourceResources
import Maxwell.Composition.SourceRecordCounts

/-! Executable source-side specialization. Counts come from the actual
emitted terminal and edge lists. Integer promise exponents and the fixed
master exponent remain explicit arguments, so no enormous closed numeral
must be expanded by code generation. -/

namespace Maxwell.Continuum.Parameters
open Maxwell.Composition Maxwell.Realization

def encodedInput (κ η : ℕ) (S : Source.SparseSystem) (hm : 0 < S.nnz) : Input :=
  let n := binaryCoefficientPrecision S.nnz κ η
  { m := S.nnz
    J := (SourceVertexList.entries S n).length+(SourceEdgeList.edges S n).length
    span := fun _ => 2^54*129*PhysicalParameters.routingSide S n
    K := PhysicalParameters.logicalInverseBudget S n (logicalScale S.nnz κ)
    epsilon := PhysicalAccuracy.epsilon S n (logicalAccuracy S.nnz η)/16
    m_pos := hm
    K_pos := zero_lt_one.trans_le (PhysicalParameters.logicalInverseBudget_ge_one
      S n _ (logicalScale_ge_one S.nnz κ hm))
    epsilon_pos := div_pos (PhysicalAccuracy.epsilon_pos S n _ (logicalAccuracy_pos S.nnz η hm))
      (by norm_num) }

private theorem input_eq_of_fields {I J : Input} (hm : I.m = J.m) (hn : I.J = J.J)
    (hs : I.span = J.span) (hK : I.K = J.K) (hε : I.epsilon = J.epsilon) : I = J := by
  cases I
  cases J
  dsimp only at hm hn hs hK hε
  subst_vars
  rfl

theorem encodedInput_eq (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    encodedInput ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ S hm = sourceInput p S hm := by
  apply input_eq_of_fields (I := encodedInput ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ S hm)
    (J := sourceInput p S hm) rfl _ rfl rfl rfl
  exact SourceRecordCounts.defects_length S _

def encode (κ η e : ℕ) (S : Source.SparseSystem) (hm : 0 < S.nnz) : ℕ :=
  selectedOuterExponent (encodedInput κ η S hm) e (minimumLengthExponent e)
    (inputLog S.nnz) (inputLog_pos S.nnz)

theorem encode_spec (κ η e : ℕ) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    let I := encodedInput κ η S hm
    let k := encode κ η e S hm
    SpacingTest e (stageLength k) I.K I.epsilon (stageSpacing I e k) ∧
    BufferTest e I.J I.m (stageLength k) (stageSpacing I e k) (stageSpan I e k)
      I.K I.epsilon (stageTau I e k) (stageBuffer I e k) ∧
    LeakageTest I e k ∧ TailTest I e k := by
  refine ⟨selectedSpacing_spec _ _ _ _ _ _, stageBuffer_spec _ _ _, ?_⟩
  exact selectedOuter_spec _ _ _ _ _

theorem encode_eq_sourceStage (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    encode ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ MasterConstants.exponent S hm =
      sourceStage p S hm := by
  unfold encode sourceStage
  rw [encodedInput_eq]

#print axioms encodedInput_eq
#print axioms encode_spec
#print axioms encode_eq_sourceStage

end Maxwell.Continuum.Parameters
