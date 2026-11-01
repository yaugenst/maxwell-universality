import Maxwell.Continuum.ContinuumDecoderSelectors
import Maxwell.Continuum.ContinuumDecoder

/-! Identification of the executed natural selector outputs with the literal
finite-decoder metadata and its exact normalization ratio. -/
noncomputable section
namespace Maxwell.Continuum.DecoderSelectors
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Logical RealizationParameters
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision

 theorem messageRangeBits_natural (m N D : ℕ) :
    FiniteAuxiliary.messageRangeBits (Parameters.inverseBudget m N (1/(D:ℚ))) m=
      Nat.clog 2 (512*m^2*N*D):=by
  unfold FiniteAuxiliary.messageRangeBits Parameters.inverseBudget Parameters.rationalUpperBits
  have h : (8*(64*(m:ℚ)*N/(1/(D:ℚ)))*m)=((512*m^2*N*D:ℕ):ℚ):=by
    push_cast
    simp only [one_div,div_inv_eq_mul]
    ring
  rw [h,Nat.ceil_natCast]

structure Inputs (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) (v : ℕ→ℕ) : Prop where
  nonzeros : v 501=S.nnz
  spectral : v 2245=count p S hm
  radius_eq : (1:ℚ)/(v 2237)=radius p S hm
  length_eq : v 2221=length p S hm
  buffer_eq : v 2244=bufferSteps p S hm
  span : ∀j:Fin 3,v (2240+j.val)=Parameters.stageSpan (Parameters.sourceInput p S hm)
    MasterConstants.exponent (stage p S hm) j
  moment : v 4428=momentPrecision p S
  sourceScale : (v 506:ℚ)/(v 507)=Normalization.sourceScale S
  matrixScale : (v 504:ℚ)/(v 505)=Normalization.matrixScale S

variable {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz} {v : ℕ→ℕ}

theorem Inputs.integerBits (h : Inputs p S hm v) : result v 4701=(gridReportFormat p S hm).integerBits:=by
  rw [result_log,h.nonzeros,h.spectral]
  change _=FiniteAuxiliary.messageRangeBits (Parameters.inverseBudget S.nnz (count p S hm) (radius p S hm)) S.nnz+2
  rw [←h.radius_eq,messageRangeBits_natural]

theorem Inputs.fractionalBits (h : Inputs p S hm v) : result v 4702=(gridReportFormat p S hm).fractionalBits:=by
  rw [result_kept v 4702 (by decide) (by decide),(values v).2.2.1,h.moment]
  rfl

theorem Inputs.sides (h : Inputs p S hm v) (j : Fin 3) : result v (4704+j.val)=gridSide p S hm j:=by
  have data := (values v).2.2.2
  have side : value v (4704+j.val)=2*(v (2240+j.val)+v 2221+v 2221*v 2244+4)+1:=by
    fin_cases j
    · exact data.1
    · exact data.2.1
    · exact data.2.2.1
  rw [result_kept v (4704+j.val) (by have := j.isLt;omega) (by have := j.isLt;omega),side,
    h.span,h.length_eq,h.buffer_eq]
  rfl

theorem Inputs.samples (h : Inputs p S hm v) : result v 4703=gridCount p S hm:=by
  rw [result_kept v 4703 (by decide) (by decide),(values v).2.2.2.2.2.2.1]
  rw [←result_kept v 4704 (by decide) (by decide),←result_kept v 4705 (by decide) (by decide),
    ←result_kept v 4706 (by decide) (by decide)]
  exact congrArg₂ (·*·) (h.sides 0) (congrArg₂ (·*·) (h.sides 1) (h.sides 2))

theorem Inputs.normalization (h : Inputs p S hm v) :
    (result v 4707:ℚ)/(result v 4708)=normalizationScale S:=by
  rw [result_kept v 4707 (by decide) (by decide),result_kept v 4708 (by decide) (by decide),
    (values v).2.2.2.2.2.2.2.1,(values v).2.2.2.2.2.2.2.2]
  unfold normalizationScale
  rw [←h.sourceScale,←h.matrixScale]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

#print axioms Inputs.integerBits
#print axioms Inputs.samples
#print axioms Inputs.normalization
end Maxwell.Continuum.DecoderSelectors
