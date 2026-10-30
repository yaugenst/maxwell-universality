import Maxwell.Continuum.CalibrationSupercellCells
import Maxwell.Continuum.CalibrationSupercellRepresentatives
import Maxwell.Continuum.CalibrationSupercellDFT
import Maxwell.Continuum.CalibrationSupercellUnitary
import Maxwell.Continuum.CellGaugeUnitary

/-! The normalized physical supercell embedding. It uses the actual
cell Fourier transform, real Bloch gauge, finite grid transform, and
disjoint spatial cells; the physical normalization is proved, not assumed. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier PeriodicSampling
open scoped InnerProduct

variable (M : ℕ) [NeZero M]

def cellUnitary (j : Grid M) : FiberSpace ≃ₗᵢ[ℂ] CellFieldL2 :=
  CellFourier.unitary.trans
    (CellGauge.realUnitary (fun i => Real.pi*(centeredGrid M (j i) : ℝ)))

omit [NeZero M] in
theorem cellUnitary_apply (j : Grid M) (u : FiberSpace) :
    cellUnitary M j u=antiGauge (momentum M j) (CellFourier.unitary u) := rfl

def gaugedBlocks : BlockSpace M ≃ₗᵢ[ℂ] CellArray M CellFieldL2 :=
  LinearIsometryEquiv.piLpCongrRight 2 (cellUnitary M)

def carrierArrayLinear : CellArray M CellFieldL2 →ₗ[ℂ] CellArray M CellFieldL2 where
  toFun u := WithLp.toLp 2 (fun a => carrier (latticeShift (representative M a)) • u a)
  map_add' u v := by
    apply PiLp.ext
    intro a
    simp only [PiLp.add_apply,smul_add]
  map_smul' c u := by
    apply PiLp.ext
    intro a
    simp only [PiLp.smul_apply,RingHom.id_apply,smul_comm _ c]

def carrierArrayIsometry : CellArray M CellFieldL2 →ₗᵢ[ℂ] CellArray M CellFieldL2 where
  toLinearMap := carrierArrayLinear M
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro a _
    change ‖carrier (latticeShift (representative M a)) • u a‖^2=‖u a‖^2
    rw [norm_smul,carrier_norm,one_mul]

def blockEmbedding : BlockSpace M →ₗᵢ[ℂ] FieldL2 :=
  (cellEmbedding (representative M) (representative_injective M)).comp
    ((carrierArrayIsometry M).comp
      ((gridTransformIsometry M).comp (gaugedBlocks M).toLinearIsometry))

def embedding : FiberSpace →ₗᵢ[ℂ] FieldL2 :=
  (blockEmbedding M).comp (unitary M).toLinearIsometry

def physicalFactor : ℝ := cellFactor*gridFactor M

theorem physicalFactor_pos : 0<physicalFactor M := mul_pos cellFactor_pos (gridFactor_pos M)

theorem physicalFactor_square : physicalFactor M^2*8*(M : ℝ)^3=1 := by
  rw [physicalFactor,mul_pow]
  calc
    cellFactor^2*gridFactor M^2*8*(M : ℝ)^3 =
      (cellFactor^2*8)*(gridFactor M^2*(M : ℝ)^3) := by ring
    _ = 1 := by rw [cellFactor_square,gridFactor_square,one_mul]

theorem blockEmbedding_apply (u : BlockSpace M) :
    blockEmbedding M u=(physicalFactor M : ℂ) •
      ∑ a : Grid M, ∑ j : Grid M,
        cellPhase M j (representative M a) •
          embedLatticeCell (representative M a) (cellUnitary M j (u j)) := by
  change (cellFactor : ℂ) • cellArrayEmbed (representative M)
    (carrierArrayLinear M (gridTransform M (gaugedBlocks M u)))=_
  rw [cellArrayEmbed_apply]
  simp only [carrierArrayLinear,LinearMap.coe_mk,AddHom.coe_mk,
    gridTransform,gridSynthesis,gaugedBlocks,LinearIsometryEquiv.piLpCongrRight_apply,
    map_smul,map_sum,smul_smul,physicalFactor,Complex.ofReal_mul,
    cellPhase,frequency_representative]
  simp only [Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

theorem embedding_apply (u : FiberSpace) :
    embedding M u=blockEmbedding M (unitary M u) := rfl

theorem embedding_norm (u : FiberSpace) : ‖embedding M u‖=‖u‖ :=
  (embedding M).norm_map u

#print axioms blockEmbedding_apply
#print axioms embedding_norm

end Maxwell.Continuum.Calibration.Supercell
