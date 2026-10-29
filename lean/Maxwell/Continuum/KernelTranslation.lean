import Maxwell.Continuum.WeakCurl
import Maxwell.Continuum.KernelCompact
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Translation of a genuine L² kernel and compact weighted convolution.
Continuity of translation is obtained from the proved continuity of Lp
composition by measure-preserving maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.KernelIntegral

open MeasureTheory
open scoped ENNReal

def shift (y : Space) : ScalarL2 →ₗᵢ[ℂ] ScalarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : Space => x + -y)
    (measurePreserving_add_right volume (-y))

theorem shift_ae (y : Space) (u : ScalarL2) :
    shift y u =ᵐ[volume] fun x => u (x - y) := by
  have h := Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume (-y))
  filter_upwards [h] with x hx
  change Lp.compMeasurePreserving (fun x => x + -y)
    (measurePreserving_add_right volume (-y)) u x = u (x - y)
  exact hx

theorem shift_continuous (u : ScalarL2) : Continuous (fun y => shift y u) := by
  let g : Space → C(Space, Space) := fun y => ⟨fun x => x + -y, by fun_prop⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_snd.add continuous_fst.neg
  exact continuous_const.compMeasurePreservingLp hg
    (fun y => measurePreserving_add_right volume (-y)) (by norm_num)

def column (w : Space → ℂ) (u : ScalarL2) (y : Space) : ScalarL2 := w y • shift y u

theorem column_norm (w : Space → ℂ) (u : ScalarL2) (y : Space) :
    ‖column w u y‖ = ‖w y‖ * ‖u‖ := by
  rw [column, norm_smul, (shift y).norm_map]

theorem column_memLp (w : Space → ℂ) (hw : MemLp w 2 volume) (u : ScalarL2) :
    MemLp (column w u) 2 volume := by
  apply hw.of_le_mul (hw.aestronglyMeasurable.smul
    (shift_continuous u).aestronglyMeasurable) (c := ‖u‖)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖column w u y‖ ≤ ‖u‖ * ‖w y‖
    rw [column_norm, mul_comm])

def columnL2 (w : Space → ℂ) (hw : MemLp w 2 volume) (u : ScalarL2) :
    Lp ScalarL2 2 (volume : Measure Space) := (column_memLp w hw u).toLp _

theorem columnL2_ae (w : Space → ℂ) (hw : MemLp w 2 volume) (u : ScalarL2) :
    columnL2 w hw u =ᵐ[volume] column w u := MemLp.coeFn_toLp _

def weightedConvolution (w : Space → ℂ) (hw : MemLp w 2 volume) (u : ScalarL2) :
    ScalarL2 →L[ℂ] ScalarL2 := operator volume (columnL2 w hw u)

theorem weightedConvolution_apply (w : Space → ℂ) (hw : MemLp w 2 volume)
    (u f : ScalarL2) : weightedConvolution w hw u f =
      ∫ y : Space, (f y * w y) • shift y u := by
  rw [weightedConvolution, operator_apply]
  apply integral_congr_ae
  filter_upwards [columnL2_ae w hw u] with y hy
  rw [hy, column, smul_smul]

theorem weightedConvolution_integrable (w : Space → ℂ) (hw : MemLp w 2 volume)
    (u f : ScalarL2) : Integrable (fun y : Space => (f y * w y) • shift y u) := by
  apply (integrable_apply volume (columnL2 w hw u) f).congr
  filter_upwards [columnL2_ae w hw u] with y hy
  rw [hy, column, smul_smul]

theorem weightedConvolution_compact (w : Space → ℂ) (hw : MemLp w 2 volume)
    (u : ScalarL2) : IsCompactOperator (weightedConvolution w hw u) :=
  operator_compact volume _

theorem weightedConvolution_inner (w : Space → ℂ) (hw : MemLp w 2 volume)
    (u f φ : ScalarL2) : inner ℂ φ (weightedConvolution w hw u f) =
      ∫ y : Space, (f y * w y) * inner ℂ φ (shift y u) := by
  rw [weightedConvolution_apply, ← integral_inner (weightedConvolution_integrable w hw u f)]
  simp only [inner_smul_right]

end Maxwell.Continuum.KernelIntegral
