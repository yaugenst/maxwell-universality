import Maxwell.Certificate.GlobalDerivativeAction
import Maxwell.Certificate.GlobalDerivativeSound
import Maxwell.Certificate.DyadicKernelActionSound
import Mathlib.Analysis.Real.Pi.Bounds

set_option maxHeartbeats 1000000

namespace Maxwell.Certificate.DyadicKernel.DerivativeAction
open Action FourierBinding GlobalDerivative Maxwell.Spectral
open Maxwell.Spectral.PeriodicYee Maxwell.Spectral.PrimitiveYee
noncomputable section

theorem theta_contains : theta.toDyadic.Contains 52 (Complex.I*(BoxSymbols.phaseScale:ℂ)) := by
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  constructor
  · norm_num [theta,Rectangle.toDyadic]
  · norm_num [theta,Rectangle.toDyadic,BoxSymbols.phaseScale]
    rw [abs_le]
    constructor <;> linarith

theorem projectorScale_contains : projectorScale.toDyadic.Contains 52 (1/32:ℂ) := by
  norm_num [projectorScale,Rectangle.toDyadic,DyadicRectangle.Contains]

theorem symbols_contains (axis : Fin 3) (d : VectorField) (c : Momentum)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j)) (r : Action.Cell) (j : Fin 3) :
    (toRectField (symbols axis d) r j).Contains 52 (axisSymbol c axis r j) := by
  change ((VectorField.build _).get r).toVector j |>.Contains 52 _
  rw [VectorField.get_build]
  exact Derivative.axisRound_contains (hd r) theta_contains j

theorem materialApply_contains (material field : VectorField) (m : Cell20 → ℝ)
    (u : FourierSpace) (hmvalid : materialValid material = true)
    (hm : ∀ r j, (toRectField material r j).Contains 52 (edgeAverage m (j,r):ℂ))
    (hu : Action.Contains field u) : Action.Contains (materialApply material field) (materialField m u) := by
  have hi := Action.inverse_contains field u hu
  have hs := Action.divideMaterial_contains (inverse field) material _ (edgeAverage m) hmvalid hi hm
  have hf := Action.forward_contains (divideMaterial (inverse field) material) _ hs
  intro r j
  rw [materialField_apply]
  exact hf r j

theorem projectionPrimeRound_getD {d dp field : Triple} {lap : Rectangle}
    (hp : 0 < lap.re-(lap.radius:ℤ)) :
    Derivative.projectionPrimeRound 52 d dp field lap =
      some ((Derivative.projectionPrimeRound 52 d dp field lap).getD zeroTriple) := by
  cases he : divRound 52 (dotTriple 52 dp field) lap with
  | none =>
    have hh := divRound_getD_of_pos 52 (dotTriple 52 dp field) lap hp
    rw [he] at hh
    cases hh
  | some z => simp [Derivative.projectionPrimeRound,he]

def Result.Contains (a : Result) (m : Cell20 → ℝ) (c : Momentum) (axis : Fin 3)
    (u : FourierSpace) : Prop :=
  Action.Contains a.curl (curlPrimeField c axis u) ∧
  Action.Contains a.weighted (weightedPrimeField m c axis u) ∧
  Action.Contains a.magnetic (magneticPrimeField m c axis u) ∧
  Action.Contains a.projection (projectionPrimeField c axis u) ∧
  Action.Contains a.auxiliary (auxiliaryPrimeField m c axis u)

attribute [local irreducible] Action.inverse Action.forward Action.divideMaterial materialApply Action.adjointCurl VectorField.build symbols projectionPrime

theorem compute_contains (axis : Fin 3) (d material field weighted : VectorField)
    (m : Cell20 → ℝ) (c : Momentum) (u : FourierSpace)
    (hdvalid : projectionValid d = true) (hmvalid : materialValid material = true)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j))
    (hm : ∀ r j, (toRectField material r j).Contains 52 (edgeAverage m (j,r):ℂ))
    (hu : Action.Contains field u)
    (hw : Action.Contains weighted (GlobalCenter.weightedField m c u)) :
    (compute axis d material field weighted).Contains m c axis u := by
  let dp := symbols axis d
  have hp := symbols_contains axis d c hd
  have hc : Action.Contains (adjointCurl dp field) (curlPrimeField c axis u) := by
    intro r j
    rw [toRectField,Action.adjointCurl,VectorField.get_build]
    exact Derivative.curlPrimeRound_contains_field (c := c) (a := axis) (f := r) (u := u)
      (hp r) (hu r) j
  have hwp : Action.Contains (materialApply material (adjointCurl dp field))
      (weightedPrimeField m c axis u) :=
    materialApply_contains material (adjointCurl dp field) m _ hmvalid hm hc
  let wp := materialApply material (adjointCurl dp field)
  have hmag : Action.Contains (VectorField.build fun r => Derivative.magneticPrimeRound 52
      (d.get r) (dp.get r) (weighted.get r) (wp.get r)) (magneticPrimeField m c axis u) := by
    intro r j
    rw [toRectField,VectorField.get_build]
    exact Derivative.magneticPrimeRound_contains_field (material := m) (c := c) (a := axis)
      (f := r) (u := u) (hd r) (hp r) (hw r) (hwp r) j
  have hproj : Action.Contains (projectionPrime d dp field) (projectionPrimeField c axis u) := by
    intro r j
    rw [toRectField,projectionPrime,VectorField.get_build]
    exact Derivative.projectionPrimeRound_contains_field (c := c) (a := axis) (f := r) (u := u)
      (projectionPrimeRound_getD (projectionValid_pos hdvalid r))
      (hd r) (hp r) (hu r) (laplacianRound_contains (hd r)) j
  refine ⟨hc,hwp,hmag,hproj,?_⟩
  intro r j
  change ((VectorField.build _).get r).toVector j |>.Contains 52 _
  rw [VectorField.get_build]
  exact Derivative.auxiliaryPrimeRound_contains_field (material := m) (c := c) (a := axis)
    (f := r) (u := u) (hmag r) projectorScale_contains (hproj r) j

end
end Maxwell.Certificate.DyadicKernel.DerivativeAction
