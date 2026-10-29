import Maxwell.Certificate.DyadicKernelAction
import Maxwell.Certificate.DyadicKernelVectorSound
import Maxwell.Certificate.DyadicKernelSchurEvalSound
import Maxwell.Certificate.GlobalFFTComputed.ConstantsSound
import Maxwell.Certificate.GlobalCenter
import Maxwell.Certificate.FourierCoercivity

namespace Maxwell.Certificate.DyadicKernel.Action
open FourierBinding Maxwell.Spectral.PrimitiveYee Matrix
open Maxwell.Spectral.PeriodicYee (Momentum Cell20)
noncomputable section

def toRectField (a : VectorField) : GlobalCenter.RectField := fun r j => (a.get r).toVector j
def Contains (a : VectorField) (u : Electric → ℂ) : Prop :=
  ∀ r j, (toRectField a r j).Contains 52 (u (j,r))

@[simp] theorem VectorField.get_build (a : Cell → Triple) (r : Cell) :
    (VectorField.build a).get r = a r := by
  simp [VectorField.get, VectorField.build, FFT.get_build]

theorem VectorField.get_component (a : VectorField) (r : Cell) (j : Fin 3) :
    (a.get r).get j = FFT.get (a.component j) r.1 r.2.1 r.2.2 := by
  fin_cases j <;> rfl

@[simp] theorem VectorField.map_component (f : FFT.Field → FFT.Field) (a : VectorField) (j : Fin 3) :
    (a.map f).component j = f (a.component j) := by fin_cases j <;> rfl

theorem toField_component (a : VectorField) (j : Fin 3) (r : Cell) :
    FFT.toField (a.component j) r = toRectField a r j := by
  rw [toRectField, ← Triple.toDyadic_get, VectorField.get_component]
  rfl

theorem projectRound_getD {p : ℕ} {d raw : Triple} {lap : Rectangle}
    (hp : 0 < lap.re-(lap.radius : ℤ)) :
    projectRound p d raw lap = some ((projectRound p d raw lap).getD zeroTriple) := by
  cases he : divRound p (dotTriple p d raw) lap with
  | none =>
      have hh := divRound_getD_of_pos p (dotTriple p d raw) lap hp
      rw [he] at hh
      cases hh
  | some quotient => simp [projectRound, he]

theorem divideTriple_getD {p : ℕ} {u m : Triple}
    (hp : ∀ j, 0 < (m.get j).re-((m.get j).radius : ℤ)) :
    divideTriple p u m = some ((divideTriple p u m).getD zeroTriple) := by
  cases hx : divRound p u.x m.x with
  | none =>
      have h := divRound_getD_of_pos p u.x m.x (hp 0)
      rw [hx] at h
      cases h
  | some x =>
    cases hy : divRound p u.y m.y with
    | none =>
        have h := divRound_getD_of_pos p u.y m.y (hp 1)
        rw [hy] at h
        cases h
    | some y =>
      cases hz : divRound p u.z m.z with
      | none =>
          have h := divRound_getD_of_pos p u.z m.z (hp 2)
          rw [hz] at h
          cases h
      | some z => simp [divideTriple, hx, hy, hz]

theorem project_contains (d raw : VectorField) (c : Momentum)
    (hvalid : projectionValid d = true)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j)) :
    Contains (project d raw) (GlobalCenter.projectedField 52 c (toRectField raw)) := by
  intro r j
  have hl := laplacianRound_contains (hd r)
  change (laplacianRound 52 (d.get r)).toDyadic.Contains 52 (laplacianSymbol c r : ℂ) at hl
  have h := projectRound_contains (projectRound_getD (projectionValid_pos hvalid r))
    (hd r) (fun i => DyadicRectangle.value_contains 52 (toRectField raw r i)) hl j
  change ((VectorField.build _).get r).toVector j |>.Contains 52 _
  rw [VectorField.get_build]
  simpa only [GlobalCenter.projectedField, GlobalCenter.projectedPolarization,
    gradientProjection_apply, PiLp.sub_apply, PiLp.smul_apply, GlobalCenter.inputPolarization,
    longitudinalVector, Complex.star_def, divergenceSymbol, LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul, mul_comm, toRectField] using h

theorem adjointCurl_contains (d field : VectorField) (c : Momentum) (u : FourierSpace)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j)) (hu : Contains field u) :
    Contains (adjointCurl d field) (GlobalCenter.curlField c u) := by
  intro r j
  have h := curlRound_contains (adjoint := true) (hd r) (hu r) j
  change ((VectorField.build _).get r).toVector j |>.Contains 52 _
  rw [VectorField.get_build]
  have he := congrArg (fun v : Polarization => v j) (frequencyCurl_adjoint_component c r u)
  change GlobalCenter.curlField c u (j,r) = ((curlSymbolMatrix c r).conjTranspose *ᵥ fun i => u (i,r)) j at he
  rw [he]
  exact h

theorem inverse_contains (field : VectorField) (u : Electric → ℂ) (hu : Contains field u) :
    Contains (inverse field) (fun e => (transform 0 *ᵥ fun r => u (e.1,r)) e.2) := by
  intro r j
  have h := GlobalFFTComputed.inverse_contains (field.component j) (fun r => u (j,r))
    (fun r => by simpa only [toField_component] using hu r j)
  have hh := h r
  rw [← toField_component]
  simpa only [inverse, VectorField.map_component] using hh

theorem divideMaterial_contains (field material : VectorField) (u : Electric → ℂ)
    (m : Electric → ℝ) (hvalid : materialValid material = true)
    (hu : Contains field u)
    (hm : ∀ r j, (toRectField material r j).Contains 52 (m (j,r) : ℂ)) :
    Contains (divideMaterial field material) (fun e => u e/(m e : ℂ)) := by
  intro r j
  change ((VectorField.build _).get r).toVector j |>.Contains 52 _
  rw [VectorField.get_build]
  exact divideTriple_contains (divideTriple_getD (materialValid_pos hvalid r)) (hu r) (hm r) j

theorem forward_contains (field : VectorField) (u : Electric → ℂ) (hu : Contains field u) :
    Contains (forward field) (fun e => ((transform 0).conjTranspose *ᵥ fun r => u (e.1,r)) e.2) := by
  intro r j
  have h := GlobalFFTComputed.forward_contains (field.component j) (fun r => u (j,r))
    (fun r => by simpa only [toField_component] using hu r j)
  have hh := h r
  rw [← toField_component]
  simpa only [forward, VectorField.map_component] using hh


theorem weighted_contains (d material field : VectorField) (m : Cell20 → ℝ)
    (c : Momentum) (u : FourierSpace) (hvalid : materialValid material = true)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j))
    (hm : ∀ r j, (toRectField material r j).Contains 52 (edgeAverage m (j,r) : ℂ))
    (hu : Contains field u) :
    Contains (forward (divideMaterial (inverse (adjointCurl d field)) material))
      (GlobalCenter.weightedField m c u) := by
  have hc := adjointCurl_contains d field c u hd hu
  have hi := inverse_contains (adjointCurl d field) (GlobalCenter.curlField c u) hc
  have hi' : Contains (inverse (adjointCurl d field)) (GlobalCenter.inverseCurlField c u) := by
    intro r j
    change (toRectField _ r j).Contains 52
      ((electricTransform 0 *ᵥ GlobalCenter.curlField c u) (j,r))
    rw [electricTransform_mulVec]
    exact hi r j
  have hs := divideMaterial_contains (inverse (adjointCurl d field)) material
    (GlobalCenter.inverseCurlField c u) (edgeAverage m) hvalid hi' hm
  have hs' : Contains (divideMaterial (inverse (adjointCurl d field)) material)
      (GlobalCenter.spatialWeightedField m c u) := by
    intro r j
    rw [GlobalCenter.spatialWeightedField_apply]
    exact hs r j
  have hf := forward_contains (divideMaterial (inverse (adjointCurl d field)) material)
    (GlobalCenter.spatialWeightedField m c u) hs'
  intro r j
  rw [GlobalCenter.weightedField_apply]
  exact hf r j

theorem magnetic_contains (d weighted field : VectorField) (m : Cell20 → ℝ)
    (c : Momentum) (u : FourierSpace)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j))
    (hu : Contains field u) (hw : Contains weighted (GlobalCenter.weightedField m c u)) :
    Contains (magnetic d weighted field)
      ((shiftedMagneticFourier m c (1/64)).toEuclideanLin u) := by
  intro r j
  change ((VectorField.build _).get r).toVector j |>.Contains 52 _
  rw [VectorField.get_build, GlobalCenter.magnetic_action_apply]
  exact magneticRound_contains (hd r) (hw r) (hu r) j


theorem contains_real_pos {p : ℕ} {a : Rectangle} {x : ℝ}
    (ha : a.toDyadic.Contains p (x : ℂ)) (hp : 0 < a.re-(a.radius : ℤ)) : 0 < x := by
  have hlow := (abs_le.mp ha.1).1
  change -(a.radius : ℝ) ≤ x*(2:ℝ)^p-a.re at hlow
  have hpr : 0 < (a.re : ℝ)-(a.radius : ℝ) := by exact_mod_cast hp
  have hmul : 0 < x*(2:ℝ)^p := by linarith
  exact (mul_pos_iff_of_pos_right (by positivity : 0 < (2:ℝ)^p)).mp hmul

theorem projectionValid_laplacian_pos (d : VectorField) (c : Momentum)
    (hvalid : projectionValid d = true)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j)) (r : Cell) :
    0 < laplacianSymbol c r :=
  contains_real_pos (laplacianRound_contains (hd r)) (projectionValid_pos hvalid r)

theorem projectedField_transverse (d raw : VectorField) (c : Momentum)
    (hvalid : projectionValid d = true)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j)) :
    GlobalCenter.projectedField 52 c (toRectField raw) ∈ transverseSubspace c :=
  GlobalCenter.projectedField_transverse 52 c (toRectField raw)
    (fun r => ne_of_gt (projectionValid_laplacian_pos d c hvalid hd r))

def Result.Contains (a : Result) (m : Cell20 → ℝ) (c : Momentum) (raw : VectorField) : Prop :=
  let u := GlobalCenter.projectedField 52 c (toRectField raw)
  Action.Contains a.projected u ∧ Action.Contains a.curl (GlobalCenter.curlField c u) ∧
    Action.Contains a.weighted (GlobalCenter.weightedField m c u) ∧
    Action.Contains a.action ((shiftedMagneticFourier m c (1/64)).toEuclideanLin u)

theorem compute_contains (d material raw : VectorField) (m : Cell20 → ℝ) (c : Momentum)
    (hdvalid : projectionValid d = true) (hmvalid : materialValid material = true)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j))
    (hm : ∀ r j, (toRectField material r j).Contains 52 (edgeAverage m (j,r) : ℂ)) :
    (compute d material raw).Contains m c raw := by
  let u := GlobalCenter.projectedField 52 c (toRectField raw)
  have hp := project_contains d raw c hdvalid hd
  have hc := adjointCurl_contains d (project d raw) c u hd hp
  have hw := weighted_contains d material (project d raw) m c u hmvalid hd hm hp
  exact ⟨hp,hc,hw,magnetic_contains d _ _ m c u hd hp hw⟩

theorem evaluate_contains {d material raw : VectorField} {a : Result}
    (m : Cell20 → ℝ) (c : Momentum) (h : evaluate d material raw = some a)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j))
    (hm : ∀ r j, (toRectField material r j).Contains 52 (edgeAverage m (j,r) : ℂ)) :
    a.Contains m c raw := by
  unfold evaluate at h
  split at h
  next hg =>
    have hboth : projectionValid d = true ∧ materialValid material = true := by
      simpa only [Bool.and_eq_true_iff] using hg
    cases Option.some.inj h
    exact compute_contains d material raw m c hboth.1 hboth.2 hd hm
  next => contradiction


theorem evaluate_transverse {d material raw : VectorField} {a : Result}
    (c : Momentum) (h : evaluate d material raw = some a)
    (hd : ∀ r j, (toRectField d r j).Contains 52 (symbol c r j)) :
    GlobalCenter.projectedField 52 c (toRectField raw) ∈ transverseSubspace c := by
  unfold evaluate at h
  split at h
  next hg =>
    exact projectedField_transverse d raw c (Bool.and_eq_true_iff.mp hg).1 hd
  next => contradiction

end
end Maxwell.Certificate.DyadicKernel.Action
