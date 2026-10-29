import Maxwell.Continuum.ClusterComplementCentralNorm

/-! Literal polar-vector coordinate reflection of the complex Maxwell symbol.
Momentum products remain bilinear; no conjugation is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.FiberReflection

open FreeFiber

def coordinateSign (j k : Fin 3) : ℂ := if k = j then -1 else 1

theorem coordinateSign_sq (j k : Fin 3) : coordinateSign j k ^ 2 = 1 := by
  unfold coordinateSign
  split_ifs <;> norm_num

theorem coordinateSign_norm (j k : Fin 3) : ‖coordinateSign j k‖ = 1 := by
  unfold coordinateSign
  split_ifs <;> norm_num

def momentum (j : Fin 3) (p : Momentum) : Momentum := fun k => coordinateSign j k * p k

theorem momentum_involutive (j : Fin 3) : Function.Involutive (momentum j) := by
  intro p
  funext k
  change coordinateSign j k * (coordinateSign j k * p k) = p k
  rw [← mul_assoc, ← pow_two, coordinateSign_sq, one_mul]

theorem momentumSquare_reflect (j : Fin 3) (p : Momentum) :
    momentumSquare (momentum j p) = momentumSquare p := by
  simp only [momentumSquare, momentum, mul_pow, coordinateSign_sq, one_mul]

theorem bilinearDot_reflect (j : Fin 3) (p q : Momentum) :
    bilinearDot (momentum j p) (momentum j q) = bilinearDot p q := by
  apply Finset.sum_congr rfl
  intro k _
  change (coordinateSign j k * p k) * (coordinateSign j k * q k) = p k * q k
  calc
    _ = coordinateSign j k ^ 2 * (p k * q k) := by ring
    _ = _ := by rw [coordinateSign_sq, one_mul]

def polarization (j : Fin 3) : Polarization ≃ₗᵢ[ℂ] Polarization where
  toFun v := WithLp.toLp 2 (momentum j (WithLp.ofLp v))
  invFun v := WithLp.toLp 2 (momentum j (WithLp.ofLp v))
  left_inv v := by
    apply PiLp.ext
    intro k
    exact congrFun (momentum_involutive j (WithLp.ofLp v)) k
  right_inv v := by
    apply PiLp.ext
    intro k
    exact congrFun (momentum_involutive j (WithLp.ofLp v)) k
  map_add' u v := by
    apply PiLp.ext
    intro k
    exact mul_add (coordinateSign j k) (u k) (v k)
  map_smul' c u := by
    apply PiLp.ext
    intro k
    change coordinateSign j k * (c * u k) = c * (coordinateSign j k * u k)
    ring
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖WithLp.toLp 2 (momentum j (WithLp.ofLp v))‖ ^ 2 = ‖v‖ ^ 2
    simp only [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro k _
    change ‖coordinateSign j k * v k‖ ^ 2 = ‖v k‖ ^ 2
    rw [norm_mul, coordinateSign_norm, one_mul]

@[simp] theorem polarization_apply (j : Fin 3) (v : Polarization) (k : Fin 3) :
    polarization j v k = coordinateSign j k * v k := rfl

theorem polarization_involutive (j : Fin 3) (v : Polarization) :
    polarization j (polarization j v) = v := (polarization j).left_inv v

theorem block_coordinate (p : Momentum) (E : ℂ) (v : Polarization) (k : Fin 3) :
    block p E v k = (momentumSquare p - E) * v k - p k * bilinearDot p (WithLp.ofLp v) := by
  change (Matrix.mulVec (blockMatrix p E) (WithLp.ofLp v)) k = _
  simp only [blockMatrix, momentumOuter, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_mulVec, bilinearDot, dotProduct, op_smul_eq_mul]

/-- Reflection intertwines the entire three-polarization block at complex momentum. -/
theorem block_reflect (j : Fin 3) (p : Momentum) (E : ℂ) (v : Polarization) :
    block (momentum j p) E (polarization j v) = polarization j (block p E v) := by
  apply PiLp.ext
  intro k
  simp only [block_coordinate, polarization_apply, momentumSquare_reflect]
  have hd : bilinearDot (momentum j p) (WithLp.ofLp (polarization j v)) =
      bilinearDot p (WithLp.ofLp v) := bilinearDot_reflect j p (WithLp.ofLp v)
  rw [hd]
  change _ = coordinateSign j k * ((momentumSquare p - E) * v k -
    p k * bilinearDot p (WithLp.ofLp v))
  simp only [momentum]
  ring

def aliasEquiv (j : Fin 3) : Alias ≃ Alias where
  toFun ν k := if k = j then -ν k - 1 else ν k
  invFun ν k := if k = j then -ν k - 1 else ν k
  left_inv ν := by
    funext k
    by_cases h : k = j <;> simp [h]
  right_inv ν := by
    funext k
    by_cases h : k = j <;> simp [h]

theorem alias_involutive (j : Fin 3) (ν : Alias) : aliasEquiv j (aliasEquiv j ν) = ν :=
  (aliasEquiv j).left_inv ν

theorem aliasMomentum_reflect (j : Fin 3) (q : Momentum) (ν : Alias) :
    aliasMomentum (momentum j q) ν = momentum j (aliasMomentum q (aliasEquiv j ν)) := by
  funext k
  by_cases h : k = j
  · simp only [aliasMomentum, momentum, coordinateSign, h, ↓reduceIte, aliasEquiv,
      Equiv.coe_fn_mk, Int.cast_sub, Int.cast_neg, Int.cast_one]
    ring
  · simp only [aliasMomentum, momentum, coordinateSign, h, ↓reduceIte, aliasEquiv,
      Equiv.coe_fn_mk, one_mul]

end Maxwell.Continuum.FiberReflection
