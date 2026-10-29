import Maxwell.Continuum.BoxModesCosineAlgebra

/-!
# The literal mixed mode span contains the dense weighted cosine algebra

Multiplying a PEC sine/cosine mode by a fundamental coordinate cosine gives
the sum of its two neighboring integer-frequency modes. This proves module
invariance directly from trigonometric identities. Stone--Weierstrass then
puts every continuous function times the explicit positive interior sine
weight in the closure of the mode span.
-/

noncomputable section
namespace Maxwell.Continuum.BoxModes

open scoped BigOperators

/-- The factor in coordinate `j`, with cosine in the component direction. -/
def cubeFactor (N : Fin 3 → ℝ) (c : Fin 3) (n : ℤ) (j : Fin 3) : C(ClosedCube N, ℝ) :=
  if j = c then cubeCos N n j else cubeSin N n j

def cubeMode (N : Fin 3 → ℝ) (c : Fin 3) (ν : Fin 3 → ℤ) : C(ClosedCube N, ℝ) :=
  ∏ j : Fin 3, cubeFactor N c (ν j) j

@[simp] theorem cubeMode_apply (N : Fin 3 → ℝ) (c : Fin 3)
    (ν : Fin 3 → ℤ) (x : ClosedCube N) :
    cubeMode N c ν x = scalarBoxMode N ν c (cubePoint N x) := by
  simp only [cubeMode, ContinuousMap.prod_apply, scalarBoxMode]
  apply Finset.prod_congr rfl
  intro j _
  rcases eq_or_ne j c with rfl | hj
  · simp [cubeFactor, cubeCos, coordinateMode]
  · simp [cubeFactor, cubeSin, coordinateMode, hj]

def mixedModeSpan (N : Fin 3 → ℝ) (c : Fin 3) : Submodule ℝ C(ClosedCube N, ℝ) :=
  Submodule.span ℝ (Set.range (cubeMode N c))

theorem cubeCos_one_mul_cos (N : Fin 3 → ℝ) (n : ℤ) (j : Fin 3) :
    cubeCos N 1 j * cubeCos N n j =
      (1 / 2 : ℝ) • (cubeCos N (n + 1) j + cubeCos N (n - 1) j) := by
  ext x
  change Real.cos ((1 : ℤ) * Real.pi / N j * (x j : ℝ)) *
      Real.cos ((n : ℝ) * Real.pi / N j * (x j : ℝ)) =
    (1 / 2 : ℝ) * (Real.cos (((n + 1 : ℤ) : ℝ) * Real.pi / N j * (x j : ℝ)) +
      Real.cos (((n - 1 : ℤ) : ℝ) * Real.pi / N j * (x j : ℝ)))
  push_cast
  simp only [one_mul]
  have hp : ((n : ℝ) + 1) * Real.pi / N j * (x j : ℝ) =
      (n : ℝ) * Real.pi / N j * (x j : ℝ) + Real.pi / N j * (x j : ℝ) := by ring
  have hm : ((n : ℝ) - 1) * Real.pi / N j * (x j : ℝ) =
      (n : ℝ) * Real.pi / N j * (x j : ℝ) - Real.pi / N j * (x j : ℝ) := by ring
  rw [hp, hm, Real.cos_add, Real.cos_sub]
  ring

theorem cubeCos_one_mul_sin (N : Fin 3 → ℝ) (n : ℤ) (j : Fin 3) :
    cubeCos N 1 j * cubeSin N n j =
      (1 / 2 : ℝ) • (cubeSin N (n + 1) j + cubeSin N (n - 1) j) := by
  ext x
  change Real.cos ((1 : ℤ) * Real.pi / N j * (x j : ℝ)) *
      Real.sin ((n : ℝ) * Real.pi / N j * (x j : ℝ)) =
    (1 / 2 : ℝ) * (Real.sin (((n + 1 : ℤ) : ℝ) * Real.pi / N j * (x j : ℝ)) +
      Real.sin (((n - 1 : ℤ) : ℝ) * Real.pi / N j * (x j : ℝ)))
  push_cast
  simp only [one_mul]
  have hp : ((n : ℝ) + 1) * Real.pi / N j * (x j : ℝ) =
      (n : ℝ) * Real.pi / N j * (x j : ℝ) + Real.pi / N j * (x j : ℝ) := by ring
  have hm : ((n : ℝ) - 1) * Real.pi / N j * (x j : ℝ) =
      (n : ℝ) * Real.pi / N j * (x j : ℝ) - Real.pi / N j * (x j : ℝ) := by ring
  rw [hp, hm, Real.sin_add, Real.sin_sub]
  ring

theorem cubeCos_one_mul_factor (N : Fin 3 → ℝ) (c : Fin 3) (n : ℤ) (j : Fin 3) :
    cubeCos N 1 j * cubeFactor N c n j =
      (1 / 2 : ℝ) • (cubeFactor N c (n + 1) j + cubeFactor N c (n - 1) j) := by
  by_cases hj : j = c
  · simpa [cubeFactor, hj] using cubeCos_one_mul_cos N n j
  · simpa [cubeFactor, hj] using cubeCos_one_mul_sin N n j

private theorem cubeMode_split (N : Fin 3 → ℝ) (c : Fin 3)
    (ν : Fin 3 → ℤ) (j : Fin 3) :
    cubeMode N c ν = cubeFactor N c (ν j) j *
      ∏ k ∈ Finset.univ.erase j, cubeFactor N c (ν k) k := by
  exact (Finset.mul_prod_erase Finset.univ (fun k => cubeFactor N c (ν k) k)
    (Finset.mem_univ j)).symm

private theorem cubeMode_update (N : Fin 3 → ℝ) (c : Fin 3)
    (ν : Fin 3 → ℤ) (j : Fin 3) (n : ℤ) :
    cubeMode N c (Function.update ν j n) = cubeFactor N c n j *
      ∏ k ∈ Finset.univ.erase j, cubeFactor N c (ν k) k := by
  rw [cubeMode_split N c _ j, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

/-- Exact neighboring-index recurrence for the full mixed mode. -/
theorem cubeCos_one_mul_mode (N : Fin 3 → ℝ) (c : Fin 3)
    (ν : Fin 3 → ℤ) (j : Fin 3) :
    cubeCos N 1 j * cubeMode N c ν = (1 / 2 : ℝ) •
      (cubeMode N c (Function.update ν j (ν j + 1)) +
        cubeMode N c (Function.update ν j (ν j - 1))) := by
  rw [cubeMode_split N c ν j, ← mul_assoc, cubeCos_one_mul_factor,
    cubeMode_update, cubeMode_update, smul_mul_assoc, add_mul]

theorem cubeCos_mul_mem_mixedModeSpan (N : Fin 3 → ℝ) (c j : Fin 3)
    (g : C(ClosedCube N, ℝ)) (hg : g ∈ mixedModeSpan N c) :
    cubeCos N 1 j * g ∈ mixedModeSpan N c := by
  refine Submodule.span_induction (p := fun g _ => cubeCos N 1 j * g ∈ mixedModeSpan N c)
    ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨ν, rfl⟩
    rw [cubeCos_one_mul_mode]
    apply Submodule.smul_mem
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨_, rfl⟩
    · exact Submodule.subset_span ⟨_, rfl⟩
  · simp
  · intro x y _ _ hx hy
    simpa only [mul_add] using (mixedModeSpan N c).add_mem hx hy
  · intro a x _ hx
    simpa only [mul_smul_comm] using (mixedModeSpan N c).smul_mem a hx

/-- Multiplication by every element of the actual dense cosine algebra
preserves the mixed mode span. -/
theorem cosineAlgebra_mul_mem_mixedModeSpan (N : Fin 3 → ℝ) (c : Fin 3)
    (f : C(ClosedCube N, ℝ)) (hf : f ∈ cosineAlgebra N)
    (g : C(ClosedCube N, ℝ)) (hg : g ∈ mixedModeSpan N c) :
    f * g ∈ mixedModeSpan N c := by
  refine Algebra.adjoin_induction
    (p := fun f _ => ∀ g ∈ mixedModeSpan N c, f * g ∈ mixedModeSpan N c)
    ?_ ?_ ?_ ?_ hf g hg
  · rintro _ ⟨j, rfl⟩ g hg
    exact cubeCos_mul_mem_mixedModeSpan N c j g hg
  · intro r g hg
    simpa only [← Algebra.smul_def] using (mixedModeSpan N c).smul_mem r hg
  · intro x y _ _ hx hy g hg
    simpa only [add_mul] using (mixedModeSpan N c).add_mem (hx g hg) (hy g hg)
  · intro x y _ _ hx hy g hg
    simpa only [mul_assoc] using hx (y * g) (hy g hg)

/-- The lowest mixed mode: constant in the cosine direction and a first
sine in both transverse coordinates. -/
def baseWeight (N : Fin 3 → ℝ) (c : Fin 3) : C(ClosedCube N, ℝ) :=
  cubeMode N c (fun j => if j = c then 0 else 1)

/-- Uniform closure of the mode span contains every continuous function
times the explicit sine weight. -/
theorem continuous_mul_baseWeight_mem_closure (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (c : Fin 3) (f : C(ClosedCube N, ℝ)) :
    f * baseWeight N c ∈ (mixedModeSpan N c).topologicalClosure := by
  have hf : f ∈ (cosineAlgebra N).topologicalClosure := by
    rw [cosineAlgebra_dense N hN]
    trivial
  have hw : baseWeight N c ∈ mixedModeSpan N c := Submodule.subset_span ⟨_, rfl⟩
  have hclosed : IsClosed {g : C(ClosedCube N, ℝ) |
      g * baseWeight N c ∈ (mixedModeSpan N c).topologicalClosure} :=
    (mixedModeSpan N c).isClosed_topologicalClosure.preimage
      (continuous_id.mul continuous_const)
  apply (closure_minimal (s := (cosineAlgebra N : Set C(ClosedCube N, ℝ)))
    (t := {g | g * baseWeight N c ∈ (mixedModeSpan N c).topologicalClosure}) ?_ hclosed) hf
  intro g hg
  exact (mixedModeSpan N c).le_topologicalClosure
    (cosineAlgebra_mul_mem_mixedModeSpan N c g hg _ hw)

/-- The weight is strictly positive throughout the open physical box. -/
theorem baseWeight_pos_on_openBox (N : Fin 3 → ℝ) (hN : ∀ j, 0 < N j)
    (c : Fin 3) (x : ClosedCube N) (hx : cubePoint N x ∈ openBox N) :
    0 < baseWeight N c x := by
  have hx' := (mem_openBox N (cubePoint N x)).mp hx
  change 0 < (∏ j : Fin 3, cubeFactor N c (if j = c then 0 else 1) j) x
  simp only [ContinuousMap.prod_apply]
  apply Finset.prod_pos
  intro j _
  by_cases hj : j = c
  · simp [cubeFactor, hj, cubeCos, intervalCos]
  · simp only [cubeFactor, hj, ite_false, cubeSin, ContinuousMap.coe_mk,
      intervalSin, Int.cast_one, one_mul]
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos (div_pos Real.pi_pos (hN j)) (hx' j).1
    · calc
        Real.pi / N j * (x j : ℝ) < Real.pi / N j * N j :=
          mul_lt_mul_of_pos_left (hx' j).2 (div_pos Real.pi_pos (hN j))
        _ = Real.pi := div_mul_cancel₀ _ (hN j).ne'

#print axioms continuous_mul_baseWeight_mem_closure
#print axioms baseWeight_pos_on_openBox

end Maxwell.Continuum.BoxModes
