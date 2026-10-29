import Maxwell.Continuum.FiberAnalyticSchur
import Maxwell.Continuum.CornerVelocity

/-!
# Literal cubeAlias coordinates for the certified continuum corner

The eight sign-cube vertices are identified with the eight central integer
aliases. Finite complex amplitudes are embedded in the actual infinite
cubeAlias Hilbert space, with their exact inner product preserved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CornerBridge

open FreeFiber ClusterComplement
open scoped Classical InnerProductSpace

abbrev Cube := Corner.Parity → Momentum

def parityBoolEquiv : Corner.Parity ≃ (Fin 3 → Bool) where
  toFun s := ![s.1, s.2.1, s.2.2]
  invFun b := (b 0, b 1, b 2)
  left_inv s := rfl
  right_inv b := by funext j; fin_cases j <;> rfl

def parityAliasEquiv : Corner.Parity ≃ CentralAlias :=
  parityBoolEquiv.trans centralAliasEquiv.symm

def cubeAlias (s : Corner.Parity) : Alias := (parityAliasEquiv s).val

theorem alias_central (s : Corner.Parity) : IsCentralAlias (cubeAlias s) :=
  (parityAliasEquiv s).property

theorem alias_apply (s : Corner.Parity) (j : Fin 3) :
    cubeAlias s j = if parityBoolEquiv s j then 0 else -1 := rfl

theorem alias_signs (s : Corner.Parity) : cornerSigns (cubeAlias s) = Corner.waveSigns s := by
  obtain ⟨a,b,c⟩ := s
  funext j
  cases a <;> cases b <;> cases c <;> fin_cases j <;>
    norm_num [cornerSigns, alias_apply, parityBoolEquiv, Corner.waveSigns, Corner.sign]

def pack (u : Cube) : FiberSpace :=
  ⟨fun ν => if hν : IsCentralAlias ν then
    momentumVector (u (parityAliasEquiv.symm ⟨ν,hν⟩)) else 0,
    central_support_memℓp _ (by intro ν hν; simp [hν])⟩

@[simp] theorem pack_alias (u : Cube) (s : Corner.Parity) :
    pack u (cubeAlias s) = momentumVector (u s) := by
  change (if hν : IsCentralAlias (cubeAlias s) then
    momentumVector (u (parityAliasEquiv.symm ⟨cubeAlias s,hν⟩)) else 0) = _
  rw [dite_eq_left (alias_central s)]
  exact congrArg (fun p => momentumVector (u p)) (parityAliasEquiv.symm_apply_apply s)

@[simp] theorem pack_noncentral (u : Cube) (ν : Alias) (hν : ¬IsCentralAlias ν) :
    pack u ν = 0 := by simp [pack,hν]

theorem pack_add (u v : Cube) : pack (u+v) = pack u + pack v := by
  apply Subtype.ext
  funext ν
  by_cases hν : IsCentralAlias ν <;> simp [pack,hν,momentumVector]

theorem pack_smul (c : ℂ) (u : Cube) : pack (c • u) = c • pack u := by
  apply Subtype.ext
  funext ν
  by_cases hν : IsCentralAlias ν <;> simp [pack,hν,momentumVector]

def packLinear : Cube →ₗ[ℂ] FiberSpace where
  toFun := pack
  map_add' := pack_add
  map_smul' := pack_smul

theorem pack_injective : Function.Injective pack := by
  intro u v h
  funext s j
  have hs := congrArg (fun f : FiberSpace => f (cubeAlias s) j) h
  simpa only [pack_alias,momentumVector] using hs

theorem eq_of_aliases (u v : FiberSpace)
    (hu : ∀ ν, ¬IsCentralAlias ν → u ν = 0)
    (hv : ∀ ν, ¬IsCentralAlias ν → v ν = 0)
    (h : ∀ s, u (cubeAlias s) = v (cubeAlias s)) : u = v := by
  apply Subtype.ext
  funext ν
  by_cases hν : IsCentralAlias ν
  · obtain ⟨s,hs⟩ := parityAliasEquiv.surjective ⟨ν,hν⟩
    have ha : cubeAlias s = ν := congrArg Subtype.val hs
    exact ha ▸ h s
  · rw [hu ν hν,hv ν hν]

theorem pack_inner (u v : Cube) :
    inner ℂ (pack u) (pack v) =
      ∑ s : Corner.Parity, inner ℂ (momentumVector (u s)) (momentumVector (v s)) := by
  have hsupport : Function.support
      (fun ν : Alias => inner ℂ (pack u ν) (pack v ν)) ⊆ {ν | IsCentralAlias ν} := by
    intro ν hν
    by_contra hn
    apply hν
    change inner ℂ (pack u ν) (pack v ν) = 0
    rw [pack_noncentral u ν hn, inner_zero_left]
  calc
    _ = ∑' ν : Alias, inner ℂ (pack u ν) (pack v ν) := lp.inner_eq_tsum _ _
    _ = ∑' ν : CentralAlias, inner ℂ (pack u ν.val) (pack v ν.val) :=
      (tsum_subtype_eq_of_support_subset hsupport).symm
    _ = ∑' s : Corner.Parity, inner ℂ (pack u (cubeAlias s)) (pack v (cubeAlias s)) :=
      (parityAliasEquiv.tsum_eq (fun ν : CentralAlias =>
        inner ℂ (pack u ν.val) (pack v ν.val))).symm
    _ = _ := by simp only [pack_alias,tsum_fintype]

def realCube (u : Corner.ClusterField) : Cube := fun s => realMomentum (u s)

def packReal (u : Corner.ClusterField) : FiberSpace := pack (realCube u)

theorem packReal_inner (u v : Corner.ClusterField) :
    inner ℂ (packReal u) (packReal v) = (Corner.clusterDot u v : ℂ) := by
  rw [packReal,packReal,pack_inner]
  simp only [realCube,momentumVector,PiLp.inner_apply,realMomentum,
    RCLike.inner_apply,Complex.conj_ofReal,Corner.clusterDot,dotProduct,
    Complex.ofReal_sum,Complex.ofReal_mul,mul_comm]

end Maxwell.Continuum.CornerBridge
