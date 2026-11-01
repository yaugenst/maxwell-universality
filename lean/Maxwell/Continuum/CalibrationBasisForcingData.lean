import Maxwell.Continuum.RationalDataflowPointSupport
import Maxwell.Continuum.CalibrationRationalMatrix

/-! The literal six-point right-coupling source of each central basis vector.
Its finite support is independent of the requested Neumann radius and order. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open FreeFiber RationalDataflow PointSupport
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def corner (column : Fin 24) : Alias := rationalCubeAlias (centralIndexFin.symm column).1
def polarization (column : Fin 24) : Fin 3 := (centralIndexFin.symm column).2
def key (ν : Alias) (j : Fin 3) : Point :=
  [(13,(ν 0:ℚ)),(14,(ν 1:ℚ)),(15,(ν 2:ℚ)),(23,(j.val:ℚ))]
def weightedKey (ν : Alias) (j : Fin 3) (w : ℚ) : Point × ℚ :=
  (key ν j,if rationalCentralCheck ν then 0 else w)
def support (column : Fin 24) : Support :=
  (List.ofFn (fun j : Fin 3 => weightedKey (corner column-unitAlias j) (polarization column)
    (-rationalAmplitude*rationalWeight j)))++
  (List.ofFn (fun j : Fin 3 => weightedKey (corner column+unitAlias j) (polarization column)
    (-rationalAmplitude*rationalWeight j)))

theorem key_matches (ν ξ : Alias) (j k : Fin 3) (v : ℕ → ℚ)
    (hcoord : v 13=(ν 0:ℚ) ∧ v 14=(ν 1:ℚ) ∧ v 15=(ν 2:ℚ))
    (hpol : v 23=(j.val:ℚ)) : Matches (key ξ k) v ↔ ν=ξ ∧ j=k := by
  simp only [Matches,key,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,
    forall_eq,hcoord.1,hcoord.2.1,hcoord.2.2,hpol,Int.cast_inj,Nat.cast_inj]
  constructor
  · rintro ⟨h0,h1,h2,hj⟩
    exact ⟨funext (fun i => by fin_cases i <;> assumption),Fin.ext hj⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,rfl,rfl⟩

theorem weighted_value (ν ξ : Alias) (j k : Fin 3) (w : ℚ) (v : ℕ → ℚ)
    (hcoord : v 13=(ν 0:ℚ) ∧ v 14=(ν 1:ℚ) ∧ v 15=(ν 2:ℚ))
    (hpol : v 23=(j.val:ℚ)) :
    (if Matches (weightedKey ξ k w).1 v then (weightedKey ξ k w).2 else 0)=
      if rationalCentralCheck ν then 0 else w*(if ν=ξ ∧ j=k then 1 else 0) := by
  simp only [weightedKey,key_matches ν ξ j k v hcoord hpol]
  by_cases he : ν=ξ
  · subst ξ
    by_cases hj : j=k <;> by_cases hc : rationalCentralCheck ν <;> simp [hj,hc]
  · simp [he]

theorem corner_central (column : Fin 24) : rationalCentralCheck (corner column)=true :=
  (rationalCentralCheck_true _).mpr (CornerBridge.alias_central _)

theorem basis_central (column : Fin 24) :
    rationalCentral (rationalBasisField column)=rationalBasisField column := by
  funext ν j
  by_cases he : ν=corner column
  · subst ν
    simp only [rationalCentral,corner_central,↓reduceIte]
  · have hb : rationalBasisField column ν j=0 := by
      change (if ν=corner column ∧ j=polarization column then 1 else 0)=0
      simp only [he,false_and,↓reduceIte]
    simp only [rationalCentral,hb,ite_self]

theorem value_correct (column : Fin 24) (ν : Alias) (j : Fin 3) (v : ℕ → ℚ)
    (hcoord : v 13=(ν 0:ℚ) ∧ v 14=(ν 1:ℚ) ∧ v 15=(ν 2:ℚ))
    (hpol : v 23=(j.val:ℚ)) :
    value (support column) v=rationalRightCoupling (rationalBasisField column) ν j := by
  simp only [value,support,List.map_append,List.sum_append,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  simp_rw [weighted_value ν _ j _ _ v hcoord hpol]
  unfold rationalRightCoupling
  rw [basis_central]
  by_cases hc : rationalCentralCheck ν
  · simp only [hc,↓reduceIte,Finset.sum_const_zero,add_zero,rationalNoncentral,
      Pi.smul_apply,smul_eq_mul,mul_zero]
  · simp only [hc,Bool.false_eq_true,↓reduceIte,rationalNoncentral,Pi.smul_apply,smul_eq_mul,rationalPotential]
    simp only [Finset.mul_sum,mul_add,Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro a _
    · have he : ν+unitAlias a=corner column ↔ ν=corner column-unitAlias a :=
        eq_sub_iff_add_eq.symm
      change (-rationalAmplitude*rationalWeight a)*(if _ then 1 else 0)=_
      change _=(-rationalAmplitude)*(rationalWeight a*
        (if ν+unitAlias a=corner column ∧ j=polarization column then 1 else 0))
      simp only [he]
      ring
    · have he : ν-unitAlias a=corner column ↔ ν=corner column+unitAlias a :=
        sub_eq_iff_eq_add
      change (-rationalAmplitude*rationalWeight a)*(if _ then 1 else 0)=_
      change _=(-rationalAmplitude)*(rationalWeight a*
        (if ν-unitAlias a=corner column ∧ j=polarization column then 1 else 0))
      simp only [he]
      ring

theorem support_scoped (column : Fin 24) : PointSupport.Scoped (support column) 32 := by
  intro p hp
  simp only [support,List.mem_append,List.mem_ofFn] at hp
  rcases hp with ⟨j,rfl⟩|⟨j,rfl⟩
  all_goals
    apply distance_scoped
    simp only [weightedKey,key,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    decide

#print axioms value_correct
end Maxwell.Continuum.Calibration.BasisForcing
