import Maxwell.Composition.SourceSeedStream
import Maxwell.Composition.SourceMassTable
import Maxwell.Defect.ConcreteFiniteStencil

/-! One fixed local source profile can be computed once for a draw and then
translated to every original source terminal. Its list contains exactly the
literal finite Yee-stencil terms, including terms whose coefficients vanish. -/
noncomputable section
namespace Maxwell.Composition.SourceProfile
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Composition.TranslatedStencil
open FiniteStencil
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1500000

def shift (a : Site) (v : SparseField) : SparseField := v.map fun t => (edge a t.1,t.2)

@[simp] theorem shift_append (a : Site) (v w : SparseField) : shift a (v++w)=shift a v++shift a w := by
  simp [shift]

@[simp] theorem shift_scale (a : Site) (q : ℚ) (v : SparseField) : shift a (scale q v)=scale q (shift a v) := by
  simp [shift,scale,List.map_map,Function.comp_def]

private theorem pullback_shift (a : Site) (p : Equiv.Perm Edge)
    (hp : ∀ e,p.symm (edge a e)=edge a (p.symm e)) (v : SparseField) :
    pullback p (shift a v)=shift a (pullback p v) := by
  simp [pullback,shift,List.map_map,Function.comp_def,hp]

private theorem permutation_shift (a : Site) (p : Equiv.Perm Direction) (w : Direction→Site) :
    ∀ e,(fieldPermutation p w).symm (edge a e)=edge a ((fieldPermutation p w).symm e) := by
  intro e
  apply Prod.ext
  · rfl
  change a+e.2-w (p.symm e.1)=a+(e.2-w (p.symm e.1))
  abel

private theorem inverse_permutation_shift (a : Site) (p : Equiv.Perm Direction) (w : Direction→Site) :
    ∀ e,(fieldPermutation p w).symm.symm (edge a e)=edge a ((fieldPermutation p w).symm.symm e) := by
  intro e
  apply Prod.ext
  · rfl
  change a+e.2+w e.1=a+(e.2+w e.1)
  abel

theorem curl_shift (a : Site) (v : SparseField) : curl (shift a v)=shift a (curl v) := by
  simp only [curl,shift_append,shift_scale]
  rw [pullback_shift a _ (permutation_shift a _ _),
    pullback_shift a _ (permutation_shift a _ _),
    pullback_shift a _ (permutation_shift a _ _),
    pullback_shift a _ (permutation_shift a _ _)]

theorem curlAdjoint_shift (a : Site) (v : SparseField) :
    curlAdjoint (shift a v)=shift a (curlAdjoint v) := by
  simp only [curlAdjoint,shift_append,shift_scale]
  rw [pullback_shift a _ (inverse_permutation_shift a _ _),
    pullback_shift a _ (inverse_permutation_shift a _ _),
    pullback_shift a _ (inverse_permutation_shift a _ _),
    pullback_shift a _ (inverse_permutation_shift a _ _)]

def mass (P : PeriodicScalarBackground) : Edge→ℚ := rationalEdgeAverage P.material

theorem mass_cast (P : PeriodicScalarBackground) (e : Edge) :
    (mass P e:ℝ)=periodicCoefficient P.edgeMaterial e := by
  simp only [mass,rationalEdgeAverage,periodicCoefficient,edgeMod20,
    PeriodicScalarBackground.edgeMaterial,PeriodicYee.edgeAverage,
    Rat.cast_div,Rat.cast_add,Rat.cast_ofNat]

theorem mass_periodic (P : PeriodicScalarBackground) (a : Site) (e : Edge) :
    mass P (edge (20 • a) e)=mass P e := by
  apply Rat.cast_injective (α:=ℝ)
  rw [mass_cast,mass_cast]
  simpa only [edge,add_comm] using periodicCoefficient_periodic P.edgeMaterial e.1 e.2 a

theorem step_shift (P : PeriodicScalarBackground) (a : Site) (σ : ℚ) (v : SparseField) :
    step (mass P) σ (shift (20 • a) v)=shift (20 • a) (step (mass P) σ v) := by
  have hm : multiply (mass P) (shift (20 • a) v)=shift (20 • a) (multiply (mass P) v) := by
    simp only [multiply,shift,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro t _
    rw [mass_periodic]
  simp only [step,shift_append,shift_scale,curl_shift,curlAdjoint_shift,hm]

def seed (P : PhysicalPlatform) (q : PhysicalSource.Local P→ℚ) : SparseField :=
  List.ofFn fun k => (ScalarDefect.edgeEmbedding P.defect k,
    (ScalarDefect.coordinateWeight P.defect k)⁻¹*q k)

def profile (P : PhysicalPlatform) (σ : ℚ) (q : PhysicalSource.Local P→ℚ) : SparseField :=
  step (mass P.background) σ (seed P q)

theorem profile_length (P : PhysicalPlatform) (σ : ℚ) (q : PhysicalSource.Local P→ℚ) :
    (profile P σ q).length=18*(ScalarDefect.edges P.defect).card := by
  simp [profile,step_length,seed]

theorem seed_supported (P : PhysicalPlatform) (q : PhysicalSource.Local P→ℚ) :
    Supported (seed P q) (SourceDefectLayout.radius P.defect+1) := by
  intro t ht j
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ht
  have h := edge_bounds P.defect (SourceDefectLayout.radius P.defect)
    (SourceDefectLayout.radius_bounds P.defect) (ScalarDefect.edgeEmbedding P.defect k)
    (embedding_mem P.defect k) j
  exact abs_le.mpr ⟨by exact_mod_cast (show -((SourceDefectLayout.radius P.defect:ℤ)+1)≤
    (ScalarDefect.edgeEmbedding P.defect k).2 j by omega),by exact_mod_cast h.2⟩

theorem profile_supported (P : PhysicalPlatform) (σ : ℚ) (q : PhysicalSource.Local P→ℚ) :
    Supported (profile P σ q) (SourceDefectLayout.radius P.defect+3) := by
  simpa only [profile,Nat.add_assoc] using (seed_supported P q).step (mass P.background) σ

/-- Exact equality with the actual operating lattice operator, including
its draw-dependent scalar shift. -/
theorem embed_profile (P : PhysicalPlatform) (σ : ℚ) (q : PhysicalSource.Local P→ℚ) :
    embed (profile P σ q) =
      (P.background.operator-(σ:ℂ)•ContinuousLinearMap.id ℂ Field) (embed (seed P q)) := by
  have hm (e : Edge) : |(mass P.background e:ℝ)|≤25 := by
    rw [mass_cast]
    exact P.background.edge_bound e
  rw [profile,embed_step (mass P.background) 25 (by norm_num) hm]
  have he : (fun e => (mass P.background e:ℝ))=periodicCoefficient P.background.edgeMaterial :=
    funext (mass_cast P.background)
  simp only [FiniteStencil.operator,he,PeriodicScalarBackground.operator]

end Maxwell.Composition.SourceProfile
