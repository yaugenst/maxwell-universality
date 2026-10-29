import Maxwell.Logical.Routing

/-! Composition of actual slab paths into disjoint token trajectories.
The hypotheses concern individual layer paths and their port faces;
the global injectivity conclusion is derived rather than supplied. -/

namespace Maxwell.Logical.Routing.Assembly

open Maxwell.Logical.Routing

/-- Layer paths with exact shared port coordinates. -/
structure LayeredRoutes (Token : Type*) (layers : ℕ) where
  length : Fin layers → Token → ℕ
  point : Fin layers → Token → ℕ → Point
  port : Fin (layers + 1) → Token → Point
  port_height : ∀ level token, (port level token).2.2 = 16 * level.val
  port_injective : ∀ level, Function.Injective (port level)
  first : ∀ level token, point level token 0 = port level.castSucc token
  last : ∀ level token, point level token (length level token) = port level.succ token
  step : ∀ level token i, i < length level token →
    UnitAdjacent (point level token i) (point level token (i + 1))
  slab : ∀ level token i, i ≤ length level token →
    16 * (level.val : ℤ) ≤ (point level token i).2.2 ∧
      (point level token i).2.2 ≤ 16 * (level.val + 1 : ℕ)
  lower_index : ∀ level token i, i ≤ length level token →
    (point level token i).2.2 = 16 * level.val → i = 0
  upper_index : ∀ level token i, i ≤ length level token →
    (point level token i).2.2 = 16 * (level.val + 1 : ℕ) → i = length level token
  layer_injective : ∀ level a b i j, i ≤ length level a → j ≤ length level b →
    point level a i = point level b j → a = b ∧ i = j

/-- If layer indices are ordered, an intersection belongs either to one
layer or to the unique common boundary of consecutive layers. -/
theorem ordered_overlap {Token : Type*} {layers : ℕ} (routes : LayeredRoutes Token layers)
    (l k : Fin layers) (a b : Token) (i j : ℕ)
    (hi : i ≤ routes.length l a) (hj : j ≤ routes.length k b)
    (hlk : l.val ≤ k.val) (he : routes.point l a i = routes.point k b j) :
    a = b ∧ (l = k ∧ i = j ∨ l.val + 1 = k.val ∧ i = routes.length l a ∧ j = 0) := by
  by_cases hl : l = k
  · subst k
    have hh := routes.layer_injective l a b i j hi hj he
    exact ⟨hh.1, Or.inl ⟨rfl, hh.2⟩⟩
  · have hln : l.val ≠ k.val := fun h => hl (Fin.ext h)
    have hs := routes.slab l a i hi
    have ht := routes.slab k b j hj
    have hz := congrArg (fun p : Point => p.2.2) he
    have hk : l.val + 1 = k.val := by omega
    have hzi : (routes.point l a i).2.2 = 16 * (l.val + 1 : ℕ) := by omega
    have hzj : (routes.point k b j).2.2 = 16 * k.val := by omega
    have hie := routes.upper_index l a i hi hzi
    have hje := routes.lower_index k b j hj hzj
    have hports : l.succ = k.castSucc := by apply Fin.ext; exact hk
    rw [hie, hje, routes.last, routes.first, hports] at he
    exact ⟨routes.port_injective k.castSucc he, Or.inr ⟨hk, hie, hje⟩⟩

/-- Different tokens are disjoint throughout all layers, including the
shared slab faces. -/
theorem token_trajectories_disjoint {Token : Type*} {layers : ℕ} (routes : LayeredRoutes Token layers)
    (l k : Fin layers) (a b : Token) (i j : ℕ)
    (hi : i ≤ routes.length l a) (hj : j ≤ routes.length k b)
    (he : routes.point l a i = routes.point k b j) : a = b := by
  by_cases hlk : l.val ≤ k.val
  · exact (ordered_overlap routes l k a b i j hi hj hlk he).1
  · exact (ordered_overlap routes k l b a j i hj hi (by omega) he.symm).1.symm

/-- Store each shared boundary vertex once: include a layer's initial
vertex and exclude its final vertex, then add the final port separately. -/
def TrajectoryIndex {Token : Type*} {layers : ℕ} (routes : LayeredRoutes Token layers) (token : Token) :=
  (Σ level : Fin layers, Fin (routes.length level token)) ⊕ Unit

def trajectoryPoint {Token : Type*} {layers : ℕ} (routes : LayeredRoutes Token layers)
    (token : Token) : TrajectoryIndex routes token → Point
  | Sum.inl ⟨level, step⟩ => routes.point level token step.val
  | Sum.inr _ => routes.port (Fin.last layers) token

/-- No stored layer vertex reaches the terminal port face. -/
theorem stored_vertex_below_end {Token : Type*} {layers : ℕ} (routes : LayeredRoutes Token layers)
    (level : Fin layers) (token : Token) (step : Fin (routes.length level token)) :
    (routes.point level token step.val).2.2 < 16 * (layers : ℤ) := by
  have hs := routes.slab level token step.val (by omega)
  have hl := level.isLt
  have hne : (routes.point level token step.val).2.2 ≠ 16 * (level.val + 1 : ℕ) := by
    intro he
    have hh := routes.upper_index level token step.val (by omega) he
    omega
  omega

/-- Concatenating the layers produces simple, pairwise disjoint actual
trajectories; the vertex indexing removes the duplicated shared ports. -/
theorem trajectory_embedding_injective {Token : Type*} {layers : ℕ}
    (routes : LayeredRoutes Token layers) :
    Function.Injective (fun entry : Σ token, TrajectoryIndex routes token =>
      trajectoryPoint routes entry.1 entry.2) := by
  intro x y hxy
  rcases x with ⟨a, x⟩
  rcases y with ⟨b, y⟩
  cases x with
  | inl x =>
    rcases x with ⟨l, i⟩
    cases y with
    | inl y =>
      rcases y with ⟨k, j⟩
      change routes.point l a i.val = routes.point k b j.val at hxy
      have hab := token_trajectories_disjoint routes l k a b i.val j.val (by omega) (by omega) hxy
      subst b
      have hlk : l = k := by
        by_cases hl : l.val ≤ k.val
        · have hh := (ordered_overlap routes l k a a i.val j.val (by omega) (by omega) hl hxy).2
          rcases hh with hsame | hnext
          · exact hsame.1
          · omega
        · have hh := (ordered_overlap routes k l a a j.val i.val (by omega) (by omega) (by omega) hxy.symm).2
          rcases hh with hsame | hnext
          · exact hsame.1.symm
          · omega
      subst k
      have hij := (routes.layer_injective l a a i.val j.val (by omega) (by omega) hxy).2
      have he : i = j := Fin.ext hij
      subst j
      rfl
    | inr u =>
      change routes.point l a i.val = routes.port (Fin.last layers) b at hxy
      have hz := congrArg (fun p : Point => p.2.2) hxy
      rw [routes.port_height] at hz
      have hb := stored_vertex_below_end routes l a i
      simp only [Fin.val_last] at hz
      omega
  | inr u =>
    cases y with
    | inl y =>
      rcases y with ⟨k, j⟩
      change routes.port (Fin.last layers) a = routes.point k b j.val at hxy
      have hz := congrArg (fun p : Point => p.2.2) hxy
      rw [routes.port_height] at hz
      have hb := stored_vertex_below_end routes k b j
      simp only [Fin.val_last] at hz
      omega
    | inr v =>
      change routes.port (Fin.last layers) a = routes.port (Fin.last layers) b at hxy
      have hab := routes.port_injective (Fin.last layers) hxy
      subst b
      cases u
      cases v
      rfl

end Maxwell.Logical.Routing.Assembly
