import Maxwell.Logical.Routing.Gluing
import Maxwell.Logical.Routing.Coloring
import Maxwell.Logical.Routing.DummyFill
import Mathlib.Data.Fintype.EquivFin

/-! Construction of the local routing data from finite bipartite degree-three
graphs. The finite indexing in this module is a specification; its machine
cost requires binding the finite enumerations to the emitted adjacency lists. -/

namespace Maxwell.Logical.Routing.Gluing

noncomputable def gridIndex {X : Type*} [Fintype X] (a b : ℕ) (h : Fintype.card X ≤ a * b) :
    X → Fin a × Fin b :=
  fun x => finProdFinEquiv.symm (Fin.castLE h ((Fintype.equivFin X) x))

theorem gridIndex_injective {X : Type*} [Fintype X] (a b : ℕ)
    (h : Fintype.card X ≤ a * b) : Function.Injective (gridIndex a b h : X → _) := by
  intro x y hxy
  apply (Fintype.equivFin X).injective
  apply Fin.ext
  exact congrArg (fun k : Fin (a * b) => k.val) (finProdFinEquiv.symm.injective hxy)

abbrev Fiber {X V : Type*} (f : X → V) (v : V) := {x : X // f x = v}

noncomputable def fiberIndex {X V : Type*} [Fintype X] [DecidableEq V] (f : X → V)
    (h : ∀ v, Fintype.card (Fiber f v) ≤ 3) (x : X) : Fin 3 :=
  Fin.castLE (h (f x)) ((Fintype.equivFin (Fiber f (f x))) ⟨x, rfl⟩)

theorem fiberIndex_at {X V : Type*} [Fintype X] [DecidableEq V] (f : X → V)
    (h : ∀ v, Fintype.card (Fiber f v) ≤ 3) (v : V) (x : X) (hx : f x = v) :
    fiberIndex f h x = Fin.castLE (h v) ((Fintype.equivFin (Fiber f v)) ⟨x, hx⟩) := by
  subst v
  rfl

theorem fiberIndex_injective {X V : Type*} [Fintype X] [DecidableEq V] (f : X → V)
    (h : ∀ v, Fintype.card (Fiber f v) ≤ 3) :
    Function.Injective (fun x => (f x, fiberIndex f h x)) := by
  intro x y he
  have hv := congrArg Prod.fst he
  have hl := congrArg Prod.snd he
  change f x = f y at hv
  change fiberIndex f h x = fiberIndex f h y at hl
  rw [fiberIndex_at f h (f x) y hv.symm] at hl
  have hi : ((Fintype.equivFin (Fiber f (f x))) ⟨x, rfl⟩) =
      ((Fintype.equivFin (Fiber f (f x))) ⟨y, hv.symm⟩) :=
    Fin.ext (congrArg (fun k : Fin 3 => k.val) hl)
  exact congrArg Subtype.val ((Fintype.equivFin (Fiber f (f x))).injective hi)

def powerColoring (q n : ℕ) (he : q = 2 ^ n) (target : Equiv.Perm (Port q)) :
    RowColoring target := by
  subst q
  exact Coloring.rowColoring n target

/-- Complete the prescribed ports with the deterministic marked-array
algorithm, after the supplied finite incidence enumeration. -/
def completePorts {X : Type*} [Fintype X] {q : ℕ}
    (index : X ≃ Fin (Fintype.card X)) (source target : X → Port q)
    (hs : Function.Injective source) (ht : Function.Injective target) : Equiv.Perm (Port q) :=
  let src := fun i => finProdFinEquiv (source (index.symm i))
  let dst := fun i => finProdFinEquiv (target (index.symm i))
  let fill := DummyFill.extension src dst
    (finProdFinEquiv.injective.comp (hs.comp index.symm.injective))
    (finProdFinEquiv.injective.comp (ht.comp index.symm.injective))
  (finProdFinEquiv.trans fill).trans finProdFinEquiv.symm

theorem completePorts_exact {X : Type*} [Fintype X] {q : ℕ}
    (index : X ≃ Fin (Fintype.card X)) (source target : X → Port q)
    (hs : Function.Injective source) (ht : Function.Injective target) (x : X) :
    completePorts index source target hs ht (source x) = target x := by
  have h := DummyFill.exact_extension
    (fun i => finProdFinEquiv (source (index.symm i)))
    (fun i => finProdFinEquiv (target (index.symm i)))
    (finProdFinEquiv.injective.comp (hs.comp index.symm.injective))
    (finProdFinEquiv.injective.comp (ht.comp index.symm.injective)) (index x)
  simpa only [completePorts, Equiv.trans_apply, Equiv.symm_apply_apply] using
    congrArg finProdFinEquiv.symm h

noncomputable def finiteGraphData {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (part : V → Bool) (endpoint : E → Bool → V)
    (hpart : ∀ e b, part (endpoint e b) = b)
    (hdegree : ∀ v, Fintype.card (Fiber (fun p : E × Bool => endpoint p.1 p.2) v) ≤ 3) :
    Data V E (portHalfSide (Fintype.card V)) := by
  let half := portHalfSide (Fintype.card V)
  have htiles : Fintype.card V ≤ half * half := by
    change Fintype.card V ≤ portHalfSide (Fintype.card V) * portHalfSide (Fintype.card V)
    rw [← pow_two, portHalfSide_square]
    exact Nat.le_pow_clog (by decide) _
  let tile : V → Port half := gridIndex half half htiles
  have ht : Function.Injective tile := gridIndex_injective half half htiles
  let ep : E × Bool → V := fun p => endpoint p.1 p.2
  let arm : E → Bool → Fin 3 := fun e b => fiberIndex ep hdegree (e, b)
  have ha : Function.Injective (fun p : E × Bool => (endpoint p.1 p.2, arm p.1 p.2)) :=
    fiberIndex_injective ep hdegree
  have hcard := Fintype.card_le_of_injective _ ha
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at hcard
  have hpairs : Fintype.card E ≤ half * (2 * half) := by nlinarith
  let pair : E → Fin half × Fin (2 * half) := gridIndex half (2 * half) hpairs
  have hp : Function.Injective pair := gridIndex_injective half (2 * half) hpairs
  let source : E × Bool → Port (2 * half) := fun p => tilePort (tile (endpoint p.1 p.2)) (arm p.1 p.2)
  have hs : Function.Injective source := by
    intro a b hab
    have hh := (tilePort_injective half)
      (a₁ := (tile (endpoint a.1 a.2), arm a.1 a.2))
      (a₂ := (tile (endpoint b.1 b.2), arm b.1 b.2)) hab
    apply ha
    exact Prod.ext (ht (congrArg (fun p : Port half × Fin 3 => p.1) hh))
      (congrArg (fun p : Port half × Fin 3 => p.2) hh)
  let destination : E × Bool → Port (2 * half) := fun p => pairPort (pair p.1) p.2
  have hd : Function.Injective destination := by
    intro a b hab
    have hh := (pairPort_injective half) (a₁ := (pair a.1, a.2)) (a₂ := (pair b.1, b.2)) hab
    exact Prod.ext (hp (congrArg (fun p : (Fin half × Fin (2 * half)) × Bool => p.1) hh))
      (congrArg (fun p : (Fin half × Fin (2 * half)) × Bool => p.2) hh)
  let target := completePorts (Fintype.equivFin (E × Bool)) source destination hs hd
  have htarget := completePorts_exact (Fintype.equivFin (E × Bool)) source destination hs hd
  have heq : 2 * half = 2 ^ (Nat.clog 4 (Fintype.card V) + 1) := portSide_power_two _
  let colors : RowColoring target := powerColoring _ _ heq target
  exact ⟨tile, ht, part, endpoint, hpart, arm, ha, pair, hp, target,
    fun e b => htarget (e, b), colors⟩

end Maxwell.Logical.Routing.Gluing
