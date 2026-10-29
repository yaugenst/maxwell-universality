import Maxwell.Logical.Routing.GraphData

/-! Executable routing data on the emitted finite vertex and edge indices.
All indexing is arithmetic. Incidence arms are supplied by the stored
counter pass, and the permutation uses the marked-array completion. -/

namespace Maxwell.Logical.Routing.Gluing

def incidenceIndex (edges : ℕ) : (Fin edges × Bool) ≃ Fin (Fintype.card (Fin edges × Bool)) :=
  ((Equiv.refl (Fin edges)).prodCongr finTwoEquiv.symm).trans
    (finProdFinEquiv.trans (finCongr (by simp)))

def indexedGraphData {vertices edges : ℕ} (part : Fin vertices → Bool)
    (endpoint : Fin edges → Bool → Fin vertices)
    (hpart : ∀ e b, part (endpoint e b) = b)
    (arm : Fin edges → Bool → Fin 3)
    (ha : Function.Injective (fun p : Fin edges × Bool => (endpoint p.1 p.2, arm p.1 p.2))) :
    Data (Fin vertices) (Fin edges) (portHalfSide vertices) := by
  let half := portHalfSide vertices
  have htiles : vertices ≤ half * half := by
    change vertices ≤ portHalfSide vertices * portHalfSide vertices
    rw [← pow_two, portHalfSide_square]
    exact Nat.le_pow_clog (by decide) _
  let tile : Fin vertices → Port half := fun v => finProdFinEquiv.symm (Fin.castLE htiles v)
  have ht : Function.Injective tile := by
    intro x y h
    exact Fin.ext (congrArg (fun k : Fin (half * half) => k.val) (finProdFinEquiv.symm.injective h))
  have hcard := Fintype.card_le_of_injective _ ha
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at hcard
  have hpairs : edges ≤ half * (2 * half) := by nlinarith
  let pair : Fin edges → Fin half × Fin (2 * half) := fun e =>
    finProdFinEquiv.symm (Fin.castLE hpairs e)
  have hp : Function.Injective pair := by
    intro x y h
    exact Fin.ext (congrArg (fun k : Fin (half * (2 * half)) => k.val)
      (finProdFinEquiv.symm.injective h))
  let source : Fin edges × Bool → Port (2 * half) := fun p =>
    tilePort (tile (endpoint p.1 p.2)) (arm p.1 p.2)
  have hs : Function.Injective source := by
    intro a b hab
    have hh := (tilePort_injective half)
      (a₁ := (tile (endpoint a.1 a.2), arm a.1 a.2))
      (a₂ := (tile (endpoint b.1 b.2), arm b.1 b.2)) hab
    apply ha
    exact Prod.ext (ht (congrArg (fun p : Port half × Fin 3 => p.1) hh))
      (congrArg (fun p : Port half × Fin 3 => p.2) hh)
  let destination : Fin edges × Bool → Port (2 * half) := fun p => pairPort (pair p.1) p.2
  have hd : Function.Injective destination := by
    intro a b hab
    have hh := (pairPort_injective half) (a₁ := (pair a.1, a.2)) (a₂ := (pair b.1, b.2)) hab
    exact Prod.ext (hp (congrArg (fun p : (Fin half × Fin (2 * half)) × Bool => p.1) hh))
      (congrArg (fun p : (Fin half × Fin (2 * half)) × Bool => p.2) hh)
  let target := completePorts (incidenceIndex edges) source destination hs hd
  have htarget := completePorts_exact (incidenceIndex edges) source destination hs hd
  have heq : 2 * half = 2 ^ (Nat.clog 4 vertices + 1) := portSide_power_two _
  let colors : RowColoring target := powerColoring _ _ heq target
  exact ⟨tile, ht, part, endpoint, hpart, arm, ha, pair, hp, target,
    fun e b => htarget (e, b), colors⟩

/-- Relabeling preserves every routing invariant while keeping exactly the
same stored target permutation and coloring. -/
def transportData {V E W F : Type*} {half : ℕ} (vertex : V ≃ W) (edge : E ≃ F)
    (data : Data W F half) : Data V E half where
  tile v := data.tile (vertex v)
  tile_injective := data.tile_injective.comp vertex.injective
  part v := data.part (vertex v)
  endpoint e b := vertex.symm (data.endpoint (edge e) b)
  endpoint_part e b := by simpa only [Equiv.apply_symm_apply] using data.endpoint_part (edge e) b
  arm e b := data.arm (edge e) b
  incidence_injective := by
    intro a b h
    have ht : (data.endpoint (edge a.1) a.2, data.arm (edge a.1) a.2) =
        (data.endpoint (edge b.1) b.2, data.arm (edge b.1) b.2) := by
      have hh := congrArg (fun p : V × Fin 3 => (vertex p.1, p.2)) h
      simpa only [Equiv.apply_symm_apply] using hh
    have hi := data.incidence_injective (a₁ := (edge a.1, a.2)) (a₂ := (edge b.1, b.2)) ht
    exact Prod.ext (edge.injective (congrArg (fun p : F × Bool => p.1) hi))
      (congrArg (fun p : F × Bool => p.2) hi)
  pair e := data.pair (edge e)
  pair_injective := data.pair_injective.comp edge.injective
  target := data.target
  target_incidence e b := by
    simpa only [Equiv.apply_symm_apply] using data.target_incidence (edge e) b
  colors := data.colors

end Maxwell.Logical.Routing.Gluing
