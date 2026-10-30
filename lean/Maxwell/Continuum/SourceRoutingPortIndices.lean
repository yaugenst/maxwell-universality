import Maxwell.Logical.Routing.IndexedData

/-! Arithmetic port addresses for the exact indexed graph construction. -/

namespace Maxwell.Cost.RoutingPorts.Complete.PortIndices
open Maxwell.Logical.Routing Maxwell.Logical.Routing.Gluing
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

def sourceIndex (half vertex arm : ℕ) : ℕ :=
  (2*(vertex/half)+arm%2)*(2*half)+(2*(vertex%half)+arm/2)
def targetIndex (half incidence : ℕ) : ℕ :=
  (2*((incidence/2)/(2*half))+incidence%2)*(2*half)+(incidence/2)%(2*half)

theorem source_exact (half : ℕ) (vertex : Fin (half*half)) (arm : Fin 3) :
    (finProdFinEquiv (tilePort (finProdFinEquiv.symm vertex) arm)).val=
      sourceIndex half vertex.val arm.val := by
  fin_cases arm <;> simp [sourceIndex,tilePort,finProdFinEquiv] <;> ring

theorem pair_exact (half : ℕ) (edge : Fin (half*(2*half))) (side : Bool) :
    (finProdFinEquiv (pairPort (finProdFinEquiv.symm edge) side)).val=
      targetIndex half (2*edge.val+if side then 1 else 0) := by
  have hd (n : ℕ) : (2*n+1)/2=n := by omega
  cases side <;> simp [targetIndex,pairPort,finProdFinEquiv,hd] <;> ring

theorem incidenceIndex_value {edges : ℕ} (edge : Fin edges) (side : Bool) :
    (incidenceIndex edges (edge,side)).val=2*edge.val+if side then 1 else 0 := by
  cases side <;> simp [incidenceIndex,finProdFinEquiv,finTwoEquiv]
  omega

theorem source_lt (half vertex arm : ℕ) (hv : vertex<half*half) (ha : arm<3) :
    sourceIndex half vertex arm<(2*half)*(2*half) := by
  rw [←source_exact half ⟨vertex,hv⟩ ⟨arm,ha⟩]
  exact (finProdFinEquiv (tilePort (finProdFinEquiv.symm ⟨vertex,hv⟩) ⟨arm,ha⟩)).isLt

theorem target_lt (half incidence : ℕ) (hi : incidence<2*(half*(2*half))) :
    targetIndex half incidence<(2*half)*(2*half) := by
  have he : incidence/2<half*(2*half) := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  have hside : incidence%2=if incidence%2=1 then 1 else 0 := by
    have hh := Nat.mod_lt incidence (by decide : 0<2)
    split_ifs <;> omega
  let side : Bool := decide (incidence%2=1)
  have hvalue : 2*(incidence/2)+(if side then 1 else 0)=incidence := by
    have hh := Nat.mod_add_div incidence 2
    simp only [side,Bool.decide_iff]
    rw [←hside]
    omega
  rw [←hvalue,←pair_exact half ⟨incidence/2,he⟩ side]
  exact (finProdFinEquiv (pairPort (finProdFinEquiv.symm ⟨incidence/2,he⟩) side)).isLt

#print axioms source_exact
#print axioms pair_exact

end Maxwell.Cost.RoutingPorts.Complete.PortIndices
