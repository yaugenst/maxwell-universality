import Maxwell.Continuum.SourceRoutingOriginalStep

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
open Structured GeometryArithmetic GeometryPath Maxwell.Logical.Routing
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def originalPrefix {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (offset count : ℕ) : List Point :=
  ((List.ofFn (Gluing.vertexPoint data)).drop offset).take count

theorem originalPrefix_zero {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half) (offset : ℕ) :
    originalPrefix data offset 0=[] := by simp [originalPrefix]

theorem originalPrefix_length {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (offset count : ℕ) (bound : offset+count≤v) :
    (originalPrefix data offset count).length=count := by
  simp only [originalPrefix,List.length_take,List.length_drop,List.length_ofFn]
  omega

theorem originalPrefix_succ {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (offset count : ℕ) (bound : offset+count<v) :
    originalPrefix data offset (count+1)=
      originalPrefix data offset count++[Gluing.vertexPoint data ⟨offset+count,bound⟩] := by
  unfold originalPrefix
  rw [List.take_succ_eq_append_getElem (by simp only [List.length_drop,List.length_ofFn];omega)]
  simp only [List.getElem_drop,List.getElem_ofFn]

theorem originalPrefix_append {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half)
    (left right : ℕ) :
    originalPrefix data 0 left++originalPrefix data left right=originalPrefix data 0 (left+right) := by
  simp only [originalPrefix,List.drop_zero]
  exact List.take_add.symm

theorem originalPrefix_end {v e half : ℕ} (data : Gluing.Data (Fin v) (Fin e) half) :
    originalPrefix data 0 v=List.ofFn (Gluing.vertexPoint data) := by
  simp [originalPrefix]

#print axioms originalPrefix_succ
end Maxwell.Cost.RoutingPorts.Complete.GeometryEmission
