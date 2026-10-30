import Maxwell.Continuum.SourceGeometryRecords

/-! Index-dependent record streams concatenate with the exact preceding
record count. These lemmas identify the runtime passes with one list. -/
namespace Maxwell.Continuum.IndexedRecordStream
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def bits {α β : Type*} (f : ℕ→α→List β) (xs : List α) (first : ℕ) : List β :=
  (xs.zipIdx first).flatMap (fun p=>f p.2 p.1)

theorem append {α β : Type*} (f : ℕ→α→List β) (xs ys : List α) (first : ℕ) :
    bits f (xs++ys) first=bits f xs first++bits f ys (first+xs.length) := by
  simp only [bits,List.zipIdx_append,List.flatMap_append]

theorem map {α β γ : Type*} (f : ℕ→β→List γ) (g : α→β) (xs : List α) (first : ℕ) :
    bits f (xs.map g) first=bits (fun i x=>f i (g x)) xs first := by
  simp only [bits,List.zipIdx_map,List.flatMap_map]
  rfl

theorem zipIdx_eq_range {α : Type*} [Inhabited α] (xs : List α) (first : ℕ) :
    xs.zipIdx first=(List.range xs.length).map (fun i=>(xs[i]?.getD default,first+i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hix : i<xs.length := by simpa only [List.length_zipIdx] using hi
    simp only [List.getElem_zipIdx,List.getElem_map,List.getElem_range,
      List.getElem?_eq_getElem hix,Option.getD_some]

theorem eq_range {α β : Type*} [Inhabited α] (f : ℕ→α→List β) (xs : List α) (first : ℕ) :
    bits f xs first=(List.range xs.length).flatMap (fun i=>f (first+i) (xs[i]?.getD default)) := by
  rw [bits,zipIdx_eq_range,List.flatMap_map]

theorem ofFn {α β : Type*} (f : ℕ→α→List β) {n : ℕ} (xs : Fin n→α) (first : ℕ) :
    bits f (List.ofFn xs) first=(List.finRange n).flatMap (fun i=>f (first+i.val) (xs i)) := by
  have he : (List.ofFn xs).zipIdx first=(List.finRange n).map (fun i=>(xs i,first+i.val)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_zipIdx,List.getElem_ofFn,List.getElem_map,List.getElem_finRange]
      rfl
  rw [bits,he,List.flatMap_map]

theorem congr {α β : Type*} (f g : ℕ→α→List β) (xs : List α) (first : ℕ)
    (h : ∀p∈xs.zipIdx first,f p.2 p.1=g p.2 p.1) : bits f xs first=bits g xs first := by
  apply List.flatMap_congr
  exact h

#print axioms append
#print axioms eq_range
end Maxwell.Continuum.IndexedRecordStream
