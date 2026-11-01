import Maxwell.Cost.Array

/-! A contiguous exact write constructs a fixed-width array from arbitrary
initial memory. This boundary is independent of the encoded objects. -/
namespace Maxwell.Cost.BitArray

theorem uniform_flatMap_length {α β : Type*} (xs : List α) (f : α→List β) (width : ℕ)
    (h : ∀x∈xs,(f x).length=width) : (xs.flatMap f).length=xs.length*width := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    rw [h x (by simp),ih (fun y hy=>h y (by simp [hy]))]
    ring

theorem uniform_flatMap_get {α β : Type*} (xs : List α) (f : α→List β) (width j i : ℕ)
    (h : ∀x∈xs,(f x).length=width) (hj : j<xs.length) (hi : i<width) :
    (xs.flatMap f)[j*width+i]'(by rw [uniform_flatMap_length xs f width h];nlinarith)=
      (f xs[j])[i]'(by rw [h _ (List.getElem_mem hj)];exact hi) := by
  induction xs generalizing j with
  | nil=>simp at hj
  | cons x xs ih=>
    have hx:=h x (by simp)
    have ht : ∀y∈xs,(f y).length=width:=fun y hy=>h y (by simp [hy])
    cases j with
    | zero=>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.getElem_append_left (by omega)]
    | succ j=>
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      rw [List.getElem_append_right (by rw [hx];nlinarith)]
      have he : (j+1)*width+i-(f x).length=j*width+i:=by
        rw [hx];simp only [Nat.add_mul,one_mul];omega
      simpa only [he] using ih j ht (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj)

theorem represents_flatMap {α : Type*} {n : ℕ} (values : Vector α n) (encode : α→List Bool)
    (width : ℕ) (uniform : ∀i,(encode (values.get i)).length=width)
    (memory : ℕ→Bool) (base : ℕ) :
    Represents (MemoryWord.writeBits memory base ((List.ofFn values.get).flatMap encode))
      base width (values.map encode) := by
  have length (i : Fin n) : ((values.map encode).get i).length=width:=by
    simpa [Vector.get,Fin.cast] using uniform i
  refine ⟨length,?_⟩
  intro i j hj
  have hlen : ∀x∈List.ofFn values.get,(encode x).length=width:=by
    intro x hx
    obtain ⟨a,rfl⟩:=List.mem_ofFn.mp hx
    exact uniform a
  have within : i.val*width+j<((List.ofFn values.get).flatMap encode).length:=by
    rw [uniform_flatMap_length _ _ _ hlen,List.length_ofFn]
    nlinarith [i.isLt]
  rw [Nat.add_assoc,MemoryWord.writeBits_inside memory base _ _ within]
  have hg:=uniform_flatMap_get (List.ofFn values.get) encode width i.val j hlen
    (by simpa only [List.length_ofFn] using i.isLt) hj
  simpa [Vector.get,Fin.cast] using hg

#print axioms represents_flatMap
end Maxwell.Cost.BitArray
