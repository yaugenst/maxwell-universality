import Maxwell.Cost.PhysicalMaterial.DenseFill

namespace Maxwell.Cost.PhysicalMaterial.Scatter
open Structured RationalAccumulator

/-- Read-only anchor/strength records are allocated outside both dense output
arrays. This is the exact memory-allocation condition used by scatter. -/
structure SeparatedData {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells) : Prop where
  num : ∀ port, IncidenceEncoding.Separated (addressValue (d.bases port))
    (n*addressValue d.width) (addressValue l.numBase) (cells*addressValue l.width)
  den : ∀ port, IncidenceEncoding.Separated (addressValue (d.bases port))
    (n*addressValue d.width) (addressValue l.denBase) (cells*addressValue l.width)

/-- The dense writer's global footprint preserves all actual descriptor bits,
even when their array bases and lengths are runtime values. -/
theorem preserve_descriptors {n cells : ℕ} (d : Descriptors.Data n) (l : Dense.Layout cells)
    (hsep : SeparatedData d l) {s t : BitRAMState} (h : Descriptors.Stored d s)
    (hout : Dense.Outside l s t)
    (ht : ∀ j, j = 300 ∨ j = 301 ∨ (310 ≤ j ∧ j ≤ 314) → t.tapes j = s.tapes j) :
    Descriptors.Stored d t := by
  refine ⟨BankArray.word_of_eq (ht 300 (by omega)) h.width,
    BankArray.word_of_eq (ht 301 (by omega)) h.clock, ?_, ?_⟩
  · intro port
    exact BankArray.word_of_eq (ht (Descriptors.baseTape port)
      (by simp only [Descriptors.baseTape]; omega)) (h.bases port)
  · intro port
    refine ⟨(h.arrays port).length, ?_⟩
    intro i j hj
    have hi := Nat.mul_le_mul_right (addressValue d.width) (show i.val+1 ≤ n by omega)
    have outside (base length : ℕ)
        (hs : IncidenceEncoding.Separated (addressValue (d.bases port))
          (n*addressValue d.width) base length) :
        addressValue (d.bases port)+i.val*addressValue d.width+j < base ∨
        base+length ≤ addressValue (d.bases port)+i.val*addressValue d.width+j := by
      rcases hs with hs | hs
      · left; nlinarith
      · right; omega
    rw [hout _ (outside _ _ (hsep.num port)) (outside _ _ (hsep.den port))]
    exact (h.arrays port).bits i j hj

/-- Exact pure semantics of the finite local scatter sequence. The machine
computes each index before applying the corresponding vector update. -/
def scatterWords {cells : ℕ} (words : Vector (List Bool) cells)
    (indices : List (Fin cells)) (payload : List Bool) : Vector (List Bool) cells :=
  indices.foldl (fun v (i : Fin cells) => v.set i payload) words

@[simp] theorem scatterWords_nil {cells : ℕ} (words : Vector (List Bool) cells) (payload : List Bool) :
    scatterWords words [] payload = words := rfl

@[simp] theorem scatterWords_cons {cells : ℕ} (words : Vector (List Bool) cells)
    (i : Fin cells) (rest : List (Fin cells)) (payload : List Bool) :
    scatterWords words (i::rest) payload = scatterWords (words.set i payload) rest payload := rfl

theorem scatterWords_get {cells : ℕ} (words : Vector (List Bool) cells)
    (indices : List (Fin cells)) (payload : List Bool) (i : Fin cells) :
    (scatterWords words indices payload).get i = if i ∈ indices then payload else words.get i := by
  induction indices generalizing words with
  | nil => simp
  | cons j rest ih =>
    rw [scatterWords_cons, ih]
    by_cases hir : i ∈ rest
    · simp [hir]
    · by_cases hij : i = j
      · subst i
        simp [hir, Vector.get, Fin.cast]
      · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        simp [hir, hij, Vector.get, Fin.cast, Ne.symm hne]

end Maxwell.Cost.PhysicalMaterial.Scatter
