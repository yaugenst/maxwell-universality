import Maxwell.Logical.Routing.IncidenceRanks
import Maxwell.Cost.Array
import Maxwell.Cost.FixedWidth
import Maxwell.Cost.Counter
import Mathlib.Data.Nat.Size

/-! Fixed-width bit memory for the incidence-rank pass. The representation
is preserved by the actual bit writer's two array updates. -/

namespace Maxwell.Cost.IncidenceEncoding

open Maxwell.Logical.Routing

/-- A little-endian natural word, padded to its declared width. -/
def word (width value : ℕ) : List Bool := FixedWidth.bits width value.bits

def words {n : ℕ} (width : ℕ) (values : Vector ℕ n) : Vector (List Bool) n :=
  values.map (word width)

@[simp] theorem word_length (width value : ℕ) : (word width value).length = width :=
  FixedWidth.bits_length _ _

theorem word_value (width value : ℕ) (h : value < 2 ^ width) :
    addressValue (word width value) = value := by
  rw [word, FixedWidth.bits_value, addressValue_bits]
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

@[simp] theorem words_get {n : ℕ} (width : ℕ) (values : Vector ℕ n) (i : Fin n) :
    (words width values).get i = word width (values.get i) := by
  simp [words, Vector.get, Fin.cast]

@[simp] theorem words_length {n : ℕ} (width : ℕ) (values : Vector ℕ n) (i : Fin n) :
    ((words width values).get i).length = width := by simp

theorem words_value {n : ℕ} (width : ℕ) (values : Vector ℕ n) (i : Fin n)
    (h : values.get i < 2 ^ width) :
    addressValue ((words width values).get i) = values.get i := by
  rw [words_get]
  exact word_value _ _ h

@[simp] theorem words_set {n : ℕ} (width : ℕ) (values : Vector ℕ n) (i : Fin n) (value : ℕ) :
    words width (values.set i.val value i.isLt) =
      (words width values).set i.val (word width value) i.isLt := by
  simp only [words, Vector.map_set]

theorem word_two_value (value : ℕ) (h : value ≤ 3) :
    addressValue (word 2 value) = value := word_value _ _ (by omega)

/-- Half-open bit intervals do not overlap; adjacency is allowed. -/
def Separated (baseA lengthA baseB lengthB : ℕ) : Prop :=
  baseA + lengthA ≤ baseB ∨ baseB + lengthB ≤ baseA

theorem Separated.symm {a n b m : ℕ} (h : Separated a n b m) : Separated b m a n :=
  Or.symm h

/-- Writing a slot in a disjoint array preserves every represented bit. -/
theorem represents_write_disjoint {n m : ℕ} {memory : ℕ → Bool}
    {base width : ℕ} {values : Vector (List Bool) n}
    (h : BitArray.Represents memory base width values)
    (writeBase writeWidth : ℕ) (slot : Fin m) (payload : List Bool)
    (hlen : payload.length = writeWidth)
    (hsep : Separated base (n * width) writeBase (m * writeWidth)) :
    BitArray.Represents
      (MemoryWord.writeBits memory (writeBase + slot.val * writeWidth) payload)
      base width values := by
  refine ⟨h.length, ?_⟩
  intro i j hj
  rw [MemoryWord.writeBits_outside]
  · exact h.bits i j hj
  · have hi := Nat.mul_le_mul_right width (show i.val + 1 ≤ n by omega)
    have hs := Nat.mul_le_mul_right writeWidth (show slot.val + 1 ≤ m by omega)
    rcases hsep with hsep | hsep
    · left
      nlinarith
    · right
      rw [hlen]
      nlinarith

/-- Addresses for the endpoint array and the two two-bit saved arrays. -/
structure Layout where
  endpointWidth : ℕ
  baseEndpoint : ℕ
  baseCounter : ℕ
  baseRank : ℕ

structure Layout.Separated (layout : Layout) (vertices incidences : ℕ) : Prop where
  endpointCounter : IncidenceEncoding.Separated layout.baseEndpoint (incidences * layout.endpointWidth)
    layout.baseCounter (vertices * 2)
  endpointRank : IncidenceEncoding.Separated layout.baseEndpoint (incidences * layout.endpointWidth)
    layout.baseRank (incidences * 2)
  counterRank : IncidenceEncoding.Separated layout.baseCounter (vertices * 2) layout.baseRank (incidences * 2)

/-- A contiguous layout uses no unused memory between its three arrays. -/
def Layout.packed (vertices incidences endpointWidth : ℕ) : Layout :=
  ⟨endpointWidth, 0, incidences * endpointWidth, incidences * endpointWidth + vertices * 2⟩

theorem Layout.packed_separated (vertices incidences endpointWidth : ℕ) :
    (Layout.packed vertices incidences endpointWidth).Separated vertices incidences := by
  constructor <;> exact Or.inl (by simp [Layout.packed])

def endpointValues {vertices incidences : ℕ} (endpoint : Fin incidences → Fin vertices) :
    Vector ℕ incidences := Vector.ofFn (fun i => (endpoint i).val)

@[simp] theorem endpointValues_get {vertices incidences : ℕ}
    (endpoint : Fin incidences → Fin vertices) (i : Fin incidences) :
    (endpointValues endpoint).get i = (endpoint i).val := by
  simp [endpointValues, Vector.get, Fin.cast]

/-- The complete memory relation for the pure incidence pass. -/
structure Represents {vertices incidences : ℕ} (layout : Layout) (memory : ℕ → Bool)
    (endpoint : Fin incidences → Fin vertices) (saved : IncidenceRanks.State vertices incidences) : Prop where
  endpoints : BitArray.Represents memory layout.baseEndpoint layout.endpointWidth
    (words layout.endpointWidth (endpointValues endpoint))
  counters : BitArray.Represents memory layout.baseCounter 2 (words 2 saved.counters)
  ranks : BitArray.Represents memory layout.baseRank 2 (words 2 saved.ranks)

theorem Represents.read_endpoint {vertices incidences : ℕ} {layout : Layout}
    {memory : ℕ → Bool} {endpoint : Fin incidences → Fin vertices}
    {saved : IncidenceRanks.State vertices incidences} (h : Represents layout memory endpoint saved)
    (i : Fin incidences) (hwidth : vertices ≤ 2 ^ layout.endpointWidth) :
    addressValue (MemoryWord.readBits memory
      (layout.baseEndpoint + i.val * layout.endpointWidth) layout.endpointWidth) = (endpoint i).val := by
  rw [h.endpoints.read, words_get, endpointValues_get]
  exact word_value _ _ (lt_of_lt_of_le (endpoint i).isLt hwidth)

theorem Represents.read_counter {vertices incidences : ℕ} {layout : Layout}
    {memory : ℕ → Bool} {endpoint : Fin incidences → Fin vertices}
    {saved : IncidenceRanks.State vertices incidences} (h : Represents layout memory endpoint saved)
    (i : Fin vertices) (hvalue : saved.counters.get i ≤ 3) :
    addressValue (MemoryWord.readBits memory (layout.baseCounter + i.val * 2) 2) =
      saved.counters.get i := by
  rw [h.counters.read, words_get]
  exact word_two_value _ hvalue

theorem Represents.read_rank {vertices incidences : ℕ} {layout : Layout}
    {memory : ℕ → Bool} {endpoint : Fin incidences → Fin vertices}
    {saved : IncidenceRanks.State vertices incidences} (h : Represents layout memory endpoint saved)
    (i : Fin incidences) (hvalue : saved.ranks.get i ≤ 3) :
    addressValue (MemoryWord.readBits memory (layout.baseRank + i.val * 2) 2) =
      saved.ranks.get i := by
  rw [h.ranks.read, words_get]
  exact word_two_value _ hvalue

/-- The two bit writes made by one incidence step. -/
def stepMemory {vertices incidences : ℕ} (layout : Layout)
    (endpoint : Fin incidences → Fin vertices) (i : Fin incidences)
    (saved : IncidenceRanks.State vertices incidences) (memory : ℕ → Bool) : ℕ → Bool :=
  let vertex := endpoint i
  let rank := saved.counters.get vertex
  MemoryWord.writeBits
    (MemoryWord.writeBits memory (layout.baseCounter + vertex.val * 2) (word 2 (rank + 1)))
    (layout.baseRank + i.val * 2) (word 2 rank)

/-- The actual bit writer's updates realize exactly the saved counter/rank
step, while preserving the endpoint array and every other slot. -/
theorem represents_step {vertices incidences : ℕ} {layout : Layout} {memory : ℕ → Bool}
    {endpoint : Fin incidences → Fin vertices} {saved : IncidenceRanks.State vertices incidences}
    (h : Represents layout memory endpoint saved) (hs : layout.Separated vertices incidences)
    (i : Fin incidences) :
    Represents layout (stepMemory layout endpoint i saved memory) endpoint
      (IncidenceRanks.step endpoint i saved) := by
  let rank := saved.counters.get (endpoint i)
  let updated := MemoryWord.writeBits memory
    (layout.baseCounter + (endpoint i).val * 2) (word 2 (rank + 1))
  have hc : BitArray.Represents updated layout.baseCounter 2
      (words 2 (saved.counters.set (endpoint i).val (rank + 1) (endpoint i).isLt)) := by
    simpa only [words_set] using h.counters.write (endpoint i) (word 2 (rank + 1)) (word_length _ _)
  have he := represents_write_disjoint h.endpoints layout.baseCounter 2 (endpoint i)
    (word 2 (rank + 1)) (word_length _ _) hs.endpointCounter
  have hr := represents_write_disjoint h.ranks layout.baseCounter 2 (endpoint i)
    (word 2 (rank + 1)) (word_length _ _) hs.counterRank.symm
  refine ⟨?_, ?_, ?_⟩
  · exact represents_write_disjoint he layout.baseRank 2 i (word 2 rank)
      (word_length _ _) hs.endpointRank
  · exact represents_write_disjoint hc layout.baseRank 2 i (word 2 rank)
      (word_length _ _) hs.counterRank
  · simpa only [IncidenceRanks.step, stepMemory, words_set, rank] using
      hr.write i (word 2 rank) (word_length _ _)

/-- Degree three bounds every saved counter throughout the executed pass. -/
theorem run_counters_le_three {vertices incidences : ℕ}
    (endpoint : Fin incidences → Fin vertices) (hd : IncidenceRanks.DegreeBound endpoint)
    (limit : ℕ) (hl : limit ≤ incidences) (v : Fin vertices) :
    (IncidenceRanks.run endpoint limit hl).counters.get v ≤ 3 := by
  rw [IncidenceRanks.counters_eq]
  apply le_trans (Finset.card_le_card ?_) (hd v)
  intro j hj
  have h := (IncidenceRanks.mem_prior endpoint limit v j).mp hj
  simpa using h.2

/-- Unvisited ranks remain zero; visited ranks are smaller than three. -/
theorem run_ranks_lt_three {vertices incidences : ℕ}
    (endpoint : Fin incidences → Fin vertices) (hd : IncidenceRanks.DegreeBound endpoint)
    (limit : ℕ) (hl : limit ≤ incidences) (i : Fin incidences) :
    (IncidenceRanks.run endpoint limit hl).ranks.get i < 3 := by
  induction limit with
  | zero => simp [IncidenceRanks.run, IncidenceRanks.initial, Vector.get, Fin.cast]
  | succ limit ih =>
    rw [IncidenceRanks.run, IncidenceRanks.step_ranks]
    split_ifs with he
    · rw [he, IncidenceRanks.counters_eq]
      have hi : limit = i.val := congrArg Fin.val he
      rw [hi]
      exact IncidenceRanks.priorCount_lt_three endpoint hd i
    · exact ih (by omega)

/-- The counter selected for the next increment is at most two. -/
theorem run_current_counter_lt_three {vertices incidences : ℕ}
    (endpoint : Fin incidences → Fin vertices) (hd : IncidenceRanks.DegreeBound endpoint)
    (limit : ℕ) (hl : limit < incidences) :
    (IncidenceRanks.run endpoint limit hl.le).counters.get (endpoint ⟨limit, hl⟩) < 3 := by
  rw [IncidenceRanks.counters_eq]
  exact IncidenceRanks.priorCount_lt_three endpoint hd ⟨limit, hl⟩

end Maxwell.Cost.IncidenceEncoding
