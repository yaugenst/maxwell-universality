import Maxwell.Continuum.RationalDataflowArrayOutputFrame

/-! A prefix view keeps the actual memory words and runtime descriptors.
No copying, allocation, or assumption about unused cells is introduced. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000

def Table.prefix {n : ℕ} (a : Table n) (m : ℕ) (hm : m≤n) : Table m where
  width := a.width
  basePositive := a.basePositive
  baseNegative := a.baseNegative
  baseDenominator := a.baseDenominator
  clock := a.clock
  positive := Vector.ofFn (fun i => a.positive.get ⟨i.val,lt_of_lt_of_le i.isLt hm⟩)
  negative := Vector.ofFn (fun i => a.negative.get ⟨i.val,lt_of_lt_of_le i.isLt hm⟩)
  denominator := Vector.ofFn (fun i => a.denominator.get ⟨i.val,lt_of_lt_of_le i.isLt hm⟩)
  width_pos := a.width_pos
  clock_length := a.clock_length

theorem prefix_represents {n m : ℕ} {memory : ℕ→Bool} {base width : ℕ}
    {v : Vector (List Bool) n} (h : BitArray.Represents memory base width v) (hm : m≤n) :
    BitArray.Represents memory base width
      (Vector.ofFn (fun i:Fin m => v.get ⟨i.val,lt_of_lt_of_le i.isLt hm⟩)) := by
  refine ⟨?_,?_⟩
  · intro i
    simpa [Vector.get,Fin.cast] using h.length ⟨i.val,lt_of_lt_of_le i.isLt hm⟩
  · intro i j hj
    simpa [Vector.get,Fin.cast] using h.bits ⟨i.val,lt_of_lt_of_le i.isLt hm⟩ j hj

theorem Table.Ready.prefix {n m : ℕ} {a : Table n} {s : Store}
    (h : a.Ready s) (hm : m≤n) : (a.prefix m hm).Ready s :=
  ⟨h.scratch,h.seven,h.width,h.basePositive,h.baseNegative,h.baseDenominator,h.clock,
    prefix_represents h.positive hm,prefix_represents h.negative hm,prefix_represents h.denominator hm⟩

theorem Table.OutputReady.prefix {n m : ℕ} {a : Table n} {s : Store}
    (h : a.OutputReady s) (hm : m≤n) : (a.prefix m hm).OutputReady s :=
  ⟨h.scratch,h.seven,h.packing,h.width,h.basePositive,h.baseNegative,h.baseDenominator,h.clock,
    prefix_represents h.positive hm,prefix_represents h.negative hm,prefix_represents h.denominator hm⟩

theorem Table.MetadataWidth.prefix {n m B : ℕ} {a : Table n}
    (h : a.MetadataWidth B) (hm : m≤n) : (a.prefix m hm).MetadataWidth B :=
  ⟨h.width,h.basePositive,h.baseNegative,h.baseDenominator,h.clock⟩

theorem separated_shrink {a b n m n' m' : ℕ} (h : IncidenceEncoding.Separated a n b m)
    (hn : n'≤n) (hm : m'≤m) : IncidenceEncoding.Separated a n' b m' := by
  unfold IncidenceEncoding.Separated at h ⊢
  omega

theorem Table.Separated.prefix {n m : ℕ} {a : Table n}
    (h : a.Separated) (hm : m≤n) : (a.prefix m hm).Separated := by
  have hmul := Nat.mul_le_mul_right (addressValue a.width) hm
  exact ⟨separated_shrink h.1 hmul hmul,separated_shrink h.2.1 hmul hmul,
    separated_shrink h.2.2 hmul hmul⟩

theorem Table.SeparatedFrom.prefix_right {n m k : ℕ} {a : Table n} {b : Table m}
    (h : a.SeparatedFrom b) (hk : k≤m) : a.SeparatedFrom (b.prefix k hk) := by
  intro x hx y hy
  exact separated_shrink (h x hx y hy) le_rfl (Nat.mul_le_mul_right _ hk)

#print axioms Table.OutputReady.prefix
#print axioms Table.SeparatedFrom.prefix_right
end Maxwell.Continuum.RationalDataflow.PartArray
