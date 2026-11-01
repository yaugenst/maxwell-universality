import Maxwell.Logical.Routing.SortArrays

/-! The three sorting-key arrays can be filled by a single pass over source
ports. All addresses and values are direct coordinates of the source,
target, and already-computed color; no inverse permutation is evaluated. -/

namespace Maxwell.Logical.Routing.PhaseKeys
open SortArrays SortSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def first {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) : Keys q :=
  targetArray (PhaseArrays.prepare colors).first
def middle {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) : Keys q :=
  targetArray (transposedTarget (PhaseArrays.prepare colors).column)
def last {q : ℕ} {target : Equiv.Perm (Port q)} (colors : RowColoring target) : Keys q :=
  targetArray (PhaseArrays.prepare colors).finalRow

def middleAddress {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) : Fin (q*q) :=
  finProdFinEquiv (p.2,colors.color p)
def lastAddress {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) : Fin (q*q) :=
  finProdFinEquiv (colors.color p,(target p).2)

theorem middleAddress_injective {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : Function.Injective (middleAddress colors) := by
  intro a b h
  have hh:=Prod.mk.inj (finProdFinEquiv.injective h)
  exact colors.source_unique a b hh.1 hh.2

theorem lastAddress_injective {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) : Function.Injective (lastAddress colors) := by
  intro a b h
  have hh:=Prod.mk.inj (finProdFinEquiv.injective h)
  exact colors.target_unique a b hh.2 hh.1

theorem targetArray_at {q : ℕ} (target : Equiv.Perm (Port q)) (p : Port q) :
    (targetArray target).get (finProdFinEquiv p)=(target p).1.val := by
  simp only [targetArray,get_ofFn,Equiv.symm_apply_apply]

theorem first_at {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) :
    (first colors).get (finProdFinEquiv p)=(colors.color p).val := by
  rw [first,targetArray_at,PhaseArrays.prepare_first]
  rfl

theorem middle_at {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) :
    (middle colors).get (middleAddress colors p)=(target p).2.val := by
  rw [middle,middleAddress,targetArray_at,PhaseArrays.prepare_column]
  change (columnPhase colors (firstPermutation colors p)).2.val=(target p).2.val
  simp only [columnPhase,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

theorem last_at {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) :
    (last colors).get (lastAddress colors p)=(target p).1.val := by
  rw [last,lastAddress,targetArray_at,PhaseArrays.prepare_finalRow]
  change (finalRowPhase colors (secondPermutation colors p)).1.val=(target p).1.val
  simp only [finalRowPhase,Equiv.trans_apply,Equiv.symm_apply_apply]

theorem middleAddress_value {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) :
    (middleAddress colors p).val=q*p.2.val+(colors.color p).val := by
  exact Nat.add_comm _ _

theorem lastAddress_value {q : ℕ} {target : Equiv.Perm (Port q)}
    (colors : RowColoring target) (p : Port q) :
    (lastAddress colors p).val=q*(colors.color p).val+(target p).2.val := by
  exact Nat.add_comm _ _

#print axioms middle_at
#print axioms last_at
end Maxwell.Logical.Routing.PhaseKeys
