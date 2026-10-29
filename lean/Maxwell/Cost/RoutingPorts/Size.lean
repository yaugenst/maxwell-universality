import Maxwell.Cost.SelectedParameters.Geometric
import Maxwell.Cost.Structured.Rename

/-! The routing grid exponent is computed by the existing finite exact
geometric search, using the runtime vertex count as its denominator. -/
namespace Maxwell.Cost.RoutingPorts.Size
open Structured RationalAccumulator

theorem exponent_eq (vertices : ℕ) (hv : 0 < vertices) :
    SelectedParameters.Geometric.exponent 1 4 1 vertices (by decide) (by decide) (by decide) hv = Nat.clog 4 vertices := by
  have criterion (n : ℕ) : (1/4:ℚ)^n ≤ 1/(vertices:ℚ) ↔ vertices ≤ 4^n := by
    rw [div_pow,one_pow]
    have hp : (0:ℚ) < 4^n := by positivity
    have hvq : (0:ℚ) < vertices := by exact_mod_cast hv
    rw [div_le_div_iff₀ hp hvq]
    simp only [one_mul]
    exact_mod_cast (Iff.rfl : vertices ≤ 4^n ↔ vertices ≤ 4^n)
  apply Nat.le_antisymm
  · apply Nat.find_min'
    exact (criterion _).mpr (Nat.le_pow_clog (by decide) vertices)
  · apply Nat.clog_le_of_le_pow
    exact (criterion _).mp (Realization.geometricSteps_spec (1/4) (1/(vertices:ℚ))
      (by norm_num) (by norm_num) (by positivity))

def ids : Finset ℕ := SelectedParameters.Geometric.ids ∪ {141}
def initial (vertices i : ℕ) : ℕ := if i=141 then vertices else 0

def prepare : List NatAssign.Instruction :=
  [.literal 520 1,.literal 521 4,.literal 522 1,.copy 141 523]
def rawCode : Code := .seq (NatAssign.code prepare) SelectedParameters.Geometric.code

def prepared (vertices i : ℕ) : ℕ :=
  if i=141 then vertices else if i=520 then 1 else if i=521 then 4 else
  if i=522 then 1 else if i=523 then vertices else 0

theorem prepare_values (vertices : ℕ) :
    NatAssign.values prepare (initial vertices) = prepared vertices := by
  funext i
  simp [prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,initial,prepared,Function.update_apply]
  split_ifs <;> omega

theorem ids_ge (i : ℕ) (hi : i ∈ ids) : 4 ≤ i := by
  simp only [ids,SelectedParameters.Geometric.ids,SelectedParameters.Geometric.extra,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem prepare_valid : ∀ a ∈ prepare, a.Valid ids := by
  simp [prepare,NatAssign.Instruction.Valid,ids,SelectedParameters.Geometric.ids,SelectedParameters.Geometric.extra]

def rawPrice (vertices : ℕ) : ℕ :=
  3000*8^4*(vertices.bits.length+5)^2 + SelectedParameters.Geometric.initialCost (vertices.bits.length+3) +
    SelectedParameters.Geometric.searchCost (Nat.clog 4 vertices) 3 (vertices.bits.length+3)

theorem raw_executes (vertices : ℕ) (hv : 0 < vertices)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank ids (initial vertices) s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape rawCode cost s t ∧ cost ≤ rawPrice vertices ∧
      SelectedParameters.Geometric.Ready 1 4 1 vertices (Nat.clog 4 vertices) t ∧
      BinaryPrecision.Frame (SelectedParameters.Geometric.workspace ∪ {520,521,522,523}) s.val t.val := by
  have h4 : (4:ℕ).bits.length = 3 := rfl
  obtain ⟨ac,a,ea,hac,ba,sa,fa⟩ := NatAssign.executes ids ids_ge prepare prepare_valid
    (initial vertices) input tape s hb hs
  have hwidth (i : ℕ) (_hi : i ∈ ids) : (initial vertices i).bits.length ≤ vertices.bits.length+3 := by
    simp only [initial]; split_ifs <;> simp
  have hp := NatAssign.price_bound ids prepare prepare_valid (initial vertices)
    (vertices.bits.length+3) hwidth (by
      intro inst hi
      simp only [prepare,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> norm_num [NatAssign.Instruction.literalWidth,h4])
  have gb : NatAssign.Bank SelectedParameters.Geometric.ids (prepared vertices) a.val := by
    rw [prepare_values] at ba
    intro i hi; exact ba i (Finset.mem_union_left _ hi)
  have gw (i : ℕ) (_hi : i ∈ SelectedParameters.Geometric.ids) : (prepared vertices i).bits.length ≤ vertices.bits.length+3 := by
    simp only [prepared]; split_ifs <;> simp [h4]
  obtain ⟨bc,t,eb,hbc,bt,fb⟩ := SelectedParameters.Geometric.executes (prepared vertices) 3 (vertices.bits.length+3)
    (by omega) (by simp [prepared]) (by simp [prepared]) (by simp [prepared])
    (by simpa [prepared] using hv) gw (by simp [prepared]) (by simp [prepared,h4])
    input tape a gb sa
  change SelectedParameters.Geometric.Ready 1 4 1 vertices
    (SelectedParameters.Geometric.exponent 1 4 1 vertices (by decide) (by decide) (by decide) hv) t at bt
  change bc ≤ SelectedParameters.Geometric.initialCost (vertices.bits.length+3) +
    SelectedParameters.Geometric.searchCost
      (SelectedParameters.Geometric.exponent 1 4 1 vertices (by decide) (by decide) (by decide) hv)
      3 (vertices.bits.length+3) at hbc
  rw [exponent_eq vertices hv] at bt hbc
  refine ⟨ac+bc,t,ea.seq eb,?_,bt,
    (fa.mono (by decide)).trans (fb.mono (Finset.subset_union_left))⟩
  have hp' : ac ≤ 3000*8^4*(vertices.bits.length+5)^2 := by
    exact hac.trans hp
  dsimp [rawPrice]
  omega

end Maxwell.Cost.RoutingPorts.Size
