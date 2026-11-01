import Maxwell.Continuum.ParameterOuterPhysicalData
import Maxwell.Continuum.ParameterOuterStageSearches

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
open RationalAccumulator (Blank)

def retained : Finset ℕ := Finset.Icc 2200 2226

structure Core (D : Data) (k : ℕ) (v : ℕ→ℕ) : Prop where
  data : dataOf v=D
  exponent : v 2206=k
  binary : v 2220=2^k
  length : v 2221=stageLength k
  one : v 2222=1
  two : v 2223=2
  eight : v 2224=8
  four : v 2225=4
  slow : v 2226=slowDivisor

def Ready (D : Data) (k W : ℕ) (s : Store) : Prop :=
  ∃v,NatAssign.Bank ids v s.val ∧ (∀i,i<5→Blank s.val i) ∧
    (∀i∈ids,(v i).bits.length ≤ W) ∧ Core D k v

theorem dataOf_congr (v w : ℕ→ℕ) (h : ∀i∈retained,w i=v i) : dataOf w=dataOf v := by
  have span : (fun j:Fin 3=>w (2217+j.val))=(fun j:Fin 3=>v (2217+j.val)) := by
    funext j
    exact h _ (by simp only [retained,Finset.mem_Icc];have := j.isLt;omega)
  simp only [dataOf,h 2210 (by decide +kernel),h 2211 (by decide +kernel),h 2212 (by decide +kernel),
    h 2213 (by decide +kernel),h 2214 (by decide +kernel),h 2215 (by decide +kernel),
    h 2216 (by decide +kernel),span]

theorem Core.congr {D : Data} {k : ℕ} {v w : ℕ→ℕ} (h : Core D k v)
    (he : ∀i∈retained,w i=v i) : Core D k w := by
  refine ⟨(dataOf_congr v w he).trans h.data,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact (he _ (by decide +kernel)).trans h.exponent
    | exact (he _ (by decide +kernel)).trans h.binary
    | exact (he _ (by decide +kernel)).trans h.length
    | exact (he _ (by decide +kernel)).trans h.one
    | exact (he _ (by decide +kernel)).trans h.two
    | exact (he _ (by decide +kernel)).trans h.eight
    | exact (he _ (by decide +kernel)).trans h.four
    | exact (he _ (by decide +kernel)).trans h.slow

theorem Core.spacing_data {D : Data} {k : ℕ} {v : ℕ→ℕ} (h : Core D k v) :
    SpacingMachine.dataOf (NatAssign.values loadSpacing v)=D.spacing k := by
  rw [loadSpacing_fields,h.length,← h.data]
  rfl

theorem retained_disjoint_spacing : Disjoint retained SpacingMachine.ids := by decide +kernel
theorem retained_disjoint_buffer : Disjoint retained BufferMachine.ids := by decide +kernel
theorem retained_disjoint_tau : Disjoint retained OuterTau.ids := by decide +kernel

#print axioms Core.congr
end Maxwell.Continuum.Parameters.OuterMachine
