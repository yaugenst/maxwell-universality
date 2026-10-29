import Maxwell.Cost.SelectedParameters.Geometric
import Maxwell.Cost.SelectedParameters.RationalBasic

namespace Maxwell.Cost.SelectedParameters.GeometricAdapter
open Structured
set_option maxHeartbeats 1500000

def ids (extra : Finset ℕ) : Finset ℕ := Rational.ids extra ∪ Geometric.extra

def extend (v : ℕ → ℕ) (i : ℕ) : ℕ := if i ∈ Geometric.extra then 0 else v i

def loadInputs (a b c d : ℕ) : List NatAssign.Instruction :=
  [.literal 520 a,.literal 521 b,.copy c 522,.copy d 523]

def loaded (a b c d : ℕ) (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (extend v) 520 a)
    521 b) 522 (v c)) 523 (v d)

def searched (v : ℕ → ℕ) (a b c d N i : ℕ) : ℕ :=
  if i ∈ Geometric.ids then Geometric.values a b c d N i else v i

def clearGeo : List NatAssign.Instruction :=
  [.literal 520 0,.literal 521 0,.literal 522 0,.literal 523 0,
   .literal 524 0,.literal 525 0,.literal 526 0,.literal 527 0]

def finish (num den : ℕ) : List NatAssign.Instruction :=
  [.copy 526 num,.literal den 1] ++ clearGeo ++ Rational.clear

def code (a b c d num den : ℕ) : Code :=
  .seq (NatAssign.code (loadInputs a b c d)) (.seq Geometric.code (NatAssign.code (finish num den)))

def workspace (num den : ℕ) : Finset ℕ := Rational.workspace num den ∪ Geometric.extra

def inputWidth (A B : ℕ) : ℕ := A+B+1

theorem loaded_values (a b c d : ℕ) (hc : 540 ≤ c) (hd : 540 ≤ d) (v : ℕ → ℕ) :
    NatAssign.values (loadInputs a b c d) (extend v) = loaded a b c d v := by
  have hcGeo : c ∉ Geometric.extra := by simp only [Geometric.extra,Finset.mem_insert,Finset.mem_singleton];omega
  have hdGeo : d ∉ Geometric.extra := by simp only [Geometric.extra,Finset.mem_insert,Finset.mem_singleton];omega
  simp [loadInputs,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,loaded,extend,hcGeo,hdGeo,
    show c≠520 by omega,show c≠521 by omega,
    show d≠520 by omega,show d≠521 by omega,show d≠522 by omega]

theorem ids_ge (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i) (i : ℕ) (hi : i ∈ ids extra) : 4 ≤ i := by
  simp only [ids,Rational.ids,Rational.common,Geometric.extra,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with (hi | hi) | hi
  · exact (by omega : 4 ≤ 540).trans (hextra i hi)
  · omega
  · omega

theorem caller_not_geo (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i) (i : ℕ)
    (hi : i ∈ Rational.ids extra) : i ∉ Geometric.extra := by
  simp only [Rational.ids,Rational.common,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  simp only [Geometric.extra,Finset.mem_insert,Finset.mem_singleton]
  rcases hi with hi | hi
  · have hh := hextra i hi
    omega
  · omega

theorem geo_subset (extra : Finset ℕ) : Geometric.ids ⊆ ids extra := by
  intro i hi
  simp only [Geometric.ids,ids,Rational.ids,Rational.common,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
  tauto

theorem loaded_width (extra : Finset ℕ) (a b c d A B : ℕ) (v : ℕ → ℕ)
    (hc : c ∈ extra) (hd : d ∈ extra) (haW : a.bits.length ≤ A) (hbW : b.bits.length ≤ A)
    (hv : ∀ i ∈ Rational.ids extra, (v i).bits.length ≤ B) :
    ∀ i ∈ ids extra, (loaded a b c d v i).bits.length ≤ inputWidth A B := by
  intro i hi
  have hA : A ≤ inputWidth A B := by dsimp [inputWidth]; omega
  have hB : B ≤ inputWidth A B := by dsimp [inputWidth]; omega
  simp only [loaded,Function.update_apply,extend]
  split_ifs <;> first
    | exact (hv d (Finset.mem_union_left _ hd)).trans hB
    | exact (hv c (Finset.mem_union_left _ hc)).trans hB
    | exact hbW.trans hA | exact haW.trans hA
    | exact (hv i ((Finset.mem_union.mp hi).resolve_right ‹i ∉ Geometric.extra›)).trans hB
    | simp

private theorem values_append (xs ys : List NatAssign.Instruction) (v : ℕ → ℕ) :
    NatAssign.values (xs++ys) v = NatAssign.values ys (NatAssign.values xs v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => exact ih (x.update v)

private theorem clearGeo_values (v : ℕ → ℕ) (i : ℕ) :
    NatAssign.values clearGeo v i = if i ∈ Geometric.extra then 0 else v i := by
  simp only [clearGeo,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update_apply,Geometric.extra,Finset.mem_insert,Finset.mem_singleton]
  split_ifs <;> simp_all

theorem finish_values (v : ℕ → ℕ) (a b c d N num den : ℕ) :
    NatAssign.values (finish num den) (searched v a b c d N) =
      extend (Rational.after v num den (N,1)) := by
  rw [finish,values_append,values_append]
  ext i
  change Rational.clean (NatAssign.values clearGeo
    (Function.update (Function.update (searched v a b c d N) num (searched v a b c d N 526)) den 1)) i = _
  rw [Rational.clean_apply,clearGeo_values]
  have h526 : searched v a b c d N 526 = N := by simp [searched,Geometric.ids,Geometric.extra,Geometric.values]
  rw [h526]
  by_cases hg : i ∈ Geometric.extra
  · have hc : i ∉ Rational.common := by
      simp only [Geometric.extra,Finset.mem_insert,Finset.mem_singleton] at hg
      simp only [Rational.common,Finset.mem_insert,Finset.mem_singleton]
      omega
    simp [extend,hg,hc]
  · by_cases hc : i ∈ Rational.common
    · simp [extend,hg,hc,Rational.after]
    · have hn : i ∉ Geometric.ids := by
        simpa only [Geometric.ids,Rational.common,Finset.mem_union,not_or] using And.intro hg hc
      simp [extend,hg,hc,Rational.after,Function.update_apply,searched,hn]

end Maxwell.Cost.SelectedParameters.GeometricAdapter
