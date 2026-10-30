import Maxwell.Continuum.SourceRoutingPhaseData
import Maxwell.Continuum.SourceRoutingGeometryAccess

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
open Structured Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

structure Plan (q : ℕ) where
  base : Fin 5→ℕ
  clock : List Bool
  positive : 0<q
  clock_length : clock.length=(q*q).bits.length
  separated : GeometryArrays.Separated base (q*q) (q*q).bits.length

def Plan.width {q : ℕ} (_p : Plan q) : ℕ := (q*q).bits.length
def Plan.bound {q : ℕ} (p : Plan q) : ℕ :=
  p.width+(p.base 0).bits.length+(p.base 1).bits.length+(p.base 2).bits.length+
    (p.base 3).bits.length+(p.base 4).bits.length+16

theorem Plan.count_positive {q : ℕ} (p : Plan q) : 0<q*q := Nat.mul_pos p.positive p.positive
theorem Plan.width_positive {q : ℕ} (p : Plan q) : 0<p.width :=
  RationalAccumulator.bits_nonempty p.count_positive
theorem Plan.width_bound {q : ℕ} (p : Plan q) : p.width ≤ p.bound := by dsimp only [Plan.bound];omega
theorem Plan.base_bound {q : ℕ} (p : Plan q) (slot : Fin 5) : (p.base slot).bits.length ≤ p.bound := by
  have cases : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 ∨ slot=4 := by
    fin_cases slot <;> simp
  rcases cases with rfl|rfl|rfl|rfl|rfl <;> dsimp only [Plan.bound] <;> omega
theorem Plan.index_fit {q : ℕ} (p : Plan q) (index : Fin (q*q)) : index.val.bits.length ≤ p.width :=
  Maxwell.Continuum.RationalWords.bits_mono index.isLt.le
theorem Plan.coordinate_fit {q : ℕ} (p : Plan q) (index : Fin q) : index.val.bits.length ≤ p.width := by
  apply Maxwell.Continuum.RationalWords.bits_mono
  exact index.isLt.le.trans (Nat.le_mul_of_pos_right _ p.positive)

structure Metadata {q : ℕ} (p : Plan q) (s : BitRAMState) : Prop where
  width : Word s 711 p.width
  forward : Word s 716 (p.base 0)
  clock : BankArray.Word s 718 p.clock

theorem Metadata.frame {q : ℕ} {p : Plan q} {s t : BitRAMState} {changed : Finset ℕ}
    (metadata : Metadata p s) (frame : ArchiveFrame changed s t)
    (keep : Disjoint ({711,716,718} : Finset ℕ) changed) : Metadata p t := by
  have kept (i : ℕ) (hi : i∈({711,716,718} : Finset ℕ)) : t.tapes i=s.tapes i :=
    frame.tapes i (Or.inr (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega))
      (Finset.disjoint_left.mp keep hi)
  exact ⟨RationalAccumulator.word_of_eq (kept 711 (by decide)) metadata.width,
    RationalAccumulator.word_of_eq (kept 716 (by decide)) metadata.forward,
    BankArray.word_of_eq (kept 718 (by decide)) metadata.clock⟩

def seed {q : ℕ} (p : Plan q) (k i : ℕ) : ℕ :=
  if i=1200 then q else if i=1201 then k else if i=1215 then p.base 1 else
    if i=1216 then p.base 2 else if i=1217 then p.base 3 else if i=1218 then p.base 4 else
      if i=1219 then 1 else 0

theorem seed_width {q : ℕ} (p : Plan q) (k : ℕ) (hk : k ≤ q*q) :
    ∀i∈GeometryArithmetic.ids,(seed p k i).bits.length ≤ p.bound := by
  have qfit : q.bits.length ≤ p.width :=
    Maxwell.Continuum.RationalWords.bits_mono (Nat.le_mul_of_pos_right _ p.positive)
  have kfit : k.bits.length ≤ p.width := Maxwell.Continuum.RationalWords.bits_mono hk
  have b1:=p.base_bound 1
  have b2:=p.base_bound 2
  have b3:=p.base_bound 3
  have b4:=p.base_bound 4
  have width:=p.width_bound
  intro i _
  simp only [seed]
  split_ifs
  · exact qfit.trans width
  · exact kfit.trans width
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · change 1 ≤ p.bound
    dsimp only [Plan.bound]
    omega
  · exact Nat.zero_le _

theorem seed_zero {q : ℕ} (p : Plan q) (k : ℕ) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,seed p k i=0 := by
  intro i hi
  simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
    Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl <;> rfl

#print axioms seed_width
end Maxwell.Cost.RoutingPorts.Complete.GeometryPhase
