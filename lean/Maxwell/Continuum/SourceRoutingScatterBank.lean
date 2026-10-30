import Maxwell.Continuum.SourceRoutingRead
import Maxwell.Continuum.NatAssignCleanup

/-! A repeated incidence step starts with exactly four canonical natural
inputs. The actual cleanup returns all other arithmetic tapes to zero. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Scatter
open Structured Maxwell.Continuum.RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def seed (half incidence endpoint rank i : ℕ) : ℕ :=
  if i=710 then half else if i=733 then incidence else if i=734 then endpoint else if i=735 then rank else 0
def clearPorts : List ℕ := [220,221,222,223,730,731,734,735,736,737,760,761,762,763,764,765,766,767,768]
def cleanup : List NatAssign.Instruction := NatAssign.clearList clearPorts

theorem seed_zero (half incidence endpoint rank : ℕ) :
    ∀i∈NaturalQuotient.workPorts,seed half incidence endpoint rank i=0 := by
  intro i hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl <;> rfl

theorem seed_width (half incidence endpoint rank B : ℕ)
    (hh : half.bits.length≤B) (hi : incidence.bits.length≤B)
    (he : endpoint.bits.length≤B) (hr : rank.bits.length≤B) :
    ∀i∈PortArithmetic.ids,(seed half incidence endpoint rank i).bits.length≤B := by
  intro i _
  simp only [seed]
  split_ifs <;> first | assumption | exact Nat.zero_le _

theorem cleanup_valid : ∀a∈cleanup,a.Valid PortArithmetic.ids := by
  exact NatAssign.clearList_valid _ _ (by decide)

theorem cleanup_values (half incidence endpoint rank i : ℕ) (hi : i∈PortArithmetic.ids) :
    NatAssign.values cleanup (PortArithmetic.output (seed half incidence endpoint rank)) i=
      seed half incidence 0 0 i := by
  rw [cleanup,NatAssign.clearList_values]
  by_cases h710 : i=710
  · subst i
    simp [clearPorts,PortArithmetic.output,PortArithmetic.finish,PortArithmetic.v4,PortArithmetic.v3,
      PortArithmetic.v2,PortArithmetic.v1,PortArithmetic.divided,PortArithmetic.prepared,PortArithmetic.prepare,
      NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,seed]
  · by_cases h733 : i=733
    · subst i
      simp [clearPorts,PortArithmetic.output,PortArithmetic.finish,PortArithmetic.v4,PortArithmetic.v3,
        PortArithmetic.v2,PortArithmetic.v1,PortArithmetic.divided,PortArithmetic.prepared,PortArithmetic.prepare,
        NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,seed]
    · have hc : i∈clearPorts := by
        simp only [PortArithmetic.ids,PortArithmetic.ports,NaturalQuotient.workPorts,
          Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
        simp only [clearPorts,List.mem_cons,List.not_mem_nil,or_false]
        omega
      simp [hc,seed,h710,h733]

theorem read_bank {n : ℕ} (half : ℕ) (endpoint rank : Vector ℕ n) (i : Fin n)
    {s t : BitRAMState} (hs : NatAssign.Bank PortArithmetic.ids (seed half i.val 0 0) s)
    (he : Word t 734 (endpoint.get i)) (hr : Word t 735 (rank.get i))
    (hf : ArchiveFrame {734,735} s t) :
    NatAssign.Bank PortArithmetic.ids (seed half i.val (endpoint.get i) (rank.get i)) t := by
  intro k hk
  by_cases h734 : k=734
  · subst k
    exact he
  · by_cases h735 : k=735
    · subst k
      exact hr
    · have hh := RationalAccumulator.word_of_eq
        (hf.tapes k (Or.inr (PortArithmetic.ids_lower k hk)) (by simp; omega)) (hs k hk)
      simpa only [seed,h734,h735,ite_false] using hh

theorem ready_after_stage {s t : BitRAMState} (hs : Ready s)
    (hz : NatAssign.Scratch t) (hf : BinaryPrecision.Frame ({0,1,2,3}∪PortArithmetic.ids) s t) : Ready t := by
  have keep (i : ℕ) (hi : i∈({5,6,7,8,9,37,752}:Finset ℕ)) : t.tapes i=s.tapes i := by
    apply hf.tapes
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  rcases hs.scratch with ⟨_,_,_,_,h5,h6,h8,h9⟩
  exact ⟨⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
    RationalAccumulator.blank_of_eq (keep 5 (by decide)) h5,
    RationalAccumulator.blank_of_eq (keep 6 (by decide)) h6,
    RationalAccumulator.blank_of_eq (keep 8 (by decide)) h8,
    RationalAccumulator.blank_of_eq (keep 9 (by decide)) h9⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by decide)) hs.seven,
    RationalAccumulator.blank_of_eq (keep 37 (by decide)) hs.pack,
    RationalAccumulator.blank_of_eq (keep 752 (by decide)) hs.probe⟩

theorem cleanup_executes (half incidence endpoint rank B : ℕ) (hB : 2≤B)
    (hw : ∀i∈PortArithmetic.ids,(seed half incidence endpoint rank i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank PortArithmetic.ids (PortArithmetic.output (seed half incidence endpoint rank)) s.val)
    (hz : Ready s.val) :
    ∃steps t, Executes input tape (NatAssign.code cleanup) steps s t ∧ steps≤2^134*(B+2)^2 ∧
      NatAssign.Bank PortArithmetic.ids (seed half incidence 0 0) t.val ∧ Ready t.val ∧
      BinaryPrecision.Frame ({0,1,2,3}∪PortArithmetic.ids) s.val t.val := by
  obtain ⟨steps,t,he,hc,ht,zt,hf⟩ := fixedBankStage_executes PortArithmetic.ids
    (fun i hi => by have := PortArithmetic.ids_lower i hi; omega) cleanup cleanup_valid
    (by decide) (PortArithmetic.output (seed half incidence endpoint rank)) (2^17*(B+2))
    (PortArithmetic.output_width _ B hB hw)
    (by intro a ha; exact (NatAssign.clearList_literalWidth clearPorts a ha).le.trans (Nat.zero_le _))
    input tape s hs (Startup.ready_scratch hz)
  refine ⟨steps,t,he,?_,?_,ready_after_stage hz zt hf,hf⟩
  · unfold stageCost at hc
    have hb : (2^17*(B+2)+2)^2≤2^38*(B+2)^2 := by
      calc
        _ ≤ (2^19*(B+2))^2 := Nat.pow_le_pow_left (by omega) 2
        _ = _ := by ring
    nlinarith only [hc,hb]
  · intro i hi
    have hh := ht i hi
    rw [cleanup_values half incidence endpoint rank i hi] at hh
    exact hh

#print axioms cleanup_executes

end Maxwell.Cost.RoutingPorts.Complete.Scatter
