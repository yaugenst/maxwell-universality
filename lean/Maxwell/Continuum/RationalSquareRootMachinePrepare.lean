import Maxwell.Continuum.RationalSquareRootMachineValues

/-! Runtime precision scaling for the literal rational square root. -/

namespace Maxwell.Continuum.Calibration.RationalRoot

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def prepareCode : Code := .seq (NatAssign.code powerPlan)
  (.seq Parameters.PowerMachine.code (NatAssign.code radicandPlan))
def prepareCost (N W : ℕ) : ℕ := 3000*8^3*(W+6)^2+
  (Parameters.PowerMachine.costBound N (W+4)+3000*8^10*(3*N+W+6)^2)

theorem input_width (A D N W : ℕ) (hA : A.bits.length≤W) (hD : D.bits.length≤W)
    (hN : N.bits.length≤W) (i : ℕ) : (inputValues A D N i).bits.length≤W := by
  have hzero : (0:ℕ).bits.length=0 := rfl
  simp only [inputValues]
  split_ifs <;> omega

theorem power_width (A D N W : ℕ) (hA : A.bits.length≤W) (hD : D.bits.length≤W)
    (hN : N.bits.length≤W) (i : ℕ) : (powerValues A D N i).bits.length≤3*N+W+4 := by
  have hp4 := SelectedParameters.Geometric.power_bits 4 N
  have hp2 := SelectedParameters.Geometric.power_bits 2 N
  change (4^N).bits.length≤N*3+1 at hp4
  change (2^N).bits.length≤N*2+1 at hp2
  have hinput := input_width A D N W hA hD hN i
  have fourBits : (4:ℕ).bits.length=3 := rfl
  have twoBits : (2:ℕ).bits.length=2 := rfl
  simp only [powerValues]
  split_ifs <;> omega

theorem prepare_executes (A D N W : ℕ) (hA : A.bits.length≤W) (hD : D.bits.length≤W)
    (hN : N.bits.length≤W) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids (inputValues A D N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape prepareCode cost s t ∧ cost≤prepareCost N W ∧
      NatAssign.Bank ids (preparedValues A D N) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := NatAssign.executes ids ids_ge powerPlan powerPlan_valid
    (inputValues A D N) input tape s hs hz
  have fourBits : (4:ℕ).bits.length=3 := rfl
  have twoBits : (2:ℕ).bits.length=2 := rfl
  have price0 := NatAssign.price_bound ids powerPlan powerPlan_valid (inputValues A D N)
    (W+4) (fun i _ => (input_width A D N W hA hD hN i).trans (by omega))
    (by simp [powerPlan,NatAssign.Instruction.literalWidth,fourBits,twoBits])
  have cost0 : c0≤3000*8^3*(W+6)^2 := by
    simpa only [powerPlan,List.length_cons,List.length_nil,Nat.add_assoc] using hc0.trans price0
  have widths : ∀ i∈SelectedParameters.DynamicPower.ids,
      (NatAssign.values powerPlan (inputValues A D N) i).bits.length≤W+4 := by
    intro i _
    rw [powerPlan_values]
    have hi := input_width A D N W hA hD hN i
    split_ifs <;> omega
  have count : Word u.val 534 N := by
    simpa [powerPlan_values] using b0 534 (by decide)
  obtain ⟨c1,v,e1,hc1,b1,blank1,f1⟩ := Parameters.PowerMachine.executes
    (NatAssign.values powerPlan (inputValues A D N)) N (W+4) (by omega) widths
      (hN.trans (by omega)) input tape u
      (fun i hi => b0 i ((by decide : SelectedParameters.DynamicPower.ids⊆ids) hi)) z0 count
  have fullBank : NatAssign.Bank ids (powerValues A D N) v.val := by
    intro i hi
    by_cases core : i∈({530,531,532,533,534}:Finset ℕ)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at core
      rcases core with rfl|rfl|rfl|rfl|rfl
      · simpa [powerValues,SelectedParameters.DynamicPower.values,powerPlan_values] using b1.bank 530 (by decide)
      · simpa [powerValues,SelectedParameters.DynamicPower.values,powerPlan_values] using b1.bank 531 (by decide)
      · simpa [powerValues,SelectedParameters.DynamicPower.values,powerPlan_values] using b1.bank 532 (by decide)
      · simpa [powerValues,SelectedParameters.DynamicPower.values,powerPlan_values] using b1.bank 533 (by decide)
      · simpa [powerValues,inputValues] using (RationalAccumulator.zero_word_iff_blank _ _).mpr blank1
    · have outside : i∉SelectedParameters.DynamicPower.workspace := by
        have hlo := ids_ge i hi
        simp only [SelectedParameters.DynamicPower.workspace,Finset.mem_insert,
          Finset.mem_singleton]
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at core
        omega
      have hb := RationalAccumulator.word_of_eq (f1.tapes i outside) (b0 i hi)
      rw [powerPlan_values] at hb
      have h530 : i≠530 := by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at core; omega
      have h531 : i≠531 := by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at core; omega
      have h532 : i≠532 := by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at core; omega
      have h533 : i≠533 := by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at core; omega
      have h534 : i≠534 := by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at core; omega
      simpa only [powerValues,ite_eq_right h530,ite_eq_right h531,ite_eq_right h532,
        ite_eq_right h533,ite_eq_right h534] using hb
  obtain ⟨c2,t,e2,hc2,b2,z2,f2⟩ := NatAssign.executes ids ids_ge radicandPlan radicandPlan_valid
    (powerValues A D N) input tape v fullBank b1.scratch
  have price2 := NatAssign.price_bound ids radicandPlan radicandPlan_valid (powerValues A D N)
    (3*N+W+4) (fun i _ => power_width A D N W hA hD hN i)
      (by simp [radicandPlan,NatAssign.Instruction.literalWidth])
  have cost2 : c2≤3000*8^10*(3*N+W+6)^2 := by
    simpa only [radicandPlan,List.length_cons,List.length_nil,Nat.add_assoc] using hc2.trans price2
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,?_,z2,
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))⟩
  · unfold prepareCost
    omega
  · simpa only [radicandPlan_values] using b2

theorem prepared_root_bank (A D N : ℕ) {s : BitRAMState}
    (h : NatAssign.Bank ids (preparedValues A D N) s) :
    NatAssign.Bank NaturalRoot.fullIds (NaturalRoot.inputValues (radicand A D N)) s := by
  intro i hi
  have hlo := hi
  simp only [NaturalRoot.fullIds,NaturalRoot.ids,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.mem_Icc] at hlo
  have hb := h i (Finset.mem_union_left _ hi)
  simpa [preparedValues,inputValues,NaturalRoot.inputValues,
    show i≠542 by omega,show i≠543 by omega,show i≠544 by omega,show i≠548 by omega] using hb

#print axioms prepare_executes

end Maxwell.Continuum.Calibration.RationalRoot
