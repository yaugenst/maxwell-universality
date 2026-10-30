import Maxwell.Continuum.RationalDataflowSharedLayout
import Maxwell.Continuum.RawSharedDenominator

/-! Exact conversion of one raw rational coefficient into shared-denominator integer channels. -/
namespace Maxwell.Continuum.RationalDataflow.SharedConversion
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def scaleStep (entry quotient : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update v entry
    ⟨(v quotient).positive*(v entry).positive,(v quotient).positive*(v entry).negative,1⟩

def scaleStage (entry quotient : ℕ) : List NatAssign.Instruction :=
  [.multiply (positivePort quotient) (positivePort entry),
   .multiply (positivePort quotient) (negativePort entry),.literal (denominatorPort entry) 1]

theorem scaleStage_values (entry quotient : ℕ) (hne : quotient≠entry) (v : ℕ→Parts) :
    NatAssign.values (scaleStage entry quotient) (dataValues v)=dataValues (scaleStep entry quotient v) := by
  rw [scaleStep,←writeParts_dataValues]
  simp [scaleStage,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,writeParts,hne]

theorem scale_executes (S : Finset ℕ) (entry quotient : ℕ) (he : entry∈S) (hq : quotient∈S)
    (hne : quotient≠entry) (v : ℕ→Parts) (B : ℕ) (hB : 1≤B) (hw : ∀ i∈S, (v i).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape (NatAssign.code (scaleStage entry quotient)) cost s t ∧
      cost≤stageCost B ∧ Ready S (scaleStep entry quotient v) t ∧
      BinaryPrecision.Frame (changed S) s.val t.val := by
  have logical (i : ℕ) (hi : i∈ids S) : i∈bankIds S := Finset.mem_union_left _ hi
  have hp := logical _ (cell_mem he (show positivePort entry∈cellPorts entry by simp [cellPorts]))
  have hn := logical _ (cell_mem he (show negativePort entry∈cellPorts entry by simp [cellPorts]))
  have hd := logical _ (cell_mem he (show denominatorPort entry∈cellPorts entry by simp [cellPorts]))
  have hqp := logical _ (cell_mem hq (show positivePort quotient∈cellPorts quotient by simp [cellPorts]))
  have hv : ∀ a∈scaleStage entry quotient, a.Valid (bankIds S) := by
    simp [scaleStage,NatAssign.Instruction.Valid,hp,hn,hd,hqp,hne]
  obtain ⟨cost,t,hex,hcost,hbank,hsc,hframe⟩ := fixedBankStage_executes (bankIds S)
    (fun i hi => (by omega : 4≤10).trans (bankIds_ge S i hi)) (scaleStage entry quotient) hv
    (by simp [scaleStage]) (dataValues v) B (values_width S v B hw)
    (by simp [scaleStage,NatAssign.Instruction.literalWidth,hB]) input tape s hs.1 (fun i hi => hs.2 i (by omega))
  rw [scaleStage_values entry quotient hne] at hbank
  have h4 : RationalAccumulator.Blank t.val 4 := by
    apply RationalAccumulator.blank_of_eq (hframe.tapes 4 _) (hs.2 4 (by decide))
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨by omega,by intro hi; have := bankIds_ge S 4 hi; omega⟩
  refine ⟨cost,t,hex,hcost,⟨hbank,fun i hi => ?_⟩,hframe.mono ?_⟩
  · by_cases hil : i<4
    · exact hsc i hil
    · have : i=4 := by omega
      simpa only [this] using h4
  · intro i hi
    simp only [changed,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    tauto

theorem quotientStep_width (S : Finset ℕ) (denominator entry quotient : ℕ)
    (hd : denominator∈S) (hq : quotient∈S) (v : ℕ→Parts) (B : ℕ)
    (hw : ∀ i∈S, (v i).Width B) :
    ∀ i∈S, (quotientStep denominator entry quotient v i).Width B := by
  have hqwidth : ((v denominator).positive/(v entry).denominator).bits.length≤B := by
    rw [Nat.size_eq_bits_len]
    exact (Nat.size_le_size (Nat.div_le_self _ _)).trans
      (by simpa only [Nat.size_eq_bits_len] using (hw denominator hd).1)
  intro i hi
  by_cases heq : i=quotient
  · subst i
    simpa only [quotientStep,Function.update_self,Parts.Width] using
      And.intro hqwidth (And.intro (hw quotient hq).2.1 (hw quotient hq).2.2)
  · simpa only [quotientStep,Function.update_of_ne heq] using hw i hi

def convertStep (denominator entry quotient : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  scaleStep entry quotient (quotientStep denominator entry quotient v)

def convertCode (denominator entry quotient : ℕ) : Code :=
  .seq (NaturalQuotient.code (positivePort denominator) (denominatorPort entry) (positivePort quotient))
    (NatAssign.code (scaleStage entry quotient))

theorem convert_entry (denominator entry quotient : ℕ) (hne : quotient≠entry) (v : ℕ→Parts) :
    convertStep denominator entry quotient v entry=
      ⟨((v denominator).positive/(v entry).denominator)*(v entry).positive,
       ((v denominator).positive/(v entry).denominator)*(v entry).negative,1⟩ := by
  simp [convertStep,scaleStep,quotientStep,hne.symm]

theorem convert_executes (S : Finset ℕ) (denominator entry quotient : ℕ)
    (hd : denominator∈S) (he : entry∈S) (hq : quotient∈S) (hne : quotient≠entry)
    (v : ℕ→Parts) (hentry : (v entry).Valid) (B : ℕ) (hB : 1≤B)
    (hw : ∀ i∈S, (v i).Width B) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape (convertCode denominator entry quotient) cost s t ∧
      cost≤2^102*(B+2)^2 ∧ Ready S (convertStep denominator entry quotient v) t ∧
      BinaryPrecision.Frame (changed S) s.val t.val := by
  obtain ⟨c0,t0,e0,h0,b0,f0⟩ := quotient_executes S denominator entry quotient hd he hq v hentry B hw input tape s hs
  obtain ⟨c1,t,e1,h1,b1,f1⟩ := scale_executes S entry quotient he hq hne _ B hB
    (quotientStep_width S denominator entry quotient hd hq v B hw) input tape t0 b0
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,f0.trans f1⟩
  unfold stageCost at h1
  calc
    _ ≤ (2^100+2^96)*(B+2)^2 := by nlinarith only [h0,h1]
    _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

theorem convert_entry_integerParts {ι : Type*} [Fintype ι]
    (a : ι→Parts) (i : ι) (denominator entry quotient : ℕ) (hne : quotient≠entry)
    (v : ℕ→Parts) (hd : (v denominator).positive=SharedTable.denominator a) (he : v entry=a i) :
    convertStep denominator entry quotient v entry=SharedTable.integerParts a i := by
  rw [convert_entry _ _ _ hne,hd,he]
  simp only [SharedTable.integerParts,Nat.mul_comm]

#print axioms convert_executes
#print axioms convert_entry_integerParts
end Maxwell.Continuum.RationalDataflow.SharedConversion
