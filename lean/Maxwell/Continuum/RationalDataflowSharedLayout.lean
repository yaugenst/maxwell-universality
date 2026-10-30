import Maxwell.Continuum.NaturalBankQuotient
import Maxwell.Continuum.RationalDataflowArray

/-! Register-bank interface for raw shared-denominator conversion. -/
namespace Maxwell.Continuum.RationalDataflow.SharedConversion
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000

def bankIds (S : Finset ℕ) : Finset ℕ := ids S∪NaturalQuotient.workPorts
def changed (S : Finset ℕ) : Finset ℕ := {0,1,2,3,4}∪bankIds S
def Ready (S : Finset ℕ) (v : ℕ→Parts) (s : Store) : Prop :=
  NatAssign.Bank (bankIds S) (dataValues v) s.val ∧
    (∀ i, i<5 → RationalAccumulator.Blank s.val i)

theorem bankIds_ge (S : Finset ℕ) (i : ℕ) (hi : i∈bankIds S) : 10 ≤ i := by
  rcases Finset.mem_union.mp hi with hi | hi
  · exact ids_ge_ten S i hi
  · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    omega

theorem work_values_zero (v : ℕ→Parts) (i : ℕ) (hi : i∈NaturalQuotient.workPorts) : dataValues v i=0 := by
  apply dataValues_small
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem values_width (S : Finset ℕ) (v : ℕ→Parts) (B : ℕ)
    (hw : ∀ i∈S, (v i).Width B) (i : ℕ) (hi : i∈bankIds S) : (dataValues v i).bits.length≤B := by
  rcases Finset.mem_union.mp hi with hi | hi
  · exact dataValues_width S v B hw i hi
  · rw [work_values_zero v i hi]
    simp

theorem Ready.rational {S : Finset ℕ} {v : ℕ→Parts} {s : Store} (h : Ready S v s) :
    RationalDataflow.Ready S v s :=
  ⟨fun i hi => h.1 i (Finset.mem_union_left _ hi),fun i hi => h.2 i (by omega)⟩

def quotientStep (denominator entry quotient : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update v quotient ⟨(v denominator).positive/(v entry).denominator,
    (v quotient).negative,(v quotient).denominator⟩

theorem quotientStep_values (denominator entry quotient : ℕ) (v : ℕ→Parts) :
    Function.update (dataValues v) (positivePort quotient)
      ((v denominator).positive/(v entry).denominator)=
        dataValues (quotientStep denominator entry quotient v) := by
  rw [quotientStep,←writeParts_dataValues]
  ext i
  by_cases hp : i=positivePort quotient
  · subst i; simp [writeParts]
  · by_cases hn : i=negativePort quotient
    · subst i; simp [writeParts]
    · by_cases hd : i=denominatorPort quotient
      · subst i; simp [writeParts]
      · simp [writeParts,hp,hn,hd]

theorem quotient_executes (S : Finset ℕ) (denominator entry quotient : ℕ)
    (hd : denominator∈S) (he : entry∈S) (hq : quotient∈S) (v : ℕ→Parts)
    (hentry : (v entry).Valid) (B : ℕ) (hw : ∀ i∈S, (v i).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape
      (NaturalQuotient.code (positivePort denominator) (denominatorPort entry) (positivePort quotient)) cost s t ∧
      cost≤2^100*(B+2)^2 ∧ Ready S (quotientStep denominator entry quotient v) t ∧
      BinaryPrecision.Frame (changed S) s.val t.val := by
  have logical (i : ℕ) (hi : i∈ids S) : i∈bankIds S := Finset.mem_union_left _ hi
  have outside (i : ℕ) (hi : 1000 ≤ i) : i∉NaturalQuotient.workPorts := by
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton,not_or]
    omega
  obtain ⟨cost,t,hex,hcost,hbank,hsc,hframe⟩ := NaturalQuotient.executes (bankIds S) (bankIds_ge S)
    (Finset.subset_union_right) (positivePort denominator) (denominatorPort entry) (positivePort quotient)
    (logical _ (cell_mem hd (by simp [cellPorts])))
    (logical _ (cell_mem he (by simp [cellPorts])))
    (logical _ (cell_mem hq (by simp [cellPorts])))
    (outside _ (positivePort_ge _)) (outside _ (denominatorPort_ge _))
    (outside _ (positivePort_ge _)) (dataValues v) (work_values_zero v)
    (by simpa only [dataValues_denominator,Parts.Valid] using hentry) B (values_width S v B hw)
    input tape s hs.1 hs.2
  simp only [dataValues_positive,dataValues_denominator,quotientStep_values] at hbank
  exact ⟨cost,t,hex,hcost,⟨hbank,hsc⟩,hframe⟩

#print axioms quotient_executes
end Maxwell.Continuum.RationalDataflow.SharedConversion
