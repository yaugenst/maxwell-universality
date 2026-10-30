import Maxwell.Continuum.NaturalBankStage
import Maxwell.Cost.RationalCanonical.Divide

/-! Exact natural division of runtime register values, including loading and cleanup. -/
namespace Maxwell.Continuum.RationalDataflow.NaturalQuotient
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def workPorts : Finset ℕ := {220,221,222,223}
def prepare (source divisor : ℕ) : List NatAssign.Instruction :=
  [.copy source 220,.copy divisor 221]
def finish (target : ℕ) : List NatAssign.Instruction :=
  [.copy 222 target,.literal 220 0,.literal 221 0,.literal 222 0,.literal 223 0]
def code (source divisor target : ℕ) : Code :=
  .seq (NatAssign.code (prepare source divisor))
    (.seq RationalCanonical.divideCode (NatAssign.code (finish target)))
def loadedValues (v : ℕ→ℕ) (a b : ℕ) : ℕ→ℕ :=
  Function.update (Function.update v 220 a) 221 b
def dividedValues (v : ℕ→ℕ) (a b : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (loadedValues v a b) 222 (a/b)) 223 (a%b)

theorem prepare_values (source divisor : ℕ) (hdivisor : divisor∉workPorts) (v : ℕ→ℕ) :
    NatAssign.values (prepare source divisor) v=loadedValues v (v source) (v divisor) := by
  have hne : divisor≠220 := by simp only [workPorts,Finset.mem_insert,Finset.mem_singleton,not_or] at hdivisor; tauto
  simp [prepare,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,loadedValues,hne]

theorem finish_values (target : ℕ) (ht : target∉workPorts) (v : ℕ→ℕ)
    (hv : ∀ i∈workPorts, v i=0) (a b : ℕ) :
    NatAssign.values (finish target) (dividedValues v a b)=Function.update v target (a/b) := by
  have ht' := ht
  simp only [workPorts,Finset.mem_insert,Finset.mem_singleton,not_or] at ht'
  ext i
  by_cases hi : i∈workPorts
  · have hi' := hi
    simp only [workPorts,Finset.mem_insert,Finset.mem_singleton] at hi'
    rcases hi' with rfl | rfl | rfl | rfl <;>
      simp [finish,dividedValues,loadedValues,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.value,NatAssign.Instruction.target,hv _ hi,
        Ne.symm ht'.1,Ne.symm ht'.2.1,Ne.symm ht'.2.2.1,Ne.symm ht'.2.2.2]
  · have hi' := hi
    simp only [workPorts,Finset.mem_insert,Finset.mem_singleton,not_or] at hi'
    by_cases hit : i=target
    · subst i
      simp [finish,dividedValues,loadedValues,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.value,NatAssign.Instruction.target,hi'.1,hi'.2.1,hi'.2.2.1,hi'.2.2.2]
    · simp [finish,dividedValues,loadedValues,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.value,NatAssign.Instruction.target,hi'.1,hi'.2.1,hi'.2.2.1,hi'.2.2.2,hit]

theorem executes (allIds : Finset ℕ) (hids : ∀ i∈allIds, 10 ≤ i) (hwork : workPorts⊆allIds)
    (source divisor target : ℕ) (hsource : source∈allIds) (hdivisor : divisor∈allIds)
    (htarget : target∈allIds) (hswork : source∉workPorts) (hdwork : divisor∉workPorts)
    (htwork : target∉workPorts) (v : ℕ→ℕ) (hzero : ∀ i∈workPorts, v i=0)
    (hpos : 0<v divisor) (B : ℕ) (hw : ∀ i∈allIds, (v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hbank : NatAssign.Bank allIds v s.val)
    (hscratch : ∀ i, i<5 → Blank s.val i) :
    ∃ cost t, Executes input tape (code source divisor target) cost s t ∧
      cost≤2^100*(B+2)^2 ∧ NatAssign.Bank allIds (Function.update v target (v source/v divisor)) t.val ∧
      (∀ i, i<5 → Blank t.val i) ∧ BinaryPrecision.Frame ({0,1,2,3,4}∪allIds) s.val t.val := by
  have port (i : ℕ) (hi : i∈workPorts) : i∈allIds := hwork hi
  have h220 := port 220 (by decide)
  have h221 := port 221 (by decide)
  have h222 := port 222 (by decide)
  have h223 := port 223 (by decide)
  have source220 : source≠220 := by
    intro he; subst source; exact hswork (by decide)
  have divisor221 : divisor≠221 := by
    intro he; subst divisor; exact hdwork (by decide)
  have target222 : (222:ℕ)≠target := by
    intro he; subst target; exact htwork (by decide)
  have hpvalid : ∀ a∈prepare source divisor, a.Valid allIds := by
    simp [prepare,NatAssign.Instruction.Valid,hsource,hdivisor,h220,h221,source220,divisor221]
  obtain ⟨c0,t0,e0,h0,b0,z0,f0⟩ := fixedBankStage_executes allIds (fun i hi => by have := hids i hi; omega)
    (prepare source divisor) hpvalid (by simp [prepare]) v B hw
    (by simp [prepare,NatAssign.Instruction.literalWidth]) input tape s hbank (fun i hi => hscratch i (by omega))
  rw [prepare_values source divisor hdwork] at b0
  have blank0 (i : ℕ) (hi : i<5) : Blank t0.val i := by
    by_cases hlt : i<4
    · exact z0 i hlt
    · have hi4 : i=4 := by omega
      subst i
      apply RationalAccumulator.blank_of_eq (f0.tapes 4 _) (hscratch 4 (by decide))
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨by omega,by intro hm; have := hids 4 hm; omega⟩
  have zero0 (i : ℕ) (hi : i=222 ∨ i=223) : Blank t0.val i := by
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    rcases hi with rfl | rfl
    · simpa [loadedValues,hzero 222 (by decide)] using b0 222 h222
    · simpa [loadedValues,hzero 223 (by decide)] using b0 223 h223
  obtain ⟨cd,td,hcd,ed,hq,hr,hnum,hden,zd,fd⟩ := RationalCanonical.divide input tape
    (v source) (v divisor) hpos t0
    (by simpa [loadedValues] using b0 220 h220) (by simpa [loadedValues] using b0 221 h221)
    blank0 (zero0 _ (Or.inl rfl)) (zero0 _ (Or.inr rfl))
  have bd : NatAssign.Bank allIds (dividedValues v (v source) (v divisor)) td.val := by
    intro i hi
    by_cases hi222 : i=222
    · subst i; simpa [dividedValues] using hq
    · by_cases hi223 : i=223
      · subst i; simpa [dividedValues] using hr
      · have hkeep : i∉({0,1,2,3,4,222,223}:Finset ℕ) := by
          have := hids i hi
          simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
          omega
        simpa only [dividedValues,Function.update_of_ne hi222,Function.update_of_ne hi223]
          using RationalAccumulator.word_of_eq (fd.tapes i hkeep) (b0 i hi)
  have wd : ∀ i∈allIds, (dividedValues v (v source) (v divisor) i).bits.length≤B := by
    have hqwidth : (v source/v divisor).bits.length≤B := by
      rw [Nat.size_eq_bits_len]
      exact (Nat.size_le_size (Nat.div_le_self _ _)).trans (by simpa only [Nat.size_eq_bits_len] using hw source hsource)
    have hrwidth : (v source%v divisor).bits.length≤B := by
      rw [Nat.size_eq_bits_len]
      exact (Nat.size_le_size (Nat.mod_lt _ hpos).le).trans (by simpa only [Nat.size_eq_bits_len] using hw divisor hdivisor)
    intro i hi
    by_cases h220' : i=220
    · subst i; simpa [dividedValues,loadedValues] using hw source hsource
    · by_cases h221' : i=221
      · subst i; simpa [dividedValues,loadedValues] using hw divisor hdivisor
      · by_cases h222' : i=222
        · subst i; simpa [dividedValues] using hqwidth
        · by_cases h223' : i=223
          · subst i; simpa [dividedValues] using hrwidth
          · simpa [dividedValues,loadedValues,h220',h221',h222',h223'] using hw i hi
  have hfvalid : ∀ a∈finish target, a.Valid allIds := by
    simp [finish,NatAssign.Instruction.Valid,h220,h221,h222,h223,htarget,target222]
  obtain ⟨c1,t,e1,h1,b1,z1,f1⟩ := fixedBankStage_executes allIds (fun i hi => by have := hids i hi; omega)
    (finish target) hfvalid (by simp [finish]) (dividedValues v (v source) (v divisor)) B wd
    (by simp [finish,NatAssign.Instruction.literalWidth]) input tape td bd (fun i hi => zd i (by omega))
  rw [finish_values target htwork v hzero] at b1
  have liftFrame {u w : BitRAMState} (f : BinaryPrecision.Frame ({0,1,2,3}∪allIds) u w) :
      BinaryPrecision.Frame ({0,1,2,3,4}∪allIds) u w := f.mono (by
    intro i hi
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    tauto)
  have fd' : BinaryPrecision.Frame ({0,1,2,3,4}∪allIds) t0.val td.val := by
    refine ⟨fd.address,fd.inputHead,fd.memory,fd.randomCursor,fd.output,fun i hi => fd.tapes i ?_⟩
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hi ⊢
    rcases hi with ⟨hsmall,hbig⟩
    have h222' : i≠222 := by intro he; subst i; exact hbig h222
    have h223' : i≠223 := by intro he; subst i; exact hbig h223
    tauto
  refine ⟨c0+(cd+c1),t,e0.seq (ed.seq e1),?_,b1,?_,(liftFrame f0).trans (fd'.trans (liftFrame f1))⟩
  · have hnumWidth := hw source hsource
    have hdenWidth := hw divisor hdivisor
    have hsq := Nat.pow_le_pow_left (show (v source).bits.length+(v divisor).bits.length+2≤2*B+2 by omega) 2
    have hsq2 : (2*B+2)^2≤4*(B+2)^2 := by nlinarith
    have hcd' : cd≤4000*(B+2)^2 := by nlinarith only [hcd,hsq,hsq2]
    unfold stageCost at h0 h1
    calc
      _ ≤ (2^96+4000+2^96)*(B+2)^2 := by nlinarith only [h0,h1,hcd']
      _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)
  · intro i hi
    by_cases hlt : i<4
    · exact z1 i hlt
    · have hi4 : i=4 := by omega
      subst i
      apply RationalAccumulator.blank_of_eq (f1.tapes 4 _) (zd 4 (by decide))
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨by omega,by intro hm; have := hids 4 hm; omega⟩

#print axioms executes
end Maxwell.Continuum.RationalDataflow.NaturalQuotient
