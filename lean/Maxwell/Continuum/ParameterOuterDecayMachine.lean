import Maxwell.Continuum.ParameterOuterStageSearches

/-! Executed floor exponentials for leakage and tail. Both calls use the
same quotient and binary-power primitives and preserve a uniform bank width. -/
namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
open RationalAccumulator (Blank Word)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def decayClears (quotient target : ℕ) : List ℕ := [220,221,222,223,2254,quotient,target]
def decayReset (quotient target : ℕ) : List NatAssign.Instruction :=
  (decayClears quotient target).map fun i=>.literal i 0
def decayCode (source quotient target : ℕ) : Code :=
  .seq (NatAssign.code (decayReset quotient target))
    (.seq (RationalDataflow.NaturalQuotient.code source 2226 quotient)
      (RoutingPorts.powerCode quotient 2254 target))
def decayValues (v : ℕ→ℕ) (source quotient target : ℕ) : ℕ→ℕ :=
  Function.update (Function.update (NatAssign.values (decayReset quotient target) v)
    quotient (v source/slowDivisor)) target (2^(v source/slowDivisor))
def decayCost (W : ℕ) : ℕ := (3000*8^7+2^100+50)*(W+2)^2

theorem decay_executes (source quotient target : ℕ)
    (hsource : source=2220 ∨ source=2221) (hq : quotient=2250 ∨ quotient=2252)
    (ht : target=2251 ∨ target=2253) (v : ℕ→ℕ) (W : ℕ)
    (hd : v 2226=slowDivisor) (hv : v source+1 ≤ W) (hw : ∀i∈ids,(v i).bits.length ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→Blank s.val i) :
    ∃cost t,Executes input tape (decayCode source quotient target) cost s t ∧
      cost ≤ decayCost W ∧ NatAssign.Bank ids (decayValues v source quotient target) t.val ∧
      (∀i,i<5→Blank t.val i) ∧
      (∀i∈ids,(decayValues v source quotient target i).bits.length ≤ W) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  have sp : source∈ids := by rcases hsource with rfl|rfl <;> decide +kernel
  have qp : quotient∈ids := by rcases hq with rfl|rfl <;> decide +kernel
  have tp : target∈ids := by rcases ht with rfl|rfl <;> decide +kernel
  have hvalid : ∀a∈decayReset quotient target,a.Valid ids := by
    simp [decayReset,decayClears,NatAssign.Instruction.Valid,qp,tp]
    decide +kernel
  obtain ⟨cr,r,er,pr,br,sr,fr⟩ := NatAssign.executes ids (fun i hi=>by have := ids_ge i hi;omega)
    (decayReset quotient target) hvalid v input tape s hb (fun i hi=>hs i (by omega))
  have prc := NatAssign.price_bound ids (decayReset quotient target) hvalid v W hw
    (by simp [decayReset,decayClears,NatAssign.Instruction.literalWidth])
  let vr := NatAssign.values (decayReset quotient target) v
  have rv (i : ℕ) : vr i=if i∈decayClears quotient target then 0 else v i :=
    NatAssign.values_literals (decayClears quotient target) (fun _=>0) v i
  have rs : vr source=v source := by rw [rv];simp only [decayClears,List.mem_cons,List.not_mem_nil,or_false];split_ifs <;> omega
  have rd : vr 2226=slowDivisor := by
    rw [rv]
    simp only [decayClears,List.mem_cons,List.not_mem_nil,or_false]
    split_ifs <;> omega
  have rwid : ∀i∈ids,(vr i).bits.length ≤ W := by
    intro i hi;rw [rv];split_ifs <;> first | exact hw i hi | simp
  have rz : ∀i∈RationalDataflow.NaturalQuotient.workPorts,vr i=0 := by
    intro i hi
    rw [rv]
    simp only [RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> simp [decayClears]
  have fr' : BinaryPrecision.Frame ({0,1,2,3}∪ids) s.val r.val := fr.mono (by
    rcases hq with rfl|rfl <;> rcases ht with rfl|rfl <;> decide +kernel)
  have sr' : ∀i,i<5→Blank r.val i := by
    intro i hi
    by_cases h4 : i<4
    · exact sr i h4
    · have he : i=4 := by omega
      subst i;exact RationalAccumulator.blank_of_eq (fr'.tapes 4 (by decide +kernel)) (hs 4 (by decide))
  obtain ⟨cq,q,eq,pq,bq,sq,fq⟩ := RationalDataflow.NaturalQuotient.executes ids ids_ge
    (by decide +kernel) source 2226 quotient sp (by decide +kernel) qp
    (by simp only [RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton];omega)
    (by decide) (by simp only [RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton];omega)
    vr rz (by rw [rd];exact slowDivisor_pos) W rwid input tape r br sr'
  let vq := Function.update vr quotient (vr source/vr 2226)
  have qvalue : vq quotient=v source/slowDivisor := by simp [vq,rs,rd]
  have qzero (i : ℕ) (hi : i=2254 ∨ i=target) : vq i=0 := by
    have hne : i≠quotient := by omega
    rw [show vq i=vr i from Function.update_of_ne hne _ _,rv]
    rcases hi with rfl|rfl <;> simp [decayClears]
  have qwid : ∀i∈ids,(vq i).bits.length ≤ W := by
    intro i hi
    by_cases he : i=quotient
    · subst i
      rw [qvalue,Nat.size_eq_bits_len]
      exact (Nat.size_le_size (Nat.div_le_self _ _)).trans (by simpa only [Nat.size_eq_bits_len] using hw source sp)
    · simpa only [vq,Function.update_of_ne he] using rwid i hi
  obtain ⟨cp,t,ep,pp,bt,ft⟩ := NatAssign.binaryPower ids quotient 2254 target qp (by decide +kernel) tp
    (by omega) (by omega) (by omega) vq (qzero _ (Or.inl rfl)) (qzero _ (Or.inr rfl)) input tape q bq
  have hn : vq quotient ≤ W := by rw [qvalue];have := Nat.div_le_self (v source) slowDivisor;omega
  have hnw := qwid quotient qp
  have pp' : cp ≤ 50*(W+2)^2 := pp.trans ((show
      (vq quotient+1)*(13*(vq quotient).bits.length+25)+21*(vq quotient).bits.length+27 ≤
        BufferMachine.powerCost (vq quotient) W by unfold BufferMachine.powerCost;gcongr).trans
      (BufferMachine.powerCost_bound _ _ hn))
  have outvalues : Function.update vq target (2^(vq quotient))=decayValues v source quotient target := by
    simp only [decayValues,vq,rs,rd,Function.update_self]
    rfl
  rw [outvalues] at bt
  refine ⟨cr+(cq+cp),t,er.seq (eq.seq ep),?_,bt,?_,?_,
    (fr'.mono (by decide +kernel)).trans ((fq.mono (by decide +kernel)).trans (ft.mono ?_))⟩
  · have pr' : cr ≤ 3000*8^7*(W+2)^2 := by
      simpa only [decayReset,decayClears,List.length_map,List.length_cons,List.length_nil] using pr.trans prc
    unfold decayCost
    nlinarith only [pr',pq,pp']
  · intro i hi
    exact RationalAccumulator.blank_of_eq (ft.tapes i (by simp;omega)) (sq i hi)
  · intro i hi
    rw [← outvalues]
    by_cases he : i=target
    · subst i
      rw [Function.update_self,qvalue,Nat.size_eq_bits_len,Nat.size_pow]
      have := Nat.div_le_self (v source) slowDivisor
      omega
    · simpa only [Function.update_of_ne he] using qwid i hi
  · rcases ht with rfl|rfl <;> decide +kernel

#print axioms decay_executes
end Maxwell.Continuum.Parameters.OuterMachine
