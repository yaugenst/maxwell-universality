import Maxwell.Continuum.CalibrationBasisForcingMachine
import Maxwell.Continuum.CalibrationArrayDecodeGeneral
import Maxwell.Continuum.RationalDataflowArray

/-! A runtime flat alias index is decoded and its actual Schur forcing value
is computed. The radius and physical scalar registers survive this call. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow
open ArrayDecodeMachine
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048

def bank : Finset ℕ := Finset.range 232
def naturalIds : Finset ℕ := ids bank ∪ ArrayDecodeMachine.ports ∪ NaturalQuotient.workPorts
def changed : Finset ℕ := {0,1,2,3,4} ∪ naturalIds
def prepareCode (column : Fin 24) : Code := .seq decodeLoadCode (code column)
def prepareWidth (B : ℕ) : ℕ := 2^265*(2*B+9)
def preparedNaturals (n : ℕ → ℕ) (out : ℕ → Parts) (k : ℕ) : ℕ :=
  if k∈ids bank then dataValues out k else NatAssign.values coordinateLoad (output n) k

attribute [local irreducible] bank code decodeLoadCode

theorem naturalIds_parts : ids bank⊆naturalIds := fun _ h =>
  Finset.mem_union_left _ (Finset.mem_union_left _ h)
theorem naturalIds_decode : ArrayDecodeMachine.ports⊆naturalIds := fun _ h =>
  Finset.mem_union_left _ (Finset.mem_union_right _ h)
theorem naturalIds_work : NaturalQuotient.workPorts⊆naturalIds := Finset.subset_union_right
theorem naturalIds_ge (k : ℕ) (hk : k∈naturalIds) : 10≤k := by
  rcases Finset.mem_union.mp hk with hk|hk
  · rcases Finset.mem_union.mp hk with hk|hk
    · exact ids_ge_ten _ k hk
    · simp only [ArrayDecodeMachine.ports,Finset.mem_Icc] at hk
      omega
  · simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk
    omega

private theorem workspace_subset : workspace bank⊆changed := by
  intro k hk
  rcases Finset.mem_union.mp hk with hz|hp
  · exact Finset.mem_union_left _ (by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢
      tauto)
  · exact Finset.mem_union_right _ (naturalIds_parts hp)

theorem prepare_executes (column : Fin 24) (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀k∈ids bank,n k=dataValues v k)
    (hzwork : ∀k∈NaturalQuotient.workPorts,n k=0) (hg : Good bank v)
    (B : ℕ) (hB : 103≤B) (hw : ∀k∈naturalIds,(n k).bits.length≤B)
    (R : ℕ) (i : Fin (aliasArraySize R)) (hR : n 311=R) (hi : n 310=i.val)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank naturalIds n s.val)
    (hz : ∀k,k<5 → RationalAccumulator.Blank s.val k) :
    ∃cost t out,Executes input tape (prepareCode column) cost s t ∧
      cost≤2^655*(B+5)^2 ∧ Ready bank out t ∧ Good bank out ∧
      WidthBank bank (prepareWidth B) out ∧ (out 32).Width 625 ∧
      NatAssign.Bank naturalIds (preparedNaturals n out) t.val ∧
      (∀k∈naturalIds,(preparedNaturals n out k).bits.length≤prepareWidth B) ∧
      (out 32).value=rationalRightCoupling (rationalBasisField column)
        (arrayAliasAt R i) (arrayPolarizationAt R i) ∧
      (∀k,k<32 → k≠13 → k≠14 → k≠15 → k≠23 → out k=v k) ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,ready,good,width,widthNat,coordinates,pol,four,f0⟩ :=
    decodeLoad_all_executes bank naturalIds naturalIds_ge naturalIds_decode naturalIds_work naturalIds_parts
      (by intro k hk; simp only [RawFree.stageRegisters,bank,Finset.mem_range] at hk ⊢;omega)
      n v hn hzwork hg B (by omega) hw R i hR hi input tape s hs hz
  let w := loadedParts v (output n)
  obtain ⟨c1,t,out,e1,hc1,r1,g1,w1,entryWidth,result,keep,f1⟩ := executes column (2*B+8) (by omega) w
    (by simpa only [bank] using width) (by simpa only [bank] using good)
    (arrayAliasAt R i) (arrayPolarizationAt R i) coordinates pol input tape u
    (by simpa only [bank] using ready)
  have bank_eq : bank=Finset.range 232 := by unfold bank;rfl
  rw [← bank_eq] at r1 g1 w1 f1
  have naturalBank : NatAssign.Bank naturalIds (preparedNaturals n out) t.val := by
    intro k hk
    by_cases hp : k∈ids bank
    · simpa only [preparedNaturals,ite_eq_left hp] using r1.1 k hp
    · have ho : k∉workspace bank := by
        have hge := naturalIds_ge k hk
        simp only [workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨by omega,hp⟩
      simpa only [preparedNaturals,ite_eq_right hp] using
        RationalAccumulator.word_of_eq (f1.tapes k ho) (b0 k hk)
  have hbase : 2*B+8≤prepareWidth B := by unfold prepareWidth;omega
  have naturalWidth : ∀k∈naturalIds,(preparedNaturals n out k).bits.length≤prepareWidth B := by
    intro k hk
    by_cases hp : k∈ids bank
    · rw [preparedNaturals,ite_eq_left hp]
      exact dataValues_width bank out (prepareWidth B) w1 k hp
    · rw [preparedNaturals,ite_eq_right hp]
      exact (widthNat k hk).trans hbase
  have blank (k : ℕ) (hk : k<5) : RationalAccumulator.Blank t.val k := by
    by_cases h4 : k<4
    · exact r1.2 k h4
    · have he : k=4 := by omega
      subst k
      have external : 4∉workspace bank := by
        simp only [workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        have hh : 4∉ids bank := fun h => by have := ids_ge_ten bank 4 h;omega
        simp [hh]
      exact RationalAccumulator.blank_of_eq (f1.tapes 4 external) four
  refine ⟨c0+c1,t,out,e0.seq e1,?_,r1,g1,w1,entryWidth,naturalBank,naturalWidth,result,?_,blank,
    f0.trans (f1.mono workspace_subset)⟩
  · have sq : (2*B+8+1)^2≤4*(B+5)^2 := by nlinarith
    nlinarith only [hc0,hc1,sq,Nat.zero_le ((B+5)^2)]
  · intro k hk h13 h14 h15 h23
    rw [keep k hk]
    simp only [w,loadedParts,Function.update_of_ne h13,Function.update_of_ne h14,
      Function.update_of_ne h15,Function.update_of_ne h23]

#print axioms prepare_executes
end Maxwell.Continuum.Calibration.BasisForcing
