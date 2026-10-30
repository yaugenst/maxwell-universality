import Maxwell.Continuum.SourceRoutingTreeWorkspace
import Maxwell.Continuum.NaturalBankDivMod

/-! The fixed tree controller divides runtime words on a private fifth
scratch tape. The source parser's tape 4 is preserved. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Division
open Structured Maxwell.Continuum.RationalDataflow
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def controls : Finset ℕ := Finset.Icc 800 819
def ids : Finset ℕ := controls∪NaturalQuotient.workPorts
def relocation : Equiv.Perm ℕ := Equiv.swap 4 839
def work : Finset ℕ := {0,1,2,3,839}∪ids
def code (source divisor targetQ targetR : ℕ) : Code :=
  .call ((NaturalDivMod.code source divisor targetQ targetR).compile.renameTapes relocation)

@[simp] theorem relocation_symm : relocation.symm=relocation := Equiv.symm_swap _ _
theorem fixed (i : ℕ) (hi : i≠4) (hj : i≠839) : relocation i=i :=
  Equiv.swap_apply_of_ne_of_ne hi hj
theorem ids_lower (i : ℕ) (hi : i∈ids) : 10 ≤ i := by
  simp only [ids,controls,NaturalQuotient.workPorts,Finset.mem_union,
    Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
  omega
theorem ids_fixed (i : ℕ) (hi : i∈ids) : relocation i=i := by
  apply fixed
  all_goals simp only [ids,controls,NaturalQuotient.workPorts,Finset.mem_union,
    Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
  all_goals omega

theorem renamed_tape (s : Store) (i : ℕ) :
    (s.renameTapes relocation).val.tapes i=s.val.tapes (relocation i) := by
  simp only [Store.renameTapes,BitRAMState.renameTapes,relocation_symm,Function.comp_apply]

theorem frame {s t : Store}
    (hf : BinaryPrecision.Frame ({0,1,2,3,4}∪ids) (s.renameTapes relocation.symm).val t.val) :
    BinaryPrecision.Frame work s.val (t.renameTapes relocation).val := by
  refine ⟨hf.address,hf.inputHead,hf.memory,hf.randomCursor,hf.output,?_⟩
  intro i hi
  have hi' := hi
  simp only [work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hi'
  by_cases h4 : i=4
  · subst i
    exact hf.tapes 839 (by decide)
  · have he := fixed i h4 hi'.1.2.2.2.2
    have hh := hf.tapes i (by
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨⟨hi'.1.1,hi'.1.2.1,hi'.1.2.2.1,hi'.1.2.2.2.1,h4⟩,hi'.2⟩)
    simpa only [relocation_symm,renamed_tape,he] using hh

theorem work_disjoint (i : ℕ) (hi : i∈Workspace.ids) (hlo : 4 ≤ i) : i∉work := by
  rcases Finset.mem_union.mp hi with hi|hi
  · simp only [Workspace.small,Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [work,ids,controls,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton]
    omega
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    have hr : 80 ≤ j ∧ j ≤ 196 := by
      simp only [NodeCleanup.banks,List.mem_cons,List.not_mem_nil,or_false] at hj
      omega
    rw [PrivateNode.shift_source j hr]
    simp only [work,ids,controls,NaturalQuotient.workPorts,Finset.mem_union,
      Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton]
    omega

theorem executes (source divisor targetQ targetR : ℕ)
    (hsource : source∈controls) (hdivisor : divisor∈controls)
    (htargetQ : targetQ∈controls) (htargetR : targetR∈controls) (hne : targetQ≠targetR)
    (v : ℕ→ℕ) (hzero : ∀i∈NaturalQuotient.workPorts,v i=0) (hpos : 0<v divisor)
    (B : ℕ) (hw : ∀i∈ids,(v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NatAssign.Bank ids v s.val)
    (hc : PrivateVisit.Clean s) (h839 : Blank s.val 839) :
    ∃steps t, Executes input tape (code source divisor targetQ targetR) steps s t ∧
      steps ≤ 2^100*(B+2)^2+1 ∧
      NatAssign.Bank ids (Function.update (Function.update v targetQ (v source/v divisor)) targetR (v source%v divisor)) t.val ∧
      PrivateVisit.Clean t ∧ Blank t.val 839 ∧ BinaryPrecision.Frame work s.val t.val := by
  have port (i : ℕ) (hi : i∈controls) : i∈ids := Finset.mem_union_left _ hi
  have outside (i : ℕ) (hi : i∈controls) : i∉NaturalQuotient.workPorts := by
    simp only [controls,Finset.mem_Icc] at hi
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton]
    omega
  have ba : NatAssign.Bank ids v (s.renameTapes relocation.symm).val := by
    intro i hi
    apply RationalAccumulator.word_of_eq _ (hs i hi)
    rw [relocation_symm,renamed_tape,ids_fixed i hi]
  have za : ∀i,i<5→Blank (s.renameTapes relocation.symm).val i := by
    intro i hi
    by_cases hi4 : i=4
    · subst i; exact h839
    · apply RationalAccumulator.blank_of_eq _ (Workspace.scratch hc i (by omega))
      rw [relocation_symm,renamed_tape,fixed i hi4 (by omega)]
  obtain ⟨steps,u,he,hcost,bu,zu,fu⟩ := NaturalDivMod.executes ids ids_lower
    Finset.subset_union_right source divisor targetQ targetR
    (port _ hsource) (port _ hdivisor) (port _ htargetQ) (port _ htargetR)
    (outside _ hsource) (outside _ hdivisor) (outside _ htargetQ) (outside _ htargetR)
    hne v hzero hpos B hw input tape (s.renameTapes relocation.symm) ba za
  let t := u.renameTapes relocation
  have ft := frame fu
  have bt : NatAssign.Bank ids
      (Function.update (Function.update v targetQ (v source/v divisor)) targetR (v source%v divisor)) t.val := by
    intro i hi
    apply RationalAccumulator.word_of_eq _ (bu i hi)
    exact (renamed_tape u i).trans (congrArg u.val.tapes (ids_fixed i hi))
  have zt : NatAssign.Scratch t.val := by
    intro i hi
    apply RationalAccumulator.blank_of_eq _ (zu i (by omega))
    exact (renamed_tape u i).trans (congrArg u.val.tapes (fixed i (by omega) (by omega)))
  refine ⟨steps+1,t,?_,by omega,bt,Workspace.of_frame hc zt ft work_disjoint,zu 4 (by decide),ft⟩
  simpa only [code,Store.renameTapes_symm] using he.renamed_call relocation

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.Division
