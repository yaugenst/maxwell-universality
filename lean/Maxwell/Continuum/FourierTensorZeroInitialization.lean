import Maxwell.Continuum.FourierTensorComputedWorkspace

/-! Reinitialize the shared rational row bank by charged scans and literal
denominator writes. Previous calibration words need not be blank. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ZeroInitialization
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def clearPorts : List ℕ := (workspace RowArithmetic.bank).sort (·≤·)
def denominators : List ℕ := (List.range 28).map denominatorPort
def plan : List NatAssign.Instruction := denominators.map (fun i => .literal i 1)
def code : Code := .seq (WordCleanup.code clearPorts) (NatAssign.code plan)

private theorem ones_values (xs : List ℕ) (v : ℕ→ℕ) (i : ℕ) :
    NatAssign.values (xs.map (fun j => .literal j 1)) v i=if i∈xs then 1 else v i := by
  induction xs generalizing v with
  | nil => simp [NatAssign.values]
  | cons x xs ih =>
    simp only [List.map_cons,NatAssign.values]
    rw [ih]
    by_cases hi : i∈xs
    · simp only [hi,List.mem_cons,or_true,ite_true]
    · by_cases he : i=x
      · subst i
        simp only [hi,List.mem_cons,true_or,ite_true,ite_false,NatAssign.Instruction.update,
          NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_self]
      · simp only [hi,he,List.mem_cons,false_or,ite_false,NatAssign.Instruction.update,
          NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_of_ne he]

private theorem no_positive (j : ℕ) : positivePort j∉denominators := by
  simp only [denominators,List.mem_map,List.mem_range]
  rintro ⟨k,_,he⟩
  unfold denominatorPort positivePort at he
  omega

private theorem no_negative (j : ℕ) : negativePort j∉denominators := by
  simp only [denominators,List.mem_map,List.mem_range]
  rintro ⟨k,_,he⟩
  unfold denominatorPort negativePort at he
  omega

private theorem denominator_mem {j : ℕ} (hj : j∈RowArithmetic.bank) : denominatorPort j∈denominators := by
  exact List.mem_map.mpr ⟨j,by simpa only [RowArithmetic.bank,Finset.mem_range,List.mem_range] using hj,rfl⟩

theorem plan_values (i : ℕ) (hi : i∈RationalDataflow.ids RowArithmetic.bank) :
    NatAssign.values plan (fun _ => 0) i=dataValues ModePrelude.zeroValues i := by
  rw [plan,ones_values]
  rcases Finset.mem_union.mp hi with hp|hw
  · obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hp
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hij
    rcases hij with rfl|rfl|rfl
    · simp only [no_positive,ite_false,dataValues_positive,ModePrelude.zeroValues]
      rfl
    · simp only [no_negative,ite_false,dataValues_negative,ModePrelude.zeroValues]
      rfl
    · simp only [denominator_mem hj,ite_true,dataValues_denominator,ModePrelude.zeroValues]
      rfl
  · have hs : i<1000 := by
      simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hw
      omega
    have hn : i∉denominators := by
      simp only [denominators,List.mem_map,List.mem_range]
      rintro ⟨j,_,he⟩
      have hg := denominatorPort_ge j
      omega
    simp only [hn,ite_false,dataValues_small _ hs]

theorem plan_valid : ∀a∈plan,a.Valid (RationalDataflow.ids RowArithmetic.bank) := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  exact cell_mem (by simpa only [RowArithmetic.bank,Finset.mem_range,List.mem_range] using hj)
    (by simp [cellPorts])

theorem executes (B : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : WordCleanup.Bounded clearPorts B s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤2^128*(B+1)^2 ∧
      Ready RowArithmetic.bank ModePrelude.zeroValues t ∧
      BinaryPrecision.Frame (workspace RowArithmetic.bank) s.val t.val := by
  obtain ⟨c0,u,e0,hc0,z0,f0⟩ := WordCleanup.executes clearPorts B input tape s hb
  have hcset : clearPorts.toFinset=workspace RowArithmetic.bank := by
    ext i
    simp [clearPorts]
  have bank : NatAssign.Bank (RationalDataflow.ids RowArithmetic.bank) (fun _ => 0) u.val := by
    intro i hi
    apply (RationalAccumulator.zero_word_iff_blank _ _).mpr
    apply z0
    rw [←List.mem_toFinset,hcset]
    exact Finset.mem_union_right ({0,1,2,3}:Finset ℕ) hi
  have scratch : NatAssign.Scratch u.val := by
    intro i hi
    apply z0
    rw [←List.mem_toFinset,hcset]
    apply Finset.mem_union_left
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  obtain ⟨c1,t,e1,hc1,bt,zt,ft⟩ := NatAssign.executes (RationalDataflow.ids RowArithmetic.bank) (RationalDataflow.ids_ge _)
    plan plan_valid (fun _ => 0) input tape u bank scratch
  have price := NatAssign.price_bound (RationalDataflow.ids RowArithmetic.bank) plan plan_valid (fun _ => 0) 1
    (by simp) (by
      intro a ha
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
      change (1:ℕ).bits.length≤1
      decide)
  have hprice : c1≤2^112 := hc1.trans (price.trans (by
    norm_num [plan,denominators]))
  have frame : BinaryPrecision.Frame (workspace RowArithmetic.bank) s.val t.val := by
    rw [hcset] at f0
    exact f0.trans (ft.mono (changes_subset RowArithmetic.bank plan plan_valid))
  refine ⟨c0+c1,t,e0.seq e1,?_,⟨?_,zt⟩,frame⟩
  · have hlen : clearPorts.length≤256 := by
      rw [clearPorts,Finset.length_sort]
      decide
    have hclear : c0≤256*(6*B+4)+1 := hc0.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) _)
    have hx : B+1≤(B+1)^2 := Nat.le_self_pow (by decide) _
    nlinarith only [hclear,hprice,hx,Nat.zero_le B]
  · intro i hi
    rw [←plan_values i hi]
    exact bt i hi

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ZeroInitialization
