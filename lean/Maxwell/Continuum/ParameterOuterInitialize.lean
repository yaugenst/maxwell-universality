import Maxwell.Continuum.ParameterOuterRetained

namespace Maxwell.Continuum.Parameters.OuterMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
open RationalAccumulator (Blank Word)
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem initialize_executes (v : ℕ→ℕ) (B : ℕ) (hℓ : 0<v 2200)
    (hw : ∀i∈ids,(v i).bits.length ≤ B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : ∀i,i<5→Blank s.val i) :
    ∃cost t,Executes input tape initializeCode cost s t ∧ cost ≤ initializeCost v B ∧
      Ready (dataOf v) (initialExponent (v 2201) (v 2200)) (initialWidth v B) t ∧
      BinaryPrecision.Frame workspace s.val t.val ∧ Word t.val 2200 (v 2200) := by
  have sub : OuterInitial.ids⊆ids := by decide +kernel
  obtain ⟨ci,a,ei,pi,bi,si,wi,_,fi⟩ := OuterInitial.executes v B hℓ (fun i hi=>hw i (sub hi))
    input tape s (fun i hi=>hb i (sub hi)) (fun i hi=>hs i (by omega))
  have ba : NatAssign.Bank ids (seedValues v) a.val := hb.overlay bi (by decide +kernel)
    (show BinaryPrecision.Frame (OuterInitial.ids∪{0,1,2,3,4}) s.val a.val from fi.mono (by decide +kernel))
  have sa : ∀i,i<5→Blank a.val i := by
    intro i hi
    by_cases h4 : i<4
    · exact si i h4
    · have he : i=4 := by omega
      subst i;exact RationalAccumulator.blank_of_eq (fi.tapes 4 (by decide +kernel)) (hs 4 (by decide))
  have wa : ∀i∈ids,(seedValues v i).bits.length ≤ seedWidth v B := by
    intro i hi
    exact (NatAssign.overlay_width hw wi i hi).trans (Nat.le_add_right _ _)
  have hseed : 4 ≤ seedWidth v B := by unfold seedWidth;omega
  obtain ⟨cp,p,ep,pp,bp,sp,fp⟩ := NatAssign.executes_scratch 5 (by decide) ids
    (fun i hi=>by have := ids_ge i hi;omega) powerSetup powerSetup_valid (seedValues v) input tape a ba sa
  have plit : ∀x∈powerSetup,x.AssignmentBound (seedWidth v B) := by
    simp only [powerSetup,List.mem_cons,List.not_mem_nil,or_false]
    intro x hx
    rcases hx with rfl|rfl|rfl
    · change 2 ≤ seedWidth v B;omega
    · change 4 ≤ seedWidth v B;exact hseed
    · trivial
  have wp : ∀i∈ids,(powerInputs v i).bits.length ≤ seedWidth v B :=
    NatAssign.values_assignment_width ids powerSetup powerSetup_valid (seedValues v) _ wa plit
  obtain ⟨pa,pb,pn⟩ := powerInputs_fields v
  let N := initialExponent (v 2201) (v 2200)
  have hn : N.bits.length ≤ seedWidth v B := by simpa only [pn] using wp 534 (by decide +kernel)
  have dpSub : DynamicPower.ids⊆ids := by decide +kernel
  have pexec := PowerMachine.executes (powerInputs v) N (seedWidth v B) (by omega)
    (fun i hi=>wp i (dpSub hi)) hn input tape p (fun i hi=>bp i (dpSub hi))
    (fun i hi=>sp i (by omega)) (by
      have hh : Word p.val 534 (powerInputs v 534) := bp 534 (by decide +kernel)
      simpa only [pn] using hh)
  rw [pa,pb] at pexec
  obtain ⟨cq,q,eq,pq,bq,zq,fq⟩ := pexec
  have qb : NatAssign.Bank powerIds (powerResult N) q.val := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · have hne : i≠534 := by simp only [DynamicPower.ids,Finset.mem_insert,Finset.mem_singleton] at hi;omega
      simpa only [powerResult,Function.update_of_ne hne] using bq.bank i hi
    · have he : i=534 := by simpa using hi
      subst i
      simpa only [powerResult,Function.update_self] using (RationalAccumulator.zero_word_iff_blank _ _).mpr zq
  have bq' : NatAssign.Bank ids (poweredValues v) q.val := bp.overlay qb (by decide +kernel)
    (show BinaryPrecision.Frame (powerIds∪{0,1,2,3,4}) p.val q.val from fq.mono (by decide +kernel))
  have sq : ∀i,i<5→Blank q.val i := by
    intro i hi
    by_cases h4 : i<4
    · exact bq.scratch i h4
    · have he : i=4 := by omega
      subst i;exact RationalAccumulator.blank_of_eq (fq.tapes 4 (by decide +kernel)) (sp 4 (by decide))
  have qw : ∀i∈powerIds,(powerResult N i).bits.length ≤ DynamicPower.width N (seedWidth v B) := by
    intro i _
    by_cases hi : i=534
    · subst i;simp [powerResult]
    · simp only [powerResult,Function.update_of_ne hi]
      exact DynamicPower.values_width 2 8 N N (seedWidth v B) le_rfl
        (by change 2 ≤ seedWidth v B;omega) (by change 4 ≤ seedWidth v B;omega) i
  have wq : ∀i∈ids,(poweredValues v i).bits.length ≤ initialWidth v B := by
    intro i hi
    exact (NatAssign.overlay_width wp qw i hi).trans (Nat.le_add_right _ _)
  obtain ⟨cf,t,ef,pf,bf,sf,ff⟩ := NatAssign.executes_scratch 5 (by decide) ids
    (fun i hi=>by have := ids_ge i hi;omega) finishSetup finishSetup_valid (poweredValues v) input tape q bq' sq
  have hfinal : 1025 ≤ initialWidth v B := by unfold initialWidth;omega
  have flit : ∀x∈finishSetup,x.AssignmentBound (initialWidth v B) := by
    have hd : slowDivisor.bits.length=1025 := by rw [slowDivisor,Nat.size_eq_bits_len,Nat.size_pow]
    simp only [finishSetup,List.mem_cons,List.not_mem_nil,or_false]
    intro x hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · trivial
    · trivial
    · change 1 ≤ initialWidth v B;omega
    · change 2 ≤ initialWidth v B;omega
    · change 4 ≤ initialWidth v B;omega
    · change 3 ≤ initialWidth v B;omega
    · change slowDivisor.bits.length ≤ initialWidth v B;rw [hd];exact hfinal
  have wf := NatAssign.values_assignment_width ids finishSetup finishSetup_valid (poweredValues v)
    (initialWidth v B) wq flit
  have ppb := NatAssign.price_bound ids powerSetup powerSetup_valid (seedValues v) (seedWidth v B) wa
    (by
      have h2 : (2:ℕ).bits.length=2 := rfl
      have h8 : (8:ℕ).bits.length=4 := rfl
      simp [powerSetup,NatAssign.Instruction.literalWidth,h2,h8];omega)
  have pfb := NatAssign.price_bound ids finishSetup finishSetup_valid (poweredValues v) (initialWidth v B) wq
    (by
      have hd : slowDivisor.bits.length=1025 := by rw [slowDivisor,Nat.size_eq_bits_len,Nat.size_pow]
      have h2 : (2:ℕ).bits.length=2 := rfl
      have h4 : (4:ℕ).bits.length=3 := rfl
      have h8 : (8:ℕ).bits.length=4 := rfl
      simp [finishSetup,NatAssign.Instruction.literalWidth,hd,h2,h4,h8];omega)
  have log : Word t.val 2200 (v 2200) := by
    have h := bf 2200 (by decide +kernel)
    change Word t.val 2200 (initializedValues v 2200) at h
    simpa only [initialized_log] using h
  exact ⟨ci+(cp+(cq+cf)),t,ei.seq (ep.seq (eq.seq ef)),
    Nat.add_le_add pi (Nat.add_le_add (pp.trans ppb) (Nat.add_le_add pq (pf.trans pfb))),
    ⟨initializedValues v,bf,sf,wf,initialized_core v⟩,
    (fi.mono (by decide +kernel)).trans ((fp.mono (by decide +kernel)).trans
      ((fq.mono (by decide +kernel)).trans (ff.mono (by decide +kernel)))),log⟩

#print axioms initialize_executes
end Maxwell.Continuum.Parameters.OuterMachine
