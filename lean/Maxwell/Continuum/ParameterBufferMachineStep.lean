import Maxwell.Continuum.ParameterBufferMachineState
import Maxwell.Cost.Structured.NatAssign.BinaryPower

namespace Maxwell.Continuum.Parameters.BufferMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
open RationalAccumulator (Blank Word)
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
attribute [local irreducible] values width

def stepCode : Code := .seq (NatAssign.code advance)
  (.seq (RationalDataflow.NaturalQuotient.code 2115 2116 2118)
    (.seq (RoutingPorts.powerCode 2118 2119 2117) (NatAssign.code formulas)))
def arithmeticCost (xs : List NatAssign.Instruction) (W : ℕ) : ℕ := 3000*8^xs.length*(W+2)^2
def powerCost (T W : ℕ) : ℕ := (T+1)*(13*W+25)+21*W+27
def stepCost (N B : ℕ) : ℕ := arithmeticCost advance (width N B)+
  (2^100*(width N B+2)^2+(powerCost (2^N) (width N B)+arithmeticCost formulas (width N B)))

theorem advance_ids_valid : ∀a∈advance,a.Valid ids := by
  intro a ha
  have h := advance_valid a ha
  cases a <;> simp only [NatAssign.Instruction.Valid] at h ⊢
  all_goals simp_all [ids,Compare.ids]

theorem beforeQuotient_width (D : Data) (k N B : ℕ) (hk : k ≤ N) (hD : D.Width B) (i : ℕ) :
    (beforeQuotient D k i).bits.length ≤ width N B := by
  unfold beforeQuotient
  by_cases h17 : i=2117
  · subst i;simp
  by_cases h18 : i=2118
  · subst i;simp
  simpa only [Function.update_of_ne h17,Function.update_of_ne h18] using
    extra_inputs_width D k N B hk hD i

theorem step_executes (D : Data) (k N B : ℕ) (hk : k+1 ≤ N) (hD : D.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready D k (width N B) s) :
    ∃cost t,Executes input tape stepCode cost s t ∧ cost ≤ stepCost N B ∧
      Ready D (k+1) (width N B) t ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨v,hb,hsc,hv,hw,h35,h36⟩ := hs
  obtain ⟨ca,a,ea,pa,ba,sa,fa⟩ := NatAssign.executes ids (fun i hi=>by have := ids_ge i hi;omega)
    advance advance_ids_valid v input tape s hb (fun i hi=>hsc i (by omega))
  have pac := NatAssign.price_bound ids advance advance_ids_valid v (width N B) hw
    (by simp [advance,resetInstructions,resetTargets,List.range_succ,NatAssign.Instruction.literalWidth])
  have fa' := fa.mono (show NatAssign.changes advance⊆{0,1,2,3}∪ids by decide +kernel)
  let va := NatAssign.values advance v
  have ae : ∀i∈extra,va i=beforeQuotient D (k+1) i := advance_values D k v hv
  have ao (i : ℕ) (hi : i∉extra) : va i=v i := NatAssign.values_outside extra advance advance_valid v i hi
  have aw : ∀i∈ids,(va i).bits.length ≤ width N B := by
    intro i hi
    by_cases he : i∈extra
    · rw [ae i he];exact beforeQuotient_width D (k+1) N B hk hD i
    · rw [ao i he];exact hw i hi
  have az : ∀i∈RationalDataflow.NaturalQuotient.workPorts,va i=0 := by
    intro i hi
    simp only [RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> rw [ae _ (by decide +kernel)] <;> simp [beforeQuotient,inputs]
  have av15 : va 2115=2^(k+1) := by simpa [beforeQuotient,inputs] using ae 2115 (by decide +kernel)
  have av16 : va 2116=slowDivisor := by simpa [beforeQuotient,inputs] using ae 2116 (by decide +kernel)
  obtain ⟨cq,q,eq,pq,bq,sq,fq⟩ := RationalDataflow.NaturalQuotient.executes ids ids_ge
    (by decide +kernel) 2115 2116 2118 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) va az (by rw [av16];unfold slowDivisor;positivity)
    (width N B) aw input tape a ba (fifth_scratch fa' hsc sa)
  let vq := Function.update va 2118 (va 2115/va 2116)
  have qe : ∀i∈extra,vq i=Function.update (inputs D (k+1)) 2117 0 i := quotient_values D (k+1) va ae
  have qo (i : ℕ) (hi : i∉extra) : vq i=v i := by
    have hn : i≠2118 := by intro h;subst i;exact hi (by decide +kernel)
    exact (Function.update_of_ne hn _ _).trans (ao i hi)
  have qw : ∀i∈ids,(vq i).bits.length ≤ width N B := by
    intro i hi
    by_cases he : i∈extra
    · rw [qe i he]
      by_cases h17 : i=2117
      · subst i;simp
      · simpa only [Function.update_of_ne h17] using extra_inputs_width D (k+1) N B hk hD i
    · rw [qo i he];exact hw i hi
  have q17 : vq 2117=0 := by simpa using qe 2117 (by decide +kernel)
  have q19 : vq 2119=0 := by simpa [inputs] using qe 2119 (by decide +kernel)
  have q18 : vq 2118=(2^(k+1))/slowDivisor := by simpa [inputs] using qe 2118 (by decide +kernel)
  obtain ⟨cp,p,ep,pp,bp,fp⟩ := NatAssign.binaryPower ids 2118 2119 2117
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide)
    vq q19 q17 input tape q bq
  let vp := Function.update vq 2117 (2^(vq 2118))
  have pe : ∀i∈extra,vp i=inputs D (k+1) i := power_values D (k+1) vq qe
  have po (i : ℕ) (hi : i∉extra) : vp i=v i := by
    have hn : i≠2117 := by intro h;subst i;exact hi (by decide +kernel)
    exact (Function.update_of_ne hn _ _).trans (qo i hi)
  have pw : ∀i∈ids,(vp i).bits.length ≤ width N B := by
    intro i hi
    by_cases he : i∈extra
    · rw [pe i he];exact extra_inputs_width D (k+1) N B hk hD i
    · rw [po i he];exact hw i hi
  have psc : ∀i,i<5→Blank p.val i := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (fp.tapes i (by simp;omega)) (sq i hi)
  have pbound : cp ≤ powerCost (2^N) (width N B) := by
    have hn : vq 2118 ≤ 2^N := by
      rw [q18]
      exact (Nat.div_le_self _ _).trans (Nat.pow_le_pow_right (by decide) hk)
    have hqbits := qw 2118 (by decide +kernel)
    exact pp.trans (by unfold powerCost;gcongr)
  obtain ⟨cf,t,ef,pf,bt,st,ft⟩ := NatAssign.executes ids (fun i hi=>by have := ids_ge i hi;omega)
    formulas formulas_valid vp input tape p bp (fun i hi=>psc i (by omega))
  have pfc := NatAssign.price_bound ids formulas formulas_valid vp (width N B) pw (formulas_literals _)
  have ft' := ft.mono (show NatAssign.changes formulas⊆{0,1,2,3}∪ids by decide +kernel)
  let w := NatAssign.values formulas vp
  have we : ∀i∈extra,w i=values D (k+1) i := by
    simpa only [w,values] using NatAssign.values_congr extra formulas formulas_extra_valid vp _ pe
  have wo (i : ℕ) (hi : i∉extra) : w i=v i :=
    (NatAssign.values_outside extra formulas formulas_extra_valid vp i hi).trans (po i hi)
  refine ⟨ca+(cq+(cp+cf)),t,ea.seq (eq.seq (ep.seq ef)),?_,
    ⟨w,bt,fifth_scratch ft' psc st,we,?_,(wo 35 (by decide +kernel)).trans h35,
      (wo 36 (by decide +kernel)).trans h36⟩,
    (nat_frame fa').trans ((quotient_frame fq).trans ((fp.mono (by decide +kernel)).trans (nat_frame ft')))⟩
  · exact Nat.add_le_add (pa.trans pac) (Nat.add_le_add pq (Nat.add_le_add pbound (pf.trans pfc)))
  · intro i hi
    by_cases he : i∈extra
    · rw [we i he];exact values_width D (k+1) N B hk hD i hi
    · rw [wo i he];exact hw i hi

#print axioms step_executes
end Maxwell.Continuum.Parameters.BufferMachine
