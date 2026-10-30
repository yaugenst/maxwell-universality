import Maxwell.Cost.SelectedParameters.DynamicPowerValues

namespace Maxwell.Continuum.Parameters.PowerMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open Maxwell.Cost.SelectedParameters.DynamicPower

private def bodyWorkspace : Finset ℕ := {0,1,2,3,532,533}

def bodyCost (B : ℕ) : ℕ := 3000*8^2*(B+2)^2
def loopCode : Code := CountedShifted.code 534 (NatAssign.code SelectedParameters.DynamicPower.advance)
def code : Code := .seq (NatAssign.code initialization)
  (.seq loopCode (.call (TapeOps.clear 534)))

def costBound (N B : ℕ) : ℕ := bodyCost B+
  ((N+1)*(13*B+15)+N*bodyCost (width N B)+(6*B+4))

theorem next (a b n N B : ℕ) (hn : n ≤ N)
    (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready a b n s) :
    ∃ cost t, Executes input tape (NatAssign.code SelectedParameters.DynamicPower.advance) cost s t ∧
      cost ≤ bodyCost (width N B) ∧ Ready a b (n+1) t ∧
      BinaryPrecision.Frame bodyWorkspace s.val t.val := by
  obtain ⟨cost,t,he,hc,bt,st,ft⟩ := NatAssign.executes ids ids_ge SelectedParameters.DynamicPower.advance advance_valid
    (values a b n) input tape s hs.bank hs.scratch
  have hp := NatAssign.price_bound ids SelectedParameters.DynamicPower.advance advance_valid (values a b n) (width N B)
    (fun i _ => values_width a b n N B hn ha hb i)
    (by simp [SelectedParameters.DynamicPower.advance,NatAssign.Instruction.literalWidth])
  refine ⟨cost,t,he,hc.trans hp,⟨?_,st⟩,ft.mono (by decide)⟩
  simpa only [advance_values] using bt

def Invariant (a b N : ℕ) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ N ∧ Ready a b (N-remaining) s ∧ BinaryPrecision.Frame workspace initial s.val

theorem loop (a b N B : ℕ) (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool)
    (hcount : addressValue count=N) (hlen : count.length ≤ B) (origin : ℤ)
    (s : Store) (hc : s.val.tapes 534=BitTape.shifted count origin)
    (hs : Ready a b 0 s) :
    ∃ cost t finalWord, Executes input tape loopCode cost s t ∧
      cost ≤ (N+1)*(13*B+15)+N*bodyCost (width N B) ∧ Ready a b N t ∧
      t.val.tapes 534=BitTape.shifted finalWord origin ∧ finalWord.length=count.length ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  let inv := Invariant a b N s.val
  have stable : ∀ n u t, CountedShifted.Frame 534 u t → inv n u → inv n t := by
    intro n u t hf hu
    exact ⟨hu.1,hu.2.1.stable hf,hu.2.2.trans (counter_frame hf)⟩
  have body : ∀ n xs u, inv (n+1) u → u.val.tapes 534=BitTape.shifted xs origin →
      addressValue xs=n → ∃ cost t, Executes input tape (NatAssign.code SelectedParameters.DynamicPower.advance) cost u t ∧
      inv n t ∧ t.val.tapes 534=BitTape.shifted xs origin ∧ cost ≤ bodyCost (width N B) := by
    intro n xs u hu hc _
    have hn : n+1 ≤ N := hu.1
    obtain ⟨cost,t,he,hcost,ht,hf⟩ := next a b (N-(n+1)) N B (by omega)
      ha hb input tape u hu.2.1
    have heq : N-(n+1)+1=N-n := by omega
    refine ⟨cost,t,he,⟨by omega,heq ▸ ht,hu.2.2.trans (hf.mono (by decide))⟩,?_,hcost⟩
    exact (hf.tapes 534 (by decide)).trans hc
  have hi : inv N s := ⟨le_rfl,by simpa using hs,BinaryPrecision.Frame.refl _ _⟩
  obtain ⟨cost,t,finalWord,he,ht,hw,hl,_,hp⟩ := CountedShifted.executes 534 origin
    (NatAssign.code SelectedParameters.DynamicPower.advance) input tape inv (fun _ => bodyCost (width N B))
    stable body N count s hcount hc hi
  refine ⟨cost,t,finalWord,he,?_,by simpa using ht.2.1,hw,hl,ht.2.2⟩
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hp
  exact hp.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _)

/-- A fixed counted program raises both stored rational operands to the
stored exponent. The exponent changes the execution count, not the code. -/
theorem executes (v : ℕ → ℕ) (N B : ℕ) (hB : 1 ≤ B)
    (hw : ∀ i ∈ ids, (v i).bits.length ≤ B) (hN : N.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hsc : NatAssign.Scratch s.val)
    (hn : Word s.val 534 N) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ costBound N B ∧
      Ready (v 530) (v 531) N t ∧ Blank t.val 534 ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cc,u,ec,pc,bc,sc,fc⟩ := NatAssign.executes ids ids_ge initialization
    initialization_valid v input tape s hs hsc
  have pci := NatAssign.price_bound ids initialization initialization_valid v B hw
    (by simp [initialization,NatAssign.Instruction.literalWidth,hB])
  have pc' : cc ≤ bodyCost B := pc.trans pci
  have hu : Ready (v 530) (v 531) 0 u := by
    refine ⟨?_,sc⟩
    intro i hi
    simpa only [initialization_values v i hi] using bc i hi
  have fcu : BinaryPrecision.Frame workspace s.val u.val := fc.mono (by decide)
  obtain ⟨origin,hno⟩ := hn
  have hnu : u.val.tapes 534=BitTape.shifted N.bits origin :=
    (fc.tapes 534 (by decide)).trans hno
  obtain ⟨lc,a,last,el,pl,ha,hl,hlen,fl⟩ := loop (v 530) (v 531) N B
    (hw 530 (by decide)) (hw 531 (by decide)) input tape N.bits (by simp) hN origin u hnu hu
  obtain ⟨t,et,ht,ft⟩ := WordCall.clear 534 input tape last origin a hl
  have keep (i : ℕ) (hi : i≠534) : t.val.tapes i=a.val.tapes i := by simp [ht,hi]
  have frame : BinaryPrecision.Frame workspace a.val t.val := by
    refine ⟨ft.1,ft.2.1,ft.2.2.1,ft.2.2.2.1,ft.2.2.2.2.1,?_⟩
    intro i hi
    exact keep i (by simp only [workspace,Finset.mem_insert,Finset.mem_singleton,not_or] at hi; omega)
  refine ⟨cc+(lc+(6*last.length+4)),t,ec.seq (el.seq et),?_,⟨?_,?_⟩,
    ⟨origin+last.length,by simp [ht]⟩,fcu.trans (fl.trans frame)⟩
  · have hlen' : last.length ≤ B := hlen.trans_le hN
    exact Nat.add_le_add pc' (Nat.add_le_add pl (by omega))
  · intro i hi
    exact word_of_eq (keep i (by simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega))
      (ha.bank i hi)
  · intro i hi
    exact blank_of_eq (keep i (by omega)) (ha.scratch i hi)

#print axioms executes

end Maxwell.Continuum.Parameters.PowerMachine
