import Maxwell.Cost.DecoderConstants.Add
import Maxwell.Cost.PowerOfTwo

namespace Maxwell.Cost.DecoderConstants
open Structured
open RationalAccumulator (Word Blank)

theorem cloneStored (source target : ℕ) (hs : 4 ≤ source) (ht : 4 ≤ target) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (n : ℕ) (s : Store)
    (hw : Word s.val source n) (hb : Blank s.val target) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.clone source target)) (15*n.bits.length+17) s t ∧
      Word t.val target n ∧ StoredProduct.Frame target s.val t.val ∧
      (∀ i, i < 4 → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨so,hso⟩ := hw
  obtain ⟨dest,hdest⟩ := hb
  obtain ⟨t,he,hp,hs',ht',hf⟩ := WordTransfer.clone_steps source target hne input tape n.bits so dest s.val
    s.property hso hdest
  refine ⟨Store.ofState t,?_,⟨dest,ht'⟩,?_,?_⟩
  · simpa using Executes.call _ _ _ _ he (by rw [hp]; rfl)
  · rcases hf with ⟨a,b,c,d,e,f,g⟩
    refine ⟨a,b,c,d,e,?_,fun i _ h24 h25 h26 h27 => g i h24 h25 h26 h27⟩
    intro i _ htarget
    by_cases hsource : i = source
    · subst i; exact hs'.trans hso.symm
    · exact f i hsource htarget
  · intro i hi
    exact hf.2.2.2.2.2.1 i (by omega) (by omega)

-- Only the destination word changes; the value one is emitted by two primitive instructions.
def oneProgram (target : ℕ) : BitRAM := ⟨[.literal 26 true,.writeTape target 26,.halt]⟩
def oneState (target : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 2
    registers := Function.update s.registers 26 true
    tapes := Function.update s.tapes target ((s.tapes target).write (some true))}

theorem one (target : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : Blank s.val target) :
    Executes input tape (.call (oneProgram target)) 3 s (Store.ofState (oneState target s.val)) ∧
      Word (oneState target s.val) target 1 ∧ StoredProduct.Frame target s.val (oneState target s.val) := by
  obtain ⟨origin,ho⟩ := hb
  refine ⟨?_,⟨origin,?_⟩,?_⟩
  · have he : PricedSteps ((oneProgram target).next input tape) 2 s.val (oneState target s.val) := by
      apply executeInstructions_sound (instructions := 2)
      simp [executeInstructions,BitRAM.next,oneProgram,s.property,oneState,BitRAMState.setRegister,BitRAMState.setTape]
    exact .call _ _ _ _ he rfl
  · simp only [oneState,Function.update_self,ho]
    apply BitTape.ext
    · rfl
    · funext k
      by_cases hk : k = origin
      · subst k; simp [BitTape.write,BitTape.blank,BitTape.shifted,Nat.bits]
      · by_cases hle : origin ≤ k
        · have hgt : origin < k := by omega
          simp [BitTape.write,BitTape.blank,BitTape.shifted,Nat.bits,hk,hle,hgt]
        · simp [BitTape.write,BitTape.blank,BitTape.shifted,Nat.bits,hk,hle]
  · simp [StoredProduct.Frame,oneState]
    simp_all

theorem clearStored (target : ℕ) (htarget : 4 ≤ target) (input : List Bool) (tape : ℕ → Bool) (n : ℕ) (s : Store)
    (hw : Word s.val target n) :
    ∃ t : Store, Executes input tape (.call (TapeOps.clear target)) (6*n.bits.length+4) s t ∧
      Blank t.val target ∧ StoredProduct.Frame target s.val t.val ∧
      (∀ i, i < 4 → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨origin,ho⟩ := hw
  obtain ⟨t,he,hp,ht,hf⟩ := TapeOps.clear_steps target input tape n.bits origin s.val s.property ho
  refine ⟨Store.ofState t,?_,⟨origin+n.bits.length,ht⟩,
    StoredProduct.frame_of_copy (Or.inl rfl) (Or.inl rfl) hf,
    fun i hi => hf.2.2.2.2.2.1 i (by omega) (by omega)⟩
  simpa using Executes.call _ _ _ _ he (by rw [hp]; rfl)

def powerCode (source target : ℕ) : Code :=
  .seq (PowerOfTwo.code source 68 target) (.call (Rewind.program target))

theorem power (source target : ℕ) (hs : source ≠ 68) (ht : target ≠ 68) (hst : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (n : ℕ) (s : Store)
    (hw : Word s.val source n) (hb : Blank s.val target) (hc : Blank s.val 68) :
    ∃ cost, ∃ t : Store, cost ≤ (n+1)*(13*n.bits.length+25)+21*n.bits.length+27 ∧
      Executes input tape (powerCode source target) cost s t ∧
      Word t.val target (2^n) ∧ Blank t.val 68 ∧ PowerOfTwo.BankFrame 68 target s t := by
  obtain ⟨so,hso⟩ := hw
  obtain ⟨dest,hdest⟩ := hb
  obtain ⟨co,hco⟩ := hc
  obtain ⟨pcost,p,ep,hpcost,hps,hpc,hpt,pf⟩ := PowerOfTwo.executes source 68 target hs hst (Ne.symm ht)
    input tape n.bits so co dest s hso hco hdest
  simp only [RationalAccumulator.address_bits] at hpcost hpt
  have hr := WordTransfer.rewind_shifted target dest input tape (2^n).bits p.val p.property hpt
  let r := Rewind.finishAt target dest p.val
  let rS := Store.ofState r
  have er : Executes input tape (.call (Rewind.program target)) (4*(2^n).bits.length+6) p rS := .call _ _ _ _ hr.1 rfl
  have rf : PowerOfTwo.BankFrame 68 target p rS := by
    have h := WordTransfer.frame_rewind 68 target target (Or.inr rfl) dest p.val
    rcases h with ⟨a,b,c,d,e,f,g⟩
    exact ⟨a,b,c,d,e,f,fun i _ h24 h25 h26 h27 _ _ => g i h24 h25 h26 h27⟩
  refine ⟨_,rS,?_,ep.seq er,⟨dest,hr.2⟩,⟨co+n.bits.length,?_⟩,pf.trans rf⟩
  · have hlen : (2^n).bits.length = n+1 := by simp [PowerOfTwo.power_bits]
    rw [hlen]
    nlinarith
  · simpa [rS,Store.ofState,r,Rewind.finishAt,Ne.symm ht] using hpc

end Maxwell.Cost.DecoderConstants
