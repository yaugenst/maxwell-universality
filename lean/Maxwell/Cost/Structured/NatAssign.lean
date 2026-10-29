import Maxwell.Cost.Structured.WordAssign
import Maxwell.Cost.BinaryPrecision

namespace Maxwell.Cost.Structured.NatAssign
open RationalAccumulator (Word Blank word_of_eq blank_of_eq)

inductive Instruction where
  | literal (target value : ℕ)
  | copy (source target : ℕ)
  | add (source target : ℕ)
  | multiply (source target : ℕ)
  deriving DecidableEq

def Instruction.target : Instruction → ℕ
  | .literal target _ | .copy _ target | .add _ target | .multiply _ target => target

def Instruction.value : Instruction → (ℕ → ℕ) → ℕ
  | .literal _ n, _ => n
  | .copy source _, v => v source
  | .add source target, v => v source+v target
  | .multiply source target, v => v source*v target

def Instruction.update (a : Instruction) (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update v a.target (a.value v)

def Instruction.code : Instruction → Code
  | .literal target n => .seq (.call (TapeOps.clear target)) (BinaryPrecision.literalCode target n)
  | .copy source target => WordReplace.code source target
  | .add source target => DecoderConstants.addCode source target
  | .multiply source target => DecoderTerm.multiplyCode source target

def Instruction.price : Instruction → (ℕ → ℕ) → ℕ
  | .literal target n, v => 6*(v target).bits.length+10*n.bits.length+11
  | .copy source target, v => 6*(v target).bits.length+15*(v source).bits.length+21
  | .add source target, v => 200*((v source).bits.length+(v target).bits.length+4)
  | .multiply source target, v => 600*((v source).bits.length+(v target).bits.length+3)^2

def Instruction.Valid (ids : Finset ℕ) : Instruction → Prop
  | .literal target _ => target ∈ ids
  | .copy source target | .add source target | .multiply source target =>
      source ∈ ids ∧ target ∈ ids ∧ source ≠ target

def Bank (ids : Finset ℕ) (v : ℕ → ℕ) (s : BitRAMState) : Prop :=
  ∀ i ∈ ids, Word s i (v i)

def Scratch (s : BitRAMState) : Prop := ∀ i, i < 4 → Blank s i

def changed (target : ℕ) : Finset ℕ := {0,1,2,3,target}

theorem stored_frame {target : ℕ} {s t : BitRAMState}
    (h : StoredProduct.Frame target s t) : BinaryPrecision.Frame (changed target) s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  intro i hi
  simp only [changed,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  exact h.2.2.2.2.2.1 i (by omega) hi.2.2.2.2

theorem updated_bank (ids : Finset ℕ) (v : ℕ → ℕ) (a : Instruction)
    (s t : BitRAMState) (hids : ∀ i ∈ ids, 4 ≤ i) (hb : Bank ids v s)
    (hw : Word t a.target (a.value v))
    (hf : BinaryPrecision.Frame (changed a.target) s t) : Bank ids (a.update v) t := by
  intro i hi
  by_cases he : i=a.target
  · subst i
    simpa [Instruction.update] using hw
  · have ht : i ∉ changed a.target := by simp only [changed,Finset.mem_insert,Finset.mem_singleton]; have := hids i hi; omega
    simpa only [Instruction.update,Function.update_of_ne he] using word_of_eq (hf.tapes i ht) (hb i hi)

theorem instruction_executes (ids : Finset ℕ) (hids : ∀ i ∈ ids, 4 ≤ i)
    (a : Instruction) (hv : a.Valid ids) (v : ℕ → ℕ)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : Bank ids v s.val) (hs : Scratch s.val) :
    ∃ cost t, Executes input tape a.code cost s t ∧ cost ≤ a.price v ∧
      Bank ids (a.update v) t.val ∧ Scratch t.val ∧
      BinaryPrecision.Frame (changed a.target) s.val t.val := by
  cases a with
  | literal target n =>
    obtain ⟨a,ea,ha,fa,ka⟩ := DecoderConstants.clearStored target (hids target hv) input tape (v target) s (hb target hv)
    obtain ⟨t,et,ht,ft⟩ := BinaryPrecision.literal target n input tape a ha
    have frame : BinaryPrecision.Frame (changed target) s.val t.val :=
      (stored_frame fa).trans (ft.mono (by simp [changed]))
    refine ⟨_,t,ea.seq et,by dsimp [Instruction.price]; omega,
      updated_bank ids v (.literal target n) s.val t.val hids hb ht frame,?_,frame⟩
    intro i hi
    have hne : i ≠ target := by have := hids target hv; omega
    exact blank_of_eq ((ft.tapes i (by simpa using hne)).trans (ka i hi)) (hs i hi)
  | copy source target =>
    obtain ⟨hsource,htarget,hne⟩ := hv
    obtain ⟨t,he,ht,hf⟩ := WordReplace.executes source target hne input tape (v source).bits
      (v target).bits s (hb source hsource) (hb target htarget)
    have frame : BinaryPrecision.Frame (changed target) s.val t.val := by
      refine ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
      intro i hi
      exact hf.2.2.2.2.2.1 i (by simp_all [changed])
    refine ⟨_,t,he,le_rfl,updated_bank ids v (.copy source target) s.val t.val hids hb ht frame,?_,frame⟩
    intro i hi
    exact blank_of_eq (hf.2.2.2.2.2.1 i (by have := hids target htarget; omega)) (hs i hi)
  | add source target =>
    obtain ⟨hsource,htarget,hne⟩ := hv
    obtain ⟨cost,t,hcost,he,ht,hs',hf⟩ := DecoderConstants.add source target (hids source hsource)
      (hids target htarget) hne input tape (v source) (v target) s (hb source hsource) (hb target htarget) hs
    exact ⟨cost,t,he,hcost,updated_bank ids v (.add source target) s.val t.val hids hb ht (stored_frame hf),hs',stored_frame hf⟩
  | multiply source target =>
    obtain ⟨hsource,htarget,hne⟩ := hv
    obtain ⟨cost,t,hcost,he,ht,hs',hf⟩ := DecoderTerm.multiply source target (hids source hsource)
      (hids target htarget) hne input tape (v source) (v target) s (hb source hsource) (hb target htarget) hs
    exact ⟨cost,t,he,hcost,updated_bank ids v (.multiply source target) s.val t.val hids hb ht (stored_frame hf),hs',stored_frame hf⟩

def code : List Instruction → Code
  | [] => .skip
  | a::rest => .seq a.code (code rest)

def values : List Instruction → (ℕ → ℕ) → (ℕ → ℕ)
  | [], v => v
  | a::rest, v => values rest (a.update v)

def price : List Instruction → (ℕ → ℕ) → ℕ
  | [], _ => 1
  | a::rest, v => a.price v+price rest (a.update v)

def changes (instructions : List Instruction) : Finset ℕ :=
  {0,1,2,3} ∪ (instructions.map Instruction.target).toFinset

theorem executes (ids : Finset ℕ) (hids : ∀ i ∈ ids, 4 ≤ i)
    (instructions : List Instruction) (hv : ∀ a ∈ instructions, a.Valid ids)
    (v : ℕ → ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : Bank ids v s.val) (hs : Scratch s.val) :
    ∃ cost t, Executes input tape (code instructions) cost s t ∧ cost ≤ price instructions v ∧
      Bank ids (values instructions v) t.val ∧ Scratch t.val ∧
      BinaryPrecision.Frame (changes instructions) s.val t.val := by
  induction instructions generalizing v s with
  | nil => exact ⟨1,s,.skip s,le_rfl,hb,hs,BinaryPrecision.Frame.refl _ _⟩
  | cons a rest ih =>
    obtain ⟨acost,u,eu,hu,bu,su,fu⟩ := instruction_executes ids hids a (hv a (by simp)) v input tape s hb hs
    obtain ⟨cost,t,et,ht,bt,st,ft⟩ := ih (fun a ha => hv a (by simp [ha])) (a.update v) u bu su
    exact ⟨acost+cost,t,eu.seq et,Nat.add_le_add hu ht,bt,st,
      (fu.mono (by
        intro i hi
        simp only [changed,changes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
          List.map_cons,List.toFinset_cons] at hi ⊢
        tauto)).trans
        (ft.mono (by
          intro i hi
          simp only [changes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
            List.map_cons,List.toFinset_cons] at hi ⊢
          tauto))⟩

end Maxwell.Cost.Structured.NatAssign
