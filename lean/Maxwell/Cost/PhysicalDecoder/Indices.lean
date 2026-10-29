import Maxwell.Cost.Structured.NatAssign.Bounds
import Maxwell.Composition.SourcePhysicalDecoderRecords

namespace Maxwell.Cost.PhysicalDecoder.Indices
open Structured RationalAccumulator

def ids : Finset ℕ := {302,344,345,359,503}
def initial (row dimension : ℕ) (i : ℕ) : ℕ :=
  if i=344 then row else if i=503 then dimension else 0
def statements (localSize : ℕ) : List NatAssign.Instruction :=
  [.literal 359 localSize,.copy 344 345,.multiply 359 345,
    .copy 503 302,.add 344 302,.literal 359 0]
def code (localSize : ℕ) : Code := NatAssign.code (statements localSize)
def work : Finset ℕ := {0,1,2,3,302,345,359}
def costBound (B : ℕ) : ℕ := 3000*8^6*(B+2)^2

theorem valid (k : ℕ) : ∀ a ∈ statements k,a.Valid ids := by
  simp [statements,NatAssign.Instruction.Valid,ids]

theorem changes (k : ℕ) : NatAssign.changes (statements k)=work := by
  ext i
  simp [statements,NatAssign.changes,NatAssign.Instruction.target,work]
  tauto

set_option maxRecDepth 8192 in
theorem executes (localSize row dimension B : ℕ)
    (hk : localSize.bits.length ≤ B) (hi : row.bits.length ≤ B) (hd : dimension.bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hrow : Word s.val 344 row) (hdim : Word s.val 503 dimension)
    (h302 : Blank s.val 302) (h345 : Blank s.val 345) (h359 : Blank s.val 359)
    (hr : NatAssign.Scratch s.val) :
    ∃ cost t, cost ≤ costBound B ∧ Executes input tape (code localSize) cost s t ∧
      Word t.val 302 (dimension+row) ∧ Word t.val 345 (localSize*row) ∧
      Blank t.val 359 ∧ NatAssign.Scratch t.val ∧ BinaryPrecision.Frame work s.val t.val := by
  have hb : NatAssign.Bank ids (initial row dimension) s.val := by
    intro j hj
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl
    · exact (zero_word_iff_blank _ _).mpr h302
    · exact hrow
    · exact (zero_word_iff_blank _ _).mpr h345
    · exact (zero_word_iff_blank _ _).mpr h359
    · exact hdim
  obtain ⟨c,t,et,hc,tb,tr,tf⟩ := NatAssign.executes ids (by decide) (statements localSize)
    (valid localSize) (initial row dimension) input tape s hb hr
  have hb' : ∀ j ∈ ids,(initial row dimension j).bits.length ≤ B := by
    intro j _
    simp only [initial]
    split_ifs <;> simp_all
  have hc' : NatAssign.price (statements localSize) (initial row dimension) ≤ costBound B := by
    simpa [statements,costBound] using NatAssign.price_bound ids (statements localSize)
      (valid localSize) (initial row dimension) B hb'
      (by intro a ha; simp only [statements,List.mem_cons,List.not_mem_nil,or_false] at ha
          rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
          · exact hk
          all_goals simp [NatAssign.Instruction.literalWidth])
  refine ⟨c,t,hc.trans hc',et,?_,?_,?_,tr,changes localSize ▸ tf⟩
  · simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial,Nat.add_comm] using tb 302 (by decide)
  · simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,initial] using tb 345 (by decide)
  · apply (zero_word_iff_blank _ _).mp
    simpa [statements,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target] using tb 359 (by decide)

end Maxwell.Cost.PhysicalDecoder.Indices
