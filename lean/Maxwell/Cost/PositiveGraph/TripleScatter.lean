import Maxwell.Cost.PositiveGraph.Frame
import Maxwell.Cost.IncidenceEncoding

namespace Maxwell.Cost.PositiveGraph.TripleScatter
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1600000

def flaggedCode (indexBank : ℕ) (mediator : Bool) : Code :=
  .seq (Code.atom (.literal 47 mediator)) (DiagonalUpdate.code indexBank)

def code : Code := .seq (flaggedCode 111 false)
  (.seq (flaggedCode 122 false) (flaggedCode 121 true))

def write (base : ℕ) (row column mediator : ℕ) (rv cv mv : ℕ)
    (negative half : Bool) (memory : ℕ → Bool) : ℕ → Bool :=
  MemoryWord.writeBits (MemoryWord.writeBits (MemoryWord.writeBits memory
    (base+4*row) (DiagonalUpdate.payload rv negative half false))
    (base+4*column) (DiagonalUpdate.payload cv negative half false))
    (base+4*mediator) (DiagonalUpdate.payload mv negative half true)

def updated {n : ℕ} (words : Vector (List Bool) n) (row column mediator : Fin n)
    (rv cv mv : ℕ) (negative half : Bool) : Vector (List Bool) n :=
  ((words.set row (DiagonalUpdate.payload rv negative half false)).set column
    (DiagonalUpdate.payload cv negative half false)).set mediator
    (DiagonalUpdate.payload mv negative half true)

def costCap (row column mediator clock : List Bool) (base rv cv mv : ℕ)
    (negative half : Bool) : ℕ :=
  DiagonalUpdate.costCap row base clock rv negative half false+
  DiagonalUpdate.costCap column base clock cv negative half false+
  DiagonalUpdate.costCap mediator base clock mv negative half true+6

private theorem get_set_ne {n : ℕ} (words : Vector (List Bool) n)
    (i j : Fin n) (value : List Bool) (hne : i ≠ j) :
    (words.set i value).get j = words.get j := by
  change (words.set i.val value)[j.val] = words[j.val]
  exact Vector.getElem_set_ne i.isLt j.isLt (fun h => hne (Fin.ext h))

private theorem flagged {n : ℕ} (indexBank : ℕ) (hbank : 10 ≤ indexBank)
    (hbank120 : indexBank ≠ 120) (input : List Bool) (tape : ℕ → Bool)
    (index clock : List Bool) (base value : ℕ) (words : Vector (List Bool) n) (i : Fin n)
    (hindex : addressValue index = i.val) (hclock : clock.length = 4) (hvalue : value < 16)
    (hword : words.get i = FixedWidth.bits 4 value.bits) (negative half mediator : Bool)
    (s : Store) (hscratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h120 : Blank s.val 120)
    (h147 : BankArray.Word s.val 147 (4 : ℕ).bits) (hindexWord : BankArray.Word s.val indexBank index)
    (h145 : BankArray.Word s.val 145 base.bits) (h148 : BankArray.Word s.val 148 clock)
    (harray : BitArray.Represents s.val.memory base 4 words)
    (hnegative : s.val.registers 44 = negative) (hhalf : s.val.registers 45 = half) :
    ∃ steps, ∃ t : Store,
      steps ≤ DiagonalUpdate.costCap index base clock value negative half mediator+2 ∧
      Executes input tape (flaggedCode indexBank mediator) steps s t ∧
      t.val.memory = MemoryWord.writeBits s.val.memory (base+4*i.val)
        (DiagonalUpdate.payload value negative half mediator) ∧
      BitArray.Represents t.val.memory base 4
        (words.set i (DiagonalUpdate.payload value negative half mediator)) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 120 ∧
      t.val.registers 44 = negative ∧ t.val.registers 45 = half ∧
      t.val.registers 47 = mediator ∧ PositiveGraph.Frame {120} s.val t.val := by
  let a := Store.ofState (s.val.setRegister 47 mediator)
  have af : PositiveGraph.Frame {120} s.val a.val := by
    constructor <;> intros <;> simp_all [a,Store.ofState,BitRAMState.setRegister]
  obtain ⟨steps,t,hc,he,hm,ha,hs,h7,h120,hn,hh,hmed,hf⟩ :=
    DiagonalUpdate.executes indexBank hbank hbank120 input tape index clock base value words i
      hindex hclock hvalue hword negative half mediator a hscratch h7 h120 h147 hindexWord
      h145 h148 harray
      (by simpa [a,Store.ofState,BitRAMState.setRegister] using hnegative)
      (by simpa [a,Store.ofState,BitRAMState.setRegister] using hhalf)
      (by simp [a,Store.ofState,BitRAMState.setRegister])
  exact ⟨2+steps,t,by omega,(Executes.literal input tape s 47 mediator).seq he,
    hm,ha,hs,h7,h120,hn,hh,hmed,af.trans (PositiveGraph.Frame.of_diagonal hf)⟩

/-- The row, column, and mediator each receive one actual indexed four-bit
update. The literal role flag is charged before every update. -/
theorem executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (row column mediator clock : List Bool) (base rv cv mv : ℕ)
    (words : Vector (List Bool) n) (r c m : Fin n)
    (hr : addressValue row = r.val) (hc : addressValue column = c.val)
    (hm : addressValue mediator = m.val) (hrc : r ≠ c) (hrm : r ≠ m) (hcm : c ≠ m)
    (hclock : clock.length = 4) (hrv : rv < 16) (hcv : cv < 16) (hmv : mv < 16)
    (hrow : words.get r = FixedWidth.bits 4 rv.bits)
    (hcolumn : words.get c = FixedWidth.bits 4 cv.bits)
    (hmediator : words.get m = FixedWidth.bits 4 mv.bits) (negative half : Bool)
    (s : Store) (hscratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h120 : Blank s.val 120)
    (h147 : BankArray.Word s.val 147 (4 : ℕ).bits) (h145 : BankArray.Word s.val 145 base.bits)
    (h148 : BankArray.Word s.val 148 clock) (h111 : BankArray.Word s.val 111 row)
    (h122 : BankArray.Word s.val 122 column) (h121 : BankArray.Word s.val 121 mediator)
    (harray : BitArray.Represents s.val.memory base 4 words)
    (hnegative : s.val.registers 44 = negative) (hhalf : s.val.registers 45 = half) :
    ∃ steps, ∃ t : Store, steps ≤ costCap row column mediator clock base rv cv mv negative half ∧
      Executes input tape code steps s t ∧
      t.val.memory = write base r.val c.val m.val rv cv mv negative half s.val.memory ∧
      BitArray.Represents t.val.memory base 4 (updated words r c m rv cv mv negative half) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 120 ∧
      t.val.registers 44 = negative ∧ t.val.registers 45 = half ∧ t.val.registers 47 = true ∧
      PositiveGraph.Frame {120} s.val t.val := by
  obtain ⟨ac,a,hac,ea,am,aa,ascratch,a7,a120,an,ah,_arole,af⟩ :=
    flagged 111 (by decide) (by decide) input tape row clock base rv words r hr hclock hrv
      hrow negative half false s hscratch h7 h120 h147 h111 h145 h148 harray hnegative hhalf
  have keepA (j : ℕ) (hj : 10 ≤ j) (hne : j ≠ 120) : a.val.tapes j = s.val.tapes j :=
    af.tapes j (Or.inr hj) (by simpa using hne)
  obtain ⟨bc,b,hbc,eb,bm,ba,bscratch,b7,b120,bn,bh,_brole,bf⟩ :=
    flagged 122 (by decide) (by decide) input tape column clock base cv
      (words.set r (DiagonalUpdate.payload rv negative half false)) c hc hclock hcv
      (by rw [get_set_ne _ _ _ _ hrc]; exact hcolumn) negative half false a ascratch a7 a120
      (BankArray.word_of_eq (keepA 147 (by decide) (by decide)) h147)
      (BankArray.word_of_eq (keepA 122 (by decide) (by decide)) h122)
      (BankArray.word_of_eq (keepA 145 (by decide) (by decide)) h145)
      (BankArray.word_of_eq (keepA 148 (by decide) (by decide)) h148) aa an ah
  have abf := af.trans bf
  have keepB (j : ℕ) (hj : 10 ≤ j) (hne : j ≠ 120) : b.val.tapes j = s.val.tapes j :=
    abf.tapes j (Or.inr hj) (by simpa using hne)
  obtain ⟨mc,t,hmc,et,tm,ta,tscratch,t7,t120,tn,th,trole,tf⟩ :=
    flagged 121 (by decide) (by decide) input tape mediator clock base mv
      ((words.set r (DiagonalUpdate.payload rv negative half false)).set c
        (DiagonalUpdate.payload cv negative half false)) m hm hclock hmv
      (by rw [get_set_ne _ _ _ _ hcm,get_set_ne _ _ _ _ hrm]; exact hmediator)
      negative half true b bscratch b7 b120
      (BankArray.word_of_eq (keepB 147 (by decide) (by decide)) h147)
      (BankArray.word_of_eq (keepB 121 (by decide) (by decide)) h121)
      (BankArray.word_of_eq (keepB 145 (by decide) (by decide)) h145)
      (BankArray.word_of_eq (keepB 148 (by decide) (by decide)) h148) ba bn bh
  refine ⟨ac+(bc+mc),t,by dsimp [costCap]; omega,ea.seq (eb.seq et),?_,ta,
    tscratch,t7,t120,tn,th,trole,abf.trans tf⟩
  rw [tm,bm,am]
  rfl

/-- The explicit writes preserve any array separated from the diagonal. -/
theorem write_preserves {n k : ℕ} {memory : ℕ → Bool} {base otherBase width : ℕ}
    {words : Vector (List Bool) k} (h : BitArray.Represents memory otherBase width words)
    (row column mediator : Fin n) (rv cv mv : ℕ) (negative half : Bool)
    (hsep : IncidenceEncoding.Separated otherBase (k*width) base (n*4)) :
    BitArray.Represents (write base row.val column.val mediator.val rv cv mv negative half memory)
      otherBase width words := by
  have a := IncidenceEncoding.represents_write_disjoint h base 4 row
    (DiagonalUpdate.payload rv negative half false)
    (by simp [DiagonalUpdate.payload,FixedWidth.bits_length]) hsep
  have b := IncidenceEncoding.represents_write_disjoint a base 4 column
    (DiagonalUpdate.payload cv negative half false)
    (by simp [DiagonalUpdate.payload,FixedWidth.bits_length]) hsep
  have c := IncidenceEncoding.represents_write_disjoint b base 4 mediator
    (DiagonalUpdate.payload mv negative half true)
    (by simp [DiagonalUpdate.payload,FixedWidth.bits_length]) hsep
  simpa only [write,Nat.mul_comm] using c

end Maxwell.Cost.PositiveGraph.TripleScatter
