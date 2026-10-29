import Maxwell.Cost.CalibrationMatrix.Allocation.Code
import Maxwell.Cost.Structured.WordAssign

namespace Maxwell.Cost.CalibrationMatrix.Allocation.Install
open Structured
open RationalAccumulator (Word)
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-- Preserve radius, radix and dimension before replacing the generator's
low metadata with inverse, pairing and sparse-source descriptors. -/
def assignments : List WordAssign.Assignment :=
  [(120,277),(121,276),(122,266),(266,107),
   (230,120),(231,121),(232,122),(233,123),(234,124),(235,125),
   (264,126),(265,127),(236,128),(237,129),(240,130),(241,131),(238,132),(239,133),
   (242,154),(243,155),(244,160),(245,161),(246,162),(263,140),(263,274),(267,159)]

def ids : List ℕ := assignments.flatMap (fun a => [a.1,a.2])
def code : Code := WordAssign.code assignments

structure Values (words : ℕ → List Bool) (heap R n width capacity K S N count : ℕ) : Prop where
  radius : words 120 = R.bits
  radix : words 121 = (2*R+1).bits
  dimension : words 122 = n.bits
  dense : ∀ i : Fin 14, words (230+i.val) = (heap+denseBase n width i.val).bits
  sparse : ∀ i : Fin 3, words (244+i.val) = (heap+sparseBase n width capacity i.val).bits
  K : words 264 = K.bits
  S : words 265 = S.bits
  degree : words 263 = N.bits
  count : words 267 = count.bits

structure Header (heap R n width capacity K S N count : ℕ) (s : BitRAMState) : Prop where
  bases : ∀ i : Fin 12, Word s (Horner.baseBank i) (heap+denseBase n width i.val)
  K : Word s 126 K
  S : Word s 127 S
  dimension : Word s 107 n
  degree : Word s 140 N
  count : Word s 159 count
  positiveRow : Word s 154 (heap+denseBase n width 12)
  negativeRow : Word s 155 (heap+denseBase n width 13)
  sparse : ∀ i : Fin 3, Word s (160+i.val) (heap+sparseBase n width capacity i.val)
  savedDimension : Word s 266 n
  savedRadix : Word s 276 (2*R+1)
  savedRadius : Word s 277 R
  savedDegree : Word s 274 N

theorem header_of_bank (words : ℕ → List Bool) (heap R n width capacity K S N count : ℕ)
    (hv : Values words heap R n width capacity K S N count) (s : BitRAMState)
    (hb : WordAssign.Bank ids s (WordAssign.values assignments words)) :
    Header heap R n width capacity K S N count s := by
  have d12 : words 242 = (heap+denseBase n width 12).bits := by simpa using hv.dense 12
  have d13 : words 243 = (heap+denseBase n width 13).bits := by simpa using hv.dense 13
  constructor
  · intro i
    have hi : Horner.baseBank i ∈ ids := by fin_cases i <;> decide
    have hh := hb (Horner.baseBank i) hi
    have hd := hv.dense ⟨i.val,by omega⟩
    fin_cases i <;> norm_num at hd <;> simpa [assignments,WordAssign.values,Horner.baseBank,hd,Word,BankArray.Word] using hh
  · simpa [assignments,WordAssign.values,hv.K,Word,BankArray.Word] using hb 126 (by decide)
  · simpa [assignments,WordAssign.values,hv.S,Word,BankArray.Word] using hb 127 (by decide)
  · simpa [assignments,WordAssign.values,hv.dimension,Word,BankArray.Word] using hb 107 (by decide)
  · simpa [assignments,WordAssign.values,hv.degree,Word,BankArray.Word] using hb 140 (by decide)
  · simpa [assignments,WordAssign.values,hv.count,Word,BankArray.Word] using hb 159 (by decide)
  · simpa [assignments,WordAssign.values,d12,Word,BankArray.Word] using hb 154 (by decide)
  · simpa [assignments,WordAssign.values,d13,Word,BankArray.Word] using hb 155 (by decide)
  · intro i
    have hi : 160+i.val ∈ ids := by fin_cases i <;> decide
    have hh := hb (160+i.val) hi
    have hd := hv.sparse i
    fin_cases i <;> norm_num at hd <;> simpa [assignments,WordAssign.values,hd,Word,BankArray.Word] using hh
  · simpa [assignments,WordAssign.values,hv.dimension,Word,BankArray.Word] using hb 266 (by decide)
  · simpa [assignments,WordAssign.values,hv.radix,Word,BankArray.Word] using hb 276 (by decide)
  · simpa [assignments,WordAssign.values,hv.radius,Word,BankArray.Word] using hb 277 (by decide)
  · simpa [assignments,WordAssign.values,hv.degree,Word,BankArray.Word] using hb 274 (by decide)

/-- The installed metadata are obtained by physical clearing and copying;
the matrix and all coefficient arrays retain their exact memory contents. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (words : ℕ → List Bool)
    (heap R n width capacity K S N count B : ℕ) (hv : Values words heap R n width capacity K S N count)
    (hl : ∀ i ∈ ids, (words i).length ≤ B) (s : Store) (hb : WordAssign.Bank ids s.val words) :
    ∃ t : Store, Executes input tape code (WordAssign.price assignments words) s t ∧
      WordAssign.price assignments words ≤ 546*B+547 ∧
      Header heap R n width capacity K S N count t.val ∧ WordAssign.Frame assignments s.val t.val := by
  have valid : WordAssign.Valid ids assignments := by
    simp [WordAssign.Valid,assignments,ids]
  obtain ⟨t,he,ht,hf⟩ := WordAssign.executes assignments ids input tape words valid s hb
  refine ⟨t,he,?_,header_of_bank words heap R n width capacity K S N count hv t.val ht,hf⟩
  have hprice := WordAssign.price_bound assignments ids words B valid hl
  simp only [assignments,List.length_cons,List.length_nil] at hprice
  simp only [assignments]
  omega

end Maxwell.Cost.CalibrationMatrix.Allocation.Install
