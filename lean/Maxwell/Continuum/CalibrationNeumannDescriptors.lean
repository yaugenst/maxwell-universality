import Maxwell.Continuum.CalibrationNeumannLayout
import Maxwell.Cost.Structured.NatAssign.Bounds

/-! Fixed executed descriptor arithmetic for the literal padded coefficient
table, its copy, and the inverse workspace. Every address is computed from
runtime dimension, width, and heap words. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.Descriptors

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Word)
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

def spanPlan : List NatAssign.Instruction :=
  [.copy 300 305,.multiply 300 305,
   .copy 305 306,.add 300 306,.add 300 306,
   .copy 306 307,.multiply 301 307,
   .copy 300 308,.multiply 301 308,
   .copy 305 309,.add 300 309,.multiply 301 309,
   .copy 302 310,.add 307 310,.add 307 310,.add 307 310,
   .add 307 310,.add 307 310,.add 307 310]

def basesPlan : List NatAssign.Instruction :=
  [.copy 302 120,.copy 302 121,.add 307 121,
   .copy 302 122,.add 309 122,.copy 121 123,.add 309 123,
   .copy 302 110,.add 308 110,.copy 121 111,.add 308 111,
   .copy 302 130,.add 307 130,.add 307 130,.add 307 130,
   .copy 130 131,.add 307 131,
   .copy 310 124,.add 308 310,.copy 310 125,.add 308 310,
   .copy 310 128,.add 308 310,.copy 310 129,.add 308 310,
   .copy 310 132,.add 308 310,.copy 310 133,.add 308 310]

def headerPlan : List NatAssign.Instruction :=
  [.copy 301 100,.copy 300 107,.copy 303 126,.literal 127 1,.copy 304 140,
   .copy 130 112,.copy 131 113,.copy 125 114,.copy 124 115,
   .copy 301 200,.copy 302 202,.copy 121 203,
   .copy 121 204,.add 307 204,
   .copy 301 210,.copy 130 212,.copy 131 213,.copy 131 214,.add 307 214,
   .literal 30 0,.literal 31 0,.literal 32 0,.literal 33 0,.literal 34 0,.literal 35 0,.literal 36 0,
   .literal 102 0,.literal 103 0,.literal 104 0,.literal 106 0,.literal 108 0,.literal 109 0]

def plan : List NatAssign.Instruction := spanPlan++basesPlan++headerPlan
def code : Code := NatAssign.code plan

def ids : Finset ℕ := Finset.Icc 30 36 ∪ Finset.Icc 100 140 ∪ {200,202,203,204,210,212,213,214} ∪ Finset.Icc 300 310

structure Inputs (v : ℕ→ℕ) (n width heap D N : ℕ) : Prop where
  dimension : v 300=n
  width : v 301=width
  heap : v 302=heap
  denominator : v 303=D
  iterations : v 304=N

structure Header (n width heap D N : ℕ) (s : BitRAMState) : Prop where
  widthWord : Word s 100 width
  dimension : Word s 107 n
  denominator : Word s 126 D
  numerator : Word s 127 1
  iterations : Word s 140 N
  matrixPositive : Word s 110 (heap+n*width)
  matrixNegative : Word s 111 (heap+(tableSize n+n)*width)
  bases : ∀ i : Fin 12, Word s (Horner.baseBank i) (heap+vectorOffset n (n*n) i*width)
  inputPositive : Word s 112 (heap+3*tableSize n*width)
  inputNegative : Word s 113 (heap+4*tableSize n*width)
  outputPositive : Word s 114 (heap+(6*tableSize n+n)*width)
  outputNegative : Word s 115 (heap+6*tableSize n*width)
  inputWidth : Word s 200 width
  inputTablePositive : Word s 202 heap
  inputTableNegative : Word s 203 (heap+tableSize n*width)
  inputTableDenominator : Word s 204 (heap+2*tableSize n*width)
  outputWidth : Word s 210 width
  outputTablePositive : Word s 212 (heap+3*tableSize n*width)
  outputTableNegative : Word s 213 (heap+4*tableSize n*width)
  outputTableDenominator : Word s 214 (heap+5*tableSize n*width)
  accumulators : ∀ i, 30 ≤ i → i ≤ 36 → Word s i 0
  cursors : ∀ i∈([102,103,104,106,108,109]:List ℕ), Word s i 0

private theorem valid : ∀ a∈plan, a.Valid ids := by
  simp [plan,spanPlan,basesPlan,headerPlan,NatAssign.Instruction.Valid,ids]

theorem header_of_bank (v : ℕ→ℕ) (n width heap D N : ℕ)
    (hi : Inputs v n width heap D N) (s : BitRAMState)
    (hb : NatAssign.Bank ids (NatAssign.values plan v) s) : Header n width heap D N s := by
  have wordEq (i x : ℕ) (hx : NatAssign.values plan v i=x) (h : i∈ids) : Word s i x :=
    hx ▸ hb i h
  constructor
  case bases =>
    intro i
    apply wordEq _ _ ?_ (by
      have hi := Horner.baseBank_bounds i
      simp only [ids,Finset.mem_union,Finset.mem_Icc]
      omega)
    fin_cases i <;>
      simp [plan,spanPlan,basesPlan,headerPlan,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value,hi.dimension,hi.width,hi.heap,
        hi.denominator,hi.iterations,Horner.baseBank,vectorOffset] <;> ring
  case accumulators =>
    intro i h30 h36
    interval_cases i <;> apply wordEq _ _ ?_ (by simp [ids]) <;>
      simp [plan,spanPlan,basesPlan,headerPlan,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value]
  case cursors =>
    intro i hi'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi'
    rcases hi' with rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply wordEq _ _ ?_ (by simp [ids]) <;>
      simp [plan,spanPlan,basesPlan,headerPlan,NatAssign.values,NatAssign.Instruction.update,
        NatAssign.Instruction.target,NatAssign.Instruction.value]
  all_goals
    apply wordEq _ _ ?_ (by simp [ids])
    simp [plan,spanPlan,basesPlan,headerPlan,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,hi.dimension,hi.width,hi.heap,
      hi.denominator,hi.iterations,tableSize] <;> ring

theorem executes (v : ℕ→ℕ) (n width heap D N B : ℕ) (hB : 0<B)
    (hi : Inputs v n width heap D N) (hw : ∀ i∈ids, (v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost≤3000*8^plan.length*(B+2)^2 ∧
      Header n width heap D N t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (NatAssign.changes plan) s.val t.val := by
  have hid : ∀ i ∈ ids, 4 ≤ i := by
    intro i hi
    simp only [ids,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have hl : ∀ a∈plan, a.literalWidth≤B := by
    simp [plan,spanPlan,basesPlan,headerPlan,NatAssign.Instruction.literalWidth]
    exact hB
  obtain ⟨cost,t,he,hcost,hbank,hsc,hframe⟩ := NatAssign.executes ids hid plan valid v input tape s hb hs
  exact ⟨cost,t,he,hcost.trans (NatAssign.price_bound ids plan valid v B hw hl),
    header_of_bank v n width heap D N hi t.val hbank,hsc,hframe⟩

#print axioms header_of_bank
#print axioms executes

end Maxwell.Continuum.Calibration.NeumannMachine.Descriptors
