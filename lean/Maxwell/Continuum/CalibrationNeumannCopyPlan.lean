import Maxwell.Continuum.CalibrationNeumannCopyTarget

/-! Fixed descriptor arithmetic for the copy of the converted table.  The
denominator is copied from its computed rational register, not supplied as
a new numerical input. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.CopyPlan

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Word)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def plan : List NatAssign.Instruction :=
  [.copy 300 305,.multiply 300 305,
   .copy 305 306,.add 300 306,.add 300 306,
   .copy 306 307,.multiply 301 307,
   .copy 301 210,.copy 302 212,.add 307 212,.add 307 212,.add 307 212,
   .copy 212 213,.add 307 213,.copy 213 214,.add 307 214,
   .copy 1000 303]

def code : Code := NatAssign.code plan
def ids : Finset ℕ := insert 1000 Descriptors.ids

structure Inputs (v : ℕ → ℕ) (n width heap D N : ℕ) : Prop where
  dimension : v 300 = n
  width : v 301 = width
  heap : v 302 = heap
  computedDenominator : v 1000 = D
  iterations : v 304 = N

structure Header (n width heap D : ℕ) (s : BitRAMState) : Prop where
  widthWord : Word s 210 width
  positive : Word s 212 (heap+3*tableSize n*width)
  negative : Word s 213 (heap+4*tableSize n*width)
  denominator : Word s 214 (heap+5*tableSize n*width)
  computedDenominator : Word s 303 D

theorem valid : ∀ a ∈ plan, a.Valid ids := by
  simp [plan,NatAssign.Instruction.Valid,ids,Descriptors.ids]

theorem outputs (v : ℕ → ℕ) (n width heap D N : ℕ)
    (hi : Inputs v n width heap D N) :
    Descriptors.Inputs (NatAssign.values plan v) n width heap D N := by
  constructor <;>
    simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,hi.dimension,hi.width,hi.heap,hi.computedDenominator,hi.iterations]

theorem header_of_bank (v : ℕ → ℕ) (n width heap D N : ℕ)
    (hi : Inputs v n width heap D N) (s : BitRAMState)
    (hb : NatAssign.Bank ids (NatAssign.values plan v) s) : Header n width heap D s := by
  have wordEq (i x : ℕ) (hx : NatAssign.values plan v i=x) (h : i∈ids) : Word s i x :=
    hx ▸ hb i h
  constructor <;> apply wordEq _ _ ?_ (by simp [ids,Descriptors.ids]) <;>
    simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,hi.dimension,hi.width,hi.heap,hi.computedDenominator,
      tableSize] <;> ring

theorem executes (v : ℕ → ℕ) (n width heap D N B : ℕ)
    (hi : Inputs v n width heap D N) (hw : ∀ i ∈ ids, (v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ 3000*8^plan.length*(B+2)^2 ∧
      NatAssign.Bank ids (NatAssign.values plan v) t.val ∧ Header n width heap D t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (NatAssign.changes plan) s.val t.val := by
  have hid : ∀ i ∈ ids, 4 ≤ i := by
    intro i hi
    simp only [ids,Descriptors.ids,Finset.mem_insert,Finset.mem_union,Finset.mem_Icc,
      Finset.mem_singleton] at hi
    omega
  have hl : ∀ a ∈ plan, a.literalWidth ≤ B := by
    simp [plan,NatAssign.Instruction.literalWidth]
  obtain ⟨cost,t,he,hc,ht,hz,hf⟩ := NatAssign.executes ids hid plan valid v input tape s hb hs
  exact ⟨cost,t,he,hc.trans (NatAssign.price_bound ids plan valid v B hw hl),ht,
    header_of_bank v n width heap D N hi t.val ht,hz,hf⟩

#print axioms executes

end Maxwell.Continuum.Calibration.NeumannMachine.CopyPlan
