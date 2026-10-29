import Maxwell.Cost.CalibrationMatrix.EntryDecode
import Maxwell.Green.CalibrationTests

namespace Maxwell.Cost.CalibrationMatrix.Entry
open Structured RationalAccumulator
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice

def coordinateValues (x y z : List Bool) : Direction → ℕ :=
  ![addressValue x,addressValue y,addressValue z]

/-- Semantic form of the reusable decoder, allowing arbitrary high padding
in the stored index and radix words. -/
theorem decode_coordinates (indexBank base : ℕ) (hib : 100 ≤ indexBank) (hbase : 100 ≤ base)
    (input : List Bool) (tape : ℕ → Bool) (R : ℕ) (i : Fin (3*cubeWidth R^3))
    (radix index : List Bool) (hrvalue : addressValue radix = cubeWidth R)
    (hivalue : addressValue index = i.val) (s : Store)
    (hr : BankArray.Word s.val 121 radix) (hi : BankArray.Word s.val indexBank index)
    (hblank : ∀ k, k < 5 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ (base ≤ k ∧ k < base+4) → Blank s.val k) :
    ∃ cost t x y z direction,
      cost ≤ 2000*(radix.length+index.length+3)^2 ∧
      Executes input tape (decodeCode 121 indexBank base) cost s t ∧
      BankArray.Word t.val base direction ∧ BankArray.Word t.val (base+1) x ∧
      BankArray.Word t.val (base+2) y ∧ BankArray.Word t.val (base+3) z ∧
      addressValue direction = (radixCubeEmbedding R i).1.val ∧
      unsignedEdge R (radixCubeEmbedding R i).1 (coordinateValues x y z) = radixCubeEmbedding R i ∧
      direction.length = index.length ∧
      x.length ≤ radix.length+index.length ∧ y.length ≤ radix.length+index.length ∧
      z.length ≤ radix.length+index.length ∧
      (∀ k, k < 5 ∨ k = 70 ∨ k = 71 ∨ k = 72 → Blank t.val k) ∧
      BinaryPrecision.Frame (decodeChanges base) s.val t.val := by
  have hrpos : 0 < addressValue radix := by rw [hrvalue]; unfold cubeWidth; omega
  obtain ⟨cost,t,x,y,z,d,hcost,he,hd,hx,hy,hz,hdv,hxv,hyv,hzv,hdl,hxl,hyl,hzl,hb,hf⟩ :=
    decode_digits 121 indexBank base (by decide) hib hbase input tape radix index hrpos s hr hi hblank
  rw [hrvalue,hivalue] at hdv hxv hyv hzv
  have hc := radix_coordinates R i
  refine ⟨cost,t,x,y,z,d,hcost,he,hd,hx,hy,hz,hdv.trans hc.1.symm,?_,hdl,hxl,hyl,hzl,hb,hf⟩
  apply Prod.ext
  · rfl
  funext j
  fin_cases j
  · change (addressValue x : ℤ)-R = (radixEdge R i).2 0
    rw [hxv]
    exact hc.2.1.symm
  · change (addressValue y : ℤ)-R = (radixEdge R i).2 1
    rw [hyv]
    exact hc.2.2.1.symm
  · change (addressValue z : ℤ)-R = (radixEdge R i).2 2
    rw [hzv]
    exact hc.2.2.2.symm

end Maxwell.Cost.CalibrationMatrix.Entry
