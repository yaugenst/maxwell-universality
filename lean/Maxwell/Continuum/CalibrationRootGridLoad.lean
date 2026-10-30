import Maxwell.Continuum.CalibrationRootGridCenterMachine
import Maxwell.Continuum.CalibrationRootGridMachine

/-! The four sample arguments are copied from the executed grid decoder,
not supplied as a rational sample table. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def loadFirst (n : ℕ→ℕ) (v : ℕ→Parts) := Function.update v 0 (FractionWord.part (n 333) (n 331))
def loadSecond (n : ℕ→ℕ) (v : ℕ→Parts) := Function.update (loadFirst n v) 1 (FractionWord.part (n 334) (n 331))
def loadThird (n : ℕ→ℕ) (v : ℕ→Parts) := Function.update (loadSecond n v) 2 (FractionWord.part (n 335) (n 331))
def loadParts (n : ℕ→ℕ) (v : ℕ→Parts) := Function.update (loadThird n v) 5 (FractionWord.part (n 341) (n 331))
def loadCode : Code := .seq (FractionWord.code 333 331 0)
  (.seq (FractionWord.code 334 331 1) (.seq (FractionWord.code 335 331 2) (FractionWord.code 341 331 5)))

theorem part_width (n : ℕ→ℕ) (a B : ℕ) (ha : (n a).bits.length≤B) (hb : (n 331).bits.length≤B) :
    (FractionWord.part (n a) (n 331)).Width B := ⟨ha,by simp [FractionWord.part],hb⟩

theorem loadParts_good (S : Finset ℕ) (n : ℕ→ℕ) (v : ℕ→Parts)
    (hg : Good S v) (hn : 0<n 331) : Good S (loadParts n v) :=
  (((hg.update 0 (show (FractionWord.part (n 333) (n 331)).Valid from hn)).update 1
    (show (FractionWord.part (n 334) (n 331)).Valid from hn)).update 2
      (show (FractionWord.part (n 335) (n 331)).Valid from hn)).update 5
        (show (FractionWord.part (n 341) (n 331)).Valid from hn)

theorem loadParts_width (S : Finset ℕ) (n : ℕ→ℕ) (v : ℕ→Parts) (W : ℕ)
    (hw : WidthBank S W v) (hn : ∀i∈ids,(n i).bits.length≤W) :
    WidthBank S W (loadParts n v) :=
  (((hw.update 0 (part_width n 333 W (hn 333 (by decide)) (hn 331 (by decide)))).update 1
    (part_width n 334 W (hn 334 (by decide)) (hn 331 (by decide)))).update 2
      (part_width n 335 W (hn 335 (by decide)) (hn 331 (by decide)))).update 5
        (part_width n 341 W (hn 341 (by decide)) (hn 331 (by decide)))

theorem loadParts_coordinate (n : ℕ→ℕ) (v : ℕ→Parts) (i : Fin 3) :
    loadParts n v i=FractionWord.part (![n 333,n 334,n 335] i) (n 331) := by
  fin_cases i <;> simp [loadParts,loadThird,loadSecond,loadFirst]

theorem loadParts_phase (n : ℕ→ℕ) (v : ℕ→Parts) :
    loadParts n v 5=FractionWord.part (n 341) (n 331) := by simp [loadParts]

theorem loadParts_other (n : ℕ→ℕ) (v : ℕ→Parts) (i : ℕ) (hi : i≠0 ∧ i≠1 ∧ i≠2 ∧ i≠5) :
    loadParts n v i=v i := by simp [loadParts,loadThird,loadSecond,loadFirst,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]

theorem load_executes (S : Finset ℕ) (hS : RootGridCenter.inputs⊆S) (n : ℕ→ℕ) (v : ℕ→Parts)
    (W : ℕ) (hW : 1≤W) (hw : WidthBank S W v) (hn : ∀i∈ids,(n i).bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s)
    (hb : NatAssign.Bank ids n s.val) :
    ∃cost t,Executes input tape loadCode cost s t ∧ cost≤2^105*(W+3)^2 ∧
      Ready S (loadParts n v) t ∧ BinaryPrecision.Frame (RationalDataflow.workspace S) s.val t.val := by
  have hp (i : ℕ) (hi : i∈RootGridCenter.inputs) : i∈S := hS hi
  have w331 := hn 331 (by decide)
  obtain ⟨c0,s0,e0,h0,b0,f0⟩ := FractionWord.executes S 333 331 0 (by omega) (by omega)
    (hp 0 (by decide)) (n 333) (n 331) W v hw hW (hn 333 (by decide)) w331
    input tape s hs (hb 333 (by decide)) (hb 331 (by decide))
  have bnat0 (i : ℕ) (hi : i∈Finset.Icc 330 341) : Word s0.val i (n i) := by
    have bound := Finset.mem_Icc.mp hi
    exact word_of_eq (f0.tapes i (FractionWord.outside S i (by omega))) (hb i (Finset.mem_union_right _ hi))
  have w0 := hw.update 0 (part_width n 333 W (hn 333 (by decide)) w331)
  obtain ⟨c1,s1,e1,h1,b1,f1⟩ := FractionWord.executes S 334 331 1 (by omega) (by omega)
    (hp 1 (by decide)) (n 334) (n 331) W (loadFirst n v) w0 hW (hn 334 (by decide)) w331
    input tape s0 b0 (bnat0 334 (by decide)) (bnat0 331 (by decide))
  have bnat1 (i : ℕ) (hi : i∈Finset.Icc 330 341) : Word s1.val i (n i) := by
    have bound := Finset.mem_Icc.mp hi
    exact word_of_eq (f1.tapes i (FractionWord.outside S i (by omega))) (bnat0 i hi)
  have w1 := w0.update 1 (part_width n 334 W (hn 334 (by decide)) w331)
  obtain ⟨c2,s2,e2,h2,b2,f2⟩ := FractionWord.executes S 335 331 2 (by omega) (by omega)
    (hp 2 (by decide)) (n 335) (n 331) W (loadSecond n v) w1 hW (hn 335 (by decide)) w331
    input tape s1 b1 (bnat1 335 (by decide)) (bnat1 331 (by decide))
  have bnat2 (i : ℕ) (hi : i∈Finset.Icc 330 341) : Word s2.val i (n i) := by
    have bound := Finset.mem_Icc.mp hi
    exact word_of_eq (f2.tapes i (FractionWord.outside S i (by omega))) (bnat1 i hi)
  have w2 := w1.update 2 (part_width n 335 W (hn 335 (by decide)) w331)
  obtain ⟨c3,t,e3,h3,b3,f3⟩ := FractionWord.executes S 341 331 5 (by omega) (by omega)
    (hp 5 (by decide)) (n 341) (n 331) W (loadThird n v) w2 hW (hn 341 (by decide)) w331
    input tape s2 b2 (bnat2 341 (by decide)) (bnat2 331 (by decide))
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,b3,f0.trans (f1.trans (f2.trans f3))⟩
  nlinarith only [h0,h1,h2,h3]

#print axioms load_executes
end Maxwell.Continuum.RationalDataflow.RootGrid
