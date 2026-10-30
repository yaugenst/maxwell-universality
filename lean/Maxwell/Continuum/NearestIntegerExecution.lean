import Maxwell.Continuum.NearestIntegerData

/-! A fixed Boolean nearest-grid routine reads the actual scale word144,
computes the half-unit, and runs the exact signed floor and normalization. -/
namespace Maxwell.Continuum.RationalDataflow.NearestInteger
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def code (target source : ℕ) : Code :=
  .seq (Instruction.literal 14 1).code
    (.seq (NaturalChannel.code .denominator 144 14)
      (.seq (tail source).code (RoundedInteger.code target 14)))

theorem executes (S : Finset ℕ) (P target source W : ℕ)
    (ht : target∈S) (hs : source∈S) (h14 : 14∈S) (h15 : 15∈S)
    (hs14 : source≠14) (hs15 : source≠15) (hW : 2≤W)
    (hP : (2^P).bits.length≤W) (v : ℕ→Parts)
    (hw : WidthBank S W v) (hg : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready S v s) (hclean : DyadicFloor.Clean s.val) (hpower : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape (code target source) cost s t ∧
      cost≤2^160*(P+W+8)^2 ∧ Ready S (values P target source v) t ∧
      Good S (values P target source v) ∧ WidthBank S (P+16*W+19) (values P target source v) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      BinaryPrecision.Frame (DyadicFloor.StoredPower.workspace S) s.val t.val := by
  have hone : (Parts.literal 1).Width W :=
    (show (Parts.literal 1).Width 1 by norm_num [Parts.Width,Parts.literal]).mono (by omega)
  obtain ⟨c0,s0,e0,hc0,r0,f0⟩ := (Instruction.literal 14 1).executes S h14 v W hw hone input tape s hr
  let v0 := Function.update v 14 (Parts.literal 1)
  have w0 : WidthBank S W v0 := hw.update 14 hone
  have pow0 : Word s0.val 144 (2^P) := RationalAccumulator.word_of_eq
    (f0.tapes 144 (outside_workspace S 144 (by decide))) hpower
  have pow0raw : BankArray.Word s0.val 144 (2^P).bits := by
    simpa only [Word,BankArray.Word] using pow0
  obtain ⟨c1,s1,e1,hc1,r1,f1⟩ := NaturalChannel.executes S .denominator 144 14 h14 (by decide)
    v0 (2^P).bits input tape s0 r0 pow0raw
  have eq1 : Function.update v0 14
      (NaturalChannel.replace .denominator (v0 14) (addressValue (2^P).bits))=loaded P v := by
    simpa only [v0,Function.update_self,addressValue_bits] using loaded_eq P v
  rw [eq1] at r1
  have f1' : BinaryPrecision.Frame (workspace S) s0.val s1.val := f1.mono (by
    intro i hi
    simp only [Finset.mem_singleton,NaturalChannel.port] at hi
    subst i
    exact Finset.mem_union_right _ (cell_mem h14 (by simp [cellPorts])))
  have w1 : WidthBank S W (loaded P v) := hw.update 14 (unitPart_width P W (by omega) hP)
  have g1 : Good S (loaded P v) := hg.update 14 (unitPart_valid P)
  have trace := (tail source).automatic_widthTrace S (tail_valid S source hs h14 h15)
    (loaded P v) W w1 (tail_fits source W hW)
  obtain ⟨c2,s2,e2,hc2,r2,f2⟩ := (tail source).executes S (tail_valid S source hs h14 h15)
    (loaded P v) (8*(W+1)) trace g1 (tail_admissible source _) input tape s1 r1
  have w2 := prepared_width S P source W hs h14 h15 v hw hW hP
  have g2 : Good S (prepared P source v) := (tail source).evaluate_good S
    (tail_valid S source hs h14 h15) (loaded P v) g1 (tail_admissible source _)
  have frame02 := f0.trans (f1'.trans f2)
  have clean2 := hclean.arithmetic_frame frame02
  have power2 : Word s2.val 144 (2^P) := RationalAccumulator.word_of_eq
    (frame02.tapes 144 (outside_workspace S 144 (by decide))) hpower
  obtain ⟨c3,t,e3,hc3,r3,w3,z3,p3,f3⟩ := RoundedInteger.executes S P target 14 ht h14
    (prepared P source v) (8*(W+1)) w2 (g2 14 h14) input tape s2 r2 clean2 power2
  have he : Function.update (prepared P source v) target
      (RoundedInteger.result P (prepared P source v 14))=values P target source v := by
    rw [rounded_eq P source v hs14 hs15 (hg source hs)]
    rfl
  rw [he] at r3 w3
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,r3,?_,?_,z3,p3,
    (frame02.mono (RoundedInteger.arithmetic_workspace_subset S)).trans f3⟩
  · have hden : (dataValues v0 (NaturalChannel.port .denominator 14)).bits.length=1 := by
      simp [v0,NaturalChannel.port,Parts.literal]
    rw [hden] at hc1
    change c2≤3*operationCost (8*(W+1))+1 at hc2
    unfold operationCost at hc0 hc2
    nlinarith only [hc0,hc1,hc2,hc3,hP,Nat.zero_le P,Nat.zero_le W]
  · exact g2.update target (Parts.literal_valid _)
  · convert w3 using 1
    omega

#print axioms executes
end Maxwell.Continuum.RationalDataflow.NearestInteger
