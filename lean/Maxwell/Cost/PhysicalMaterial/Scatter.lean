import Maxwell.Cost.PhysicalMaterial.Scatter.Coordinates
import Maxwell.Cost.PhysicalMaterial.FlattenIndex

/-! A fixed prototype point is translated, flattened with actual binary
arithmetic, and its coordinate scratch is erased before the next point. -/
namespace Maxwell.Cost.PhysicalMaterial.Scatter
open Structured RationalAccumulator

def indexCode (d : Point) : Code :=
  .seq (coordinateCode d) (.seq (FlattenIndex.code 324 325 326)
    (.seq (.call (TapeOps.clear 324))
      (.seq (.call (TapeOps.clear 325)) (.call (TapeOps.clear 326)))))

def indexWork : Finset ℕ := {0,1,2,3,292,322,324,325,326}

def indexBudget (d : Point) (B : ℕ) : ℕ :=
  coordinateFactor d*(B+1)+20000*(B+offsetWidth d+3)^2+18*(B+offsetWidth d+1)+12

private theorem clear (target : ℕ) (ht : 10≤target) (input : List Bool) (tape : ℕ→Bool)
    (n : ℕ) (s : Store) (hw : Word s.val target n) (hr : Ready s.val) :
    ∃ t, Executes input tape (.call (TapeOps.clear target)) (6*n.bits.length+4) s t ∧
      Blank t.val target ∧ Ready t.val ∧ BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨t,he,hblank,hf,hsmall⟩ := DecoderConstants.clearStored target (by omega) input tape n s hw
  have frame : BinaryPrecision.Frame {target} s.val t.val := by
    refine ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
    intro i hi
    by_cases hh : i<4
    · exact hsmall i hh
    · exact hf.2.2.2.2.2.1 i (by omega) (by simpa using hi)
  refine ⟨t,he,hblank,?_,frame⟩
  intro i hi
  exact blank_of_eq (frame.tapes i (by simp; omega)) (hr i hi)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem index_executes (d : Point) (anchor : Fin 3 → ℕ) (ny nz B : ℕ)
    (hb : ∀ j,(anchor j).bits.length≤B) (hroom : ∀ j,0≤(anchor j:ℤ)+d j)
    (hnyB : ny.bits.length≤B) (hnzB : nz.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hw : ∀ j,Word s.val (294+j.val) (anchor j))
    (hny : Word s.val 251 ny) (hnz : Word s.val 252 nz)
    (hz : ∀ j:Fin 3,Blank s.val (324+j.val)) (h292 : Blank s.val 292)
    (h322 : Blank s.val 322) (hr : Ready s.val) :
    ∃ cost t, cost ≤ indexBudget d B ∧ Executes input tape (indexCode d) cost s t ∧
      Word t.val 322 ((coordinate anchor d 0*ny+coordinate anchor d 1)*nz+coordinate anchor d 2) ∧
      (∀ j:Fin 3,Blank t.val (324+j.val)) ∧ Blank t.val 292 ∧ Ready t.val ∧
      BinaryPrecision.Frame indexWork s.val t.val := by
  obtain ⟨ac,a,hac,ea,aw,a292,ar,af⟩ := coordinates_executes d anchor B hb hroom input tape s hw hz h292 hr
  have hlen := coordinate_length anchor d B hb
  obtain ⟨bc,b,hbc,eb,bw,br,bf,_⟩ := FlattenIndex.executes 324 325 326
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    input tape (coordinate anchor d 0) (coordinate anchor d 1) (coordinate anchor d 2) ny nz
    (B+offsetWidth d+1) a (aw 0) (aw 1) (aw 2)
    (word_of_eq (af.tapes 251 (by decide)) hny) (word_of_eq (af.tapes 252 (by decide)) hnz)
    ⟨hlen 0,hlen 1,hlen 2,by omega,by omega⟩ ar (blank_of_eq (af.tapes 322 (by decide)) h322)
  obtain ⟨c,ec,c324,cr,cf⟩ := clear 324 (by decide) input tape (coordinate anchor d 0) b
    (word_of_eq (bf.tapes 324 (by decide)) (aw 0)) br
  obtain ⟨e,ee,e325,er,ef⟩ := clear 325 (by decide) input tape (coordinate anchor d 1) c
    (word_of_eq ((cf.tapes 325 (by decide)).trans (bf.tapes 325 (by decide))) (aw 1)) cr
  obtain ⟨t,et,t326,tr,tf⟩ := clear 326 (by decide) input tape (coordinate anchor d 2) e
    (word_of_eq ((ef.tapes 326 (by decide)).trans
      ((cf.tapes 326 (by decide)).trans (bf.tapes 326 (by decide)))) (aw 2)) er
  have ce : BinaryPrecision.Frame ({324,325,326}:Finset ℕ) b.val t.val :=
    (cf.mono (by decide)).trans ((ef.mono (by decide)).trans (tf.mono (by decide)))
  refine ⟨ac+(bc+((6*(coordinate anchor d 0).bits.length+4)+
    ((6*(coordinate anchor d 1).bits.length+4)+(6*(coordinate anchor d 2).bits.length+4)))),t,?_,
    ea.seq (eb.seq (ec.seq (ee.seq et))),word_of_eq (ce.tapes 322 (by decide)) bw,?_,
    blank_of_eq ((ce.tapes 292 (by decide)).trans (bf.tapes 292 (by decide))) a292,tr,
    (af.mono (by decide)).trans ((bf.mono (by decide)).trans (ce.mono (by decide)))⟩
  · have h0 := hlen 0
    have h1 := hlen 1
    have h2 := hlen 2
    unfold indexBudget
    have hh : B+offsetWidth d+1+2 = B+offsetWidth d+3 := by omega
    rw [hh] at hbc
    omega
  · intro j
    fin_cases j
    · exact blank_of_eq ((tf.tapes 324 (by decide)).trans (ef.tapes 324 (by decide))) c324
    · exact blank_of_eq (tf.tapes 325 (by decide)) e325
    · exact t326

theorem indexBudget_le (d : Point) (B : ℕ) :
    indexBudget d B ≤ (coordinateFactor d+20030)*(B+offsetWidth d+3)^2 := by
  have h : B+1≤(B+offsetWidth d+3)^2 := by
    have hh := Nat.le_mul_self (B+offsetWidth d+3)
    rw [←pow_two] at hh
    omega
  have hm := Nat.mul_le_mul_left (coordinateFactor d) h
  unfold indexBudget
  nlinarith

end Maxwell.Cost.PhysicalMaterial.Scatter
