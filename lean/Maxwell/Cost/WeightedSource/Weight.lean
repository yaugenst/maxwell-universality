import Maxwell.Cost.WeightedSource.WeightExport

namespace Maxwell.Cost.WeightedSource.Weight
open Structured RationalAccumulator
open Maxwell.Defect.DyadicSqrt.Integer
set_option maxHeartbeats 1600000

def code (A B : ℕ) : Code := .seq (setupCode A B)
  (.seq (.call (WordTransfer.clone 400 40))
    (.seq DyadicSqrt.loopCode (.seq (.call (TapeOps.clear 40)) exportCode)))
def width (A B k : ℕ) : ℕ := A.bits.length+B.bits.length+2*k+1

def costBound (A B k : ℕ) : ℕ :=
  10*(A.bits.length+B.bits.length)+30+15*k.bits.length+17+
    DyadicSqrt.loopBudget A B k+6*k.bits.length+4+100*(width A B k+1)

theorem final_width (A B k : ℕ) :
    DyadicSqrt.Width (DyadicSqrt.bank (A*4^k) B (lowerNum A B k) (2^k)) (width A B k) := by
  have hA := scaledNumerator_bits_length_le A k
  have hL := lowerNum_bits_length_le A B k
  have hP : (2^k:ℕ).bits.length ≤ k+1 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    rw [pow_succ]
    have hp : 0<(2:ℕ)^k := by positivity
    omega
  apply DyadicSqrt.bank_width <;> dsimp [width] <;> omega

/-- Fixed weight literals and an actual stored precision counter produce
both dyadic words. There is no rational or square-root runtime oracle. -/
theorem executes (A B k : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : Bank s.val (fun _=>0)) (hr : Scratch s.val 0) (hk : Word s.val 400 k)
    (h40 : Blank s.val 40) (h410 : Blank s.val 410) (h411 : Blank s.val 411) :
    ∃ cost t, cost ≤ costBound A B k  ∧  Executes input tape (code A B) cost s t  ∧ 
      Word t.val 410 (lowerNum A B k)  ∧  Word t.val 411 (2^k)  ∧ 
      Bank t.val (fun _=>0)  ∧  Scratch t.val 0  ∧  Blank t.val 40  ∧  Frame s.val t.val := by
  obtain ⟨a,ea,ba,ra,fa⟩ := setup A B input tape s hb hr
  obtain ⟨ko,hkw⟩ := word_of_eq (fa.2.2.2.2.2.1 400 (by decide)) hk
  obtain ⟨origin,hblank⟩ := blank_of_eq (fa.2.2.2.2.2.1 40 (by decide)) h40
  obtain ⟨b,eb,hbt,fb⟩ := WordCall.clone 400 40 (by decide) input tape k.bits ko origin a hkw hblank
  have keepb (i : ℕ) (hi : i ≠ 40) : b.val.tapes i=a.val.tapes i := by simp [hbt,hi]
  have bb : Bank b.val (DyadicSqrt.bank A B 0 1) := fun i hi hi' =>
    word_of_eq (keepb i (by omega)) (ba i hi hi')
  have rb : Scratch b.val 0 :=
    ⟨blank_of_eq (keepb 0 (by decide)) ra.1,word_of_eq (keepb 1 (by decide)) ra.2.1,
      blank_of_eq (keepb 2 (by decide)) ra.2.2.1,blank_of_eq (keepb 3 (by decide)) ra.2.2.2⟩
  have fclone : DyadicSqrt.LoopFrame a.val b.val :=
    ⟨fb.1,fb.2.1,fb.2.2.1,fb.2.2.2.1,fb.2.2.2.2.1,fun i hi=>keepb i (by omega),
      fun i hi=>fb.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)⟩
  obtain ⟨lc,c,counter,hlc,ec,bc,rc,hcounter,hcl,fc⟩ :=
    DyadicSqrt.loop_executes input tape A B k origin b bb rb (by simp [hbt])
  obtain ⟨d,ed,hdt,fd⟩ := WordCall.clear 40 input tape counter origin c hcounter
  have keepd (i : ℕ) (hi : i ≠ 40) : d.val.tapes i=c.val.tapes i := by simp [hdt,hi]
  have bd : Bank d.val (DyadicSqrt.bank (A*4^k) B (lowerNum A B k) (2^k)) := fun i hi hi' =>
    word_of_eq (keepd i (by omega)) (bc i hi hi')
  have rd : Scratch d.val 0 :=
    ⟨blank_of_eq (keepd 0 (by decide)) rc.1,word_of_eq (keepd 1 (by decide)) rc.2.1,
      blank_of_eq (keepd 2 (by decide)) rc.2.2.1,blank_of_eq (keepd 3 (by decide)) rc.2.2.2⟩
  have fclear : DyadicSqrt.LoopFrame c.val d.val :=
    ⟨fd.1,fd.2.1,fd.2.2.1,fd.2.2.2.1,fd.2.2.2.2.1,fun i hi=>keepd i (by omega),
      fun i hi=>fd.2.2.2.2.2.2 i (by omega) (by omega)⟩
  have fpre := ((fa.toLoop.trans fclone).trans fc).trans fclear
  obtain ⟨xc,t,hxc,ex,h410out,h411out,bt,rt,ht40,ft⟩ := export_executes input tape
    (DyadicSqrt.bank (A*4^k) B (lowerNum A B k) (2^k)) (width A B k) (final_width A B k) d bd rd
    (blank_of_eq (fpre.2.2.2.2.2.1 410 (by decide)) h410)
    (blank_of_eq (fpre.2.2.2.2.2.1 411 (by decide)) h411)
  refine ⟨(10*(A.bits.length+B.bits.length)+30)+(15*k.bits.length+17+(lc+(6*counter.length+4+xc))),t,
    ?_,ea.seq (eb.seq (ec.seq (ed.seq ex))),?_,?_,bt,rt,
    blank_of_eq ht40 ⟨origin+counter.length,by simp [hdt]⟩,(Frame.of_loop fpre).trans ft⟩
  · dsimp only [costBound]
    omega
  · simpa [DyadicSqrt.bank] using h410out
  · simpa [DyadicSqrt.bank] using h411out

theorem costBound_polynomial (A B k : ℕ) :
    costBound A B k ≤ (k+1)*(14000000000*(A.bits.length+B.bits.length+2*k+5)^2+
      400*(A.bits.length+B.bits.length+k+5)) := by
  have hu := DyadicSqrt.upperBudget_le_polynomial A B k
  have hkbits : k.bits.length ≤ k := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n:=k))
  unfold DyadicSqrt.upperBudget at hu
  dsimp only [costBound,width]
  nlinarith [Nat.zero_le (k*A.bits.length),Nat.zero_le (k*B.bits.length)]

/-- The source weighting convention calls this lower endpoint at precision
`2*b+5`, exactly matching `weight x (b+2)`. -/
theorem weight_binding (A B b : ℕ) (hB : 0<B) :
    (lowerNum A B (2*b+5):ℚ)/(2^(2*b+5):ℕ)=
      Maxwell.Defect.DyadicSqrt.weight ((A:ℚ)/B) (b+2) := by
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [lower_binding A B (2*b+5) hB]
  simp only [Maxwell.Defect.DyadicSqrt.weight]
  congr 1

/-- Capped execution of the compiled program returns the two exact words. -/
theorem compiled_run (A B k : ℕ) (hB : 0<B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : Bank s.val (fun _=>0)) (hr : Scratch s.val 0) (hk : Word s.val 400 k)
    (h40 : Blank s.val 40) (h410 : Blank s.val 410) (h411 : Blank s.val 411) :
    ∃ t : Store, (runPriced ((code A B).compile.next input tape) (costBound A B k+1) s.val).finished=
        some (t.place (code A B).size)  ∧ 
      (runPriced ((code A B).compile.next input tape) (costBound A B k+1) s.val).instructions ≤ costBound A B k  ∧ 
      Word t.val 410 (lowerNum A B k)  ∧  Word t.val 411 (2^k)  ∧ 
      (lowerNum A B k:ℚ)/(2^k:ℕ)=Maxwell.Defect.DyadicSqrt.lower ((A:ℚ)/B) k  ∧ 
      Bank t.val (fun _=>0)  ∧  Scratch t.val 0  ∧  Blank t.val 40  ∧  Frame s.val t.val := by
  obtain ⟨c,t,hc,he,h410out,h411out,bt,rt,ht40,hf⟩ := executes A B k input tape s hb hr hk h40 h410 h411
  have run := he.compiled_run (costBound A B k+1) (by omega)
  exact ⟨t,run.1,run.2 ▸ hc,h410out,h411out,by simpa only [Nat.cast_pow,Nat.cast_ofNat] using lower_binding A B k hB,bt,rt,ht40,hf⟩

end Maxwell.Cost.WeightedSource.Weight
