import Maxwell.Continuum.StoredSourceParsedParts
import Maxwell.Cost.Structured.WordCleanup

/-! Read the next original right-hand-side entry from its retained archive.
All old parser words are cleared by scans; no tape origin is reset for free. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def parseWords : List ℕ := [10,4801,4802]
def readCode : Code := .seq (WordCleanup.code parseWords)
  (.seq (NormalizedRecordParser.readRational 4801 4802) loadCode)
def readWork : Finset ℕ := {0,1,2,3,10,85,4801,4802,1000,1001,1002}

theorem read_executes (S : Finset ℕ) (h0 : 0∈S)
    (separate : Disjoint (ids S) ({10,85,4801,4802}:Finset ℕ))
    (q : ℚ) (v : ℕ→Parts) (B : ℕ) (hv : WidthBank S B v)
    (hn : q.num.natAbs.bits.length≤B) (hd : q.den.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (archiveOrigin : ℤ) (preceding suffix : List Bool) (s : Store)
    (ready : Ready S v s) (old : WordCleanup.Bounded parseWords B s.val)
    (source : s.val.tapes 85=BitTape.translate archiveOrigin (NormalizedRecordParser.cursor
      (preceding++(Codec.rat q++suffix)) preceding.length)) :
    ∃cost t,Executes input tape readCode cost s t ∧ cost≤2^25*(B+2)^2 ∧
      Ready S (Function.update v 0 (Parts.literal q)) t ∧
      WidthBank S B (Function.update v 0 (Parts.literal q)) ∧
      t.val.tapes 85=BitTape.translate archiveOrigin (NormalizedRecordParser.cursor (preceding++(Codec.rat q++suffix))
        (preceding.length+(Codec.rat q).length)) ∧
      Blank t.val 10 ∧ Word t.val 4801 q.num.natAbs ∧ Word t.val 4802 q.den ∧
      BinaryPrecision.Frame readWork s.val t.val := by
  obtain ⟨c0,a,e0,hc0,blank,f0⟩:=WordCleanup.executes parseWords B input tape s old
  have sourceA:= (f0.tapes 85 (by decide)).trans source
  obtain ⟨c1,b,e1,hc1,num,den,sign,sourceB,counter,head,f1⟩:=
    NormalizedRecordParser.readRational_shifted_executes 4801 4802
      (by decide) (by decide) (by decide) (by decide) (by decide)
      input tape q archiveOrigin preceding suffix a sourceA (blank 10 (by simp [parseWords]))
      (blank 4801 (by simp [parseWords])) (blank 4802 (by simp [parseWords]))
  have frame1 : BinaryPrecision.Frame {4801,4802,85} a.val b.val:=
    ⟨f1.address,head,f1.memory,f1.randomCursor,f1.output,f1.tapes⟩
  have before : BinaryPrecision.Frame {10,85,4801,4802} s.val b.val:=
    (f0.mono (by decide)).trans (frame1.mono (by decide))
  have readyB : Ready S v b:=by
    refine ⟨?_,?_⟩
    · intro i hi
      exact word_of_eq (before.tapes i (fun hh=>Finset.disjoint_left.mp separate hi hh)) (ready.1 i hi)
    · intro i hi
      exact blank_of_eq (before.tapes i (by simp only [Finset.mem_insert,Finset.mem_singleton];omega)) (ready.2 i hi)
  obtain ⟨c2,t,e2,hc2,rt,wt,f2⟩:=load_executes S h0 q v B hv hn hd input tape b readyB num den sign
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,rt,wt,
    (f2.tapes 85 (by decide)).trans sourceB,
    blank_of_eq (f2.tapes 10 (by decide)) counter,
    word_of_eq (f2.tapes 4801 (by decide)) num,
    word_of_eq (f2.tapes 4802 (by decide)) den,
    (before.mono (by decide)).trans (f2.mono (by decide))⟩
  change c0≤3*(6*B+4)+1 at hc0
  nlinarith only [hc0,hc1,hc2,hn,hd,Nat.zero_le B]

#print axioms read_executes
end Maxwell.Continuum.SourcePayload
