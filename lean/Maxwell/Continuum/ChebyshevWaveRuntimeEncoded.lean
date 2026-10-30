import Maxwell.Continuum.ChebyshevWaveRuntimeCanonical

/-! Fixed production of the exact canonical dyadic numerator words used by
the tensor encoder. The transform, rounding and normalization are all executed. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def encodedCode : Code := .seq cosineCode (.seq roundPairCode canonicalPairCode)
def encodedWorkspace : Finset ℕ := insert 144 cosineWorkspace
def encodedWidth (Q P grid W : ℕ) : ℕ := 2*(256*(coefficientWidth Q P grid W+1))+P+4
def encodedCost (Q P grid W : ℕ) : ℕ :=
  let B := 256*(coefficientWidth Q P grid W+1)
  cosineCost Q P grid W+roundPairCost P B+canonicalPairCost (2*B+P+3)

theorem floor_subset_encoded : DyadicFloor.StoredPower.workspace ids⊆encodedWorkspace := by
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl|hi
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ hi)))

theorem encoded_executes (Q P grid W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) (hg : Good ids v)
    (hW : 1 ≤ W) (hgrid : grid.bits.length ≤ W) (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s)
    (hn : Word s.val 680 grid) (hnSaved : Word s.val 681 grid) (hz : ∀i∈savedPorts,Blank s.val i)
    (hpower : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape encodedCode cost s t ∧ cost ≤ encodedCost Q P grid W ∧
      LoopReady Q P (encodedValues Q P grid v) t ∧ Blank t.val 680 ∧ Word t.val 681 grid ∧
      (∀i∈savedPorts,Blank t.val i) ∧ Word t.val 144 (2^P) ∧
      WidthBank ids (encodedWidth Q P grid W) (encodedValues Q P grid v) ∧
      BinaryPrecision.Frame encodedWorkspace s.val t.val := by
  let B := 256*(coefficientWidth Q P grid W+1)
  obtain ⟨c0,s0,e0,hc0,r0,z0,n0,hz0,hw0,f0⟩ := cosine_executes Q P grid W v hw hg hW hgrid hcount hone
    input tape s hs hn hnSaved hz
  have p0 := word_of_eq (f0.tapes 144 (by decide)) hpower
  obtain ⟨c1,s1,e1,hc1,r1,p1,f1⟩ := round_pair_executes Q P B _ hw0 (cosineValues_good Q P grid v hg)
    input tape s0 r0 p0
  have hw1 := roundPair_width P B _ hw0
  obtain ⟨c2,t,e2,hc2,r2,f2⟩ := canonical_pair_executes Q P (2*B+P+3) _ hw1 input tape s1 r1
  have keep (i : ℕ) (hi : 600 ≤ i ∧ i<1000) : t.val.tapes i=s0.val.tapes i :=
    (f2.tapes i (RationalDataflow.outside_workspace ids i (by omega))).trans
      (f1.tapes i (by
        simp only [DyadicFloor.StoredPower.workspace,Finset.mem_insert]
        exact not_or_intro (by omega) (DyadicFloor.high_outside_workspace ids i hi)))
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,r2,blank_of_eq (keep 680 (by decide)) z0,
    word_of_eq (keep 681 (by decide)) n0,?_,
    word_of_eq (f2.tapes 144 (RationalDataflow.outside_workspace ids 144 (by decide))) p1,
    canonicalPair_width _ _ hw1,(f0.mono (Finset.subset_insert _ _)).trans
      ((f1.mono floor_subset_encoded).trans
        (f2.mono (arithmetic_subset_cosine.trans (Finset.subset_insert _ _))))⟩
  · change _ ≤ cosineCost Q P grid W+roundPairCost P B+canonicalPairCost (2*B+P+3)
    omega
  · intro i hi
    have hh := savedPorts_range i hi
    exact blank_of_eq (keep i (by omega)) (hz0 i hi)

theorem encoded_wave_computes (q : ℚ) (Q N j W : ℕ) (hq : |q| ≤ Q) (hj : j ≤ waveDegree (8*Q) N)
    (v : ℕ→Parts) (hw : WidthBank ids W v) (hg : Good ids v) (hW : 1 ≤ W)
    (hgrid : (waveGrid (8*Q) N).bits.length ≤ W) (hcount : v 13=⟨0,0,1⟩) (hone : v 15=⟨1,0,1⟩)
    (hi : SumInput (waveGrid (8*Q) N) q (j:ℤ) 0 v) (hz0 : (v 8).value=0) (hz1 : (v 9).value=0)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q (waveWorkBits (8*Q) N) v s)
    (hn : Word s.val 680 (waveGrid (8*Q) N)) (hnSaved : Word s.val 681 (waveGrid (8*Q) N))
    (hz : ∀i∈savedPorts,Blank s.val i) (hpower : Word s.val 144 (2^waveWorkBits (8*Q) N)) :
    ∃t : Store,
      (runPriced (encodedCode.compile.next input tape)
        (encodedCost Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W+1) s.val).finished=
        some (t.place encodedCode.size) ∧
      (runPriced (encodedCode.compile.next input tape)
        (encodedCost Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W+1) s.val).instructions ≤
        encodedCost Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W ∧
      LoopReady Q (waveWorkBits (8*Q) N)
        (encodedValues Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) v) t ∧
      encodedValues Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) v 8=
        Parts.literal ((waveRoundedCoefficient q Q N j).1.numerator:ℚ) ∧
      encodedValues Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) v 9=
        Parts.literal ((waveRoundedCoefficient q Q N j).2.numerator:ℚ) ∧
      (encodedValues Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) v 8).Width (waveWorkBits (8*Q) N+7) ∧
      (encodedValues Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) v 9).Width (waveWorkBits (8*Q) N+7) := by
  obtain ⟨c,t,e,hc,rt,_,_,_,_,_,_⟩ := encoded_executes Q _ _ W v hw hg hW hgrid hcount hone
    input tape s hs hn hnSaved hz hpower
  obtain ⟨hrun,hsteps⟩ := e.compiled_run
    (encodedCost Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) W+1) (by omega)
  have he := encodedValues_wave q Q N j v hg hi hz0 hz1
  have hb := encodedValues_wave_width q Q N j hq hj v hg hi hz0 hz1
  exact ⟨t,hrun,hsteps ▸ hc,rt,he.1,he.2,hb.1,hb.2⟩

#print axioms encoded_executes
#print axioms encoded_wave_computes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
