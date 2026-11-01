import Maxwell.Continuum.RationalDataflowArraySquares

/-! The fixed sum-of-squares program initializes its accumulator and executes
the full counted input traversal. Its raw result and width are retained. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def squaresCode (accumulator entry : ℕ) : Code :=
  .seq (NatAssign.code (literalStage accumulator (Parts.literal 0)))
    (foldCode entry (squaresBody accumulator entry))

def squaresCost (n W wordLength : ℕ) : ℕ :=
  stageCost (squaresWidth n W)+(n+1)*(13*wordLength+15)+
    n*foldStepCost (squaresBody 0 1) (squaresWidth n W)

theorem squares_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (accumulator entry : ℕ)
    (hacc : accumulator∈S) (hentry : entry∈S) (hne : accumulator≠entry)
    (W : ℕ) (hW : 1≤W) (hmeta : a.MetadataWidth W)
    (haWidth : ∀ i, (a.get i).Width W) (haValid : ∀ i, (a.get i).Valid)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hgood : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ cost t finalWord, Executes input tape (squaresCode accumulator entry) cost s t ∧
      cost≤squaresCost n W xs.length ∧
      RationalDataflow.Ready S
        (iterate a entry (squaresBody accumulator entry) (sumStart v accumulator) n) t ∧
      a.Ready t ∧ t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      WidthBank S (squaresWidth n W)
        (iterate a entry (squaresBody accumulator entry) (sumStart v accumulator) n) ∧
      Good S (iterate a entry (squaresBody accumulator entry) (sumStart v accumulator) n) ∧
      (iterate a entry (squaresBody accumulator entry) (sumStart v accumulator) n accumulator).value=
        ∑ i : Fin n, (a.get i).value^2 := by
  have hB : W≤squaresWidth n W := by unfold squaresWidth sumWidth; nlinarith
  have hzero : (Parts.literal (0:ℚ)).Width (squaresWidth n W) :=
    (Parts.literal_width RationalWords.width_zero').mono (hW.trans hB)
  obtain ⟨c0,t0,e0,h0,b0,f0⟩ := literal_executes S accumulator hacc (Parts.literal 0) v
    (squaresWidth n W) hzero (hv.mono hB) input tape s hs
  have t0a := ha.arithmetic_frame S f0 b0.2
  have hout : 201∉workspace S := outside_workspace S 201 (by decide)
  have before (k : ℕ) (hk : k<n) : WidthBank S (squaresWidth n W)
      (iterate a entry (squaresBody accumulator entry) (sumStart v accumulator) k) := by
    apply (squares_iterate_width a S accumulator entry hne W hW haWidth v hv hacc k).mono
    unfold squaresWidth sumWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1
  have good (k : ℕ) (_hk : k<n) :
      Good S (loaded a entry (squaresBody accumulator entry) (sumStart v accumulator) k) :=
    (squares_iterate_good a S accumulator entry haValid v hgood hacc hentry k).update entry
      (a.getD_valid haValid _)
  obtain ⟨c1,t,word,e1,b1,a1,word1,len1,h1⟩ := fold_executes a S entry hentry
    (squaresBody accumulator entry) ⟨⟨hentry,hentry,hentry⟩,⟨⟨hacc,hacc,hentry⟩,trivial⟩⟩
    (sumStart v accumulator) (squaresWidth n W) (hmeta.mono hB) before
    (squares_widthTrace a S accumulator entry hne W hW haWidth v hv hacc) good
    (fun _ _ => ⟨trivial,⟨trivial,trivial⟩⟩) input tape xs origin (hlen.trans hB) t0 hn
    ((f0.tapes 201 hout).trans hcount) b0 t0a
  refine ⟨c0+c1,t,word,e0.seq e1,?_,b1,a1,word1,len1,
    squares_iterate_width a S accumulator entry hne W hW haWidth v hv hacc n,
    squares_iterate_good a S accumulator entry haValid v hgood hacc hentry n,
    squares_iterate_value a accumulator entry hne haValid v⟩
  have eq : foldStepCost (squaresBody accumulator entry) (squaresWidth n W)=
      foldStepCost (squaresBody 0 1) (squaresWidth n W) := rfl
  rw [eq] at h1
  unfold squaresCost
  omega

#print axioms squares_executes
end Maxwell.Continuum.RationalDataflow.PartArray
