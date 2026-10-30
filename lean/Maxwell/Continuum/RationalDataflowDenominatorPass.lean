import Maxwell.Continuum.RationalDataflowDenominatorMachine
import Maxwell.Continuum.RationalDataflowSharedMapState

/-! The denominator pass exposes its exact output counter and register-width invariant. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem denominator_pass_executes {n : ℕ} (a : Table n) (W : ℕ) (hW : 1≤W)
    (hmeta : a.MetadataWidth W) (haWidth : ∀ i, (a.get i).Width W)
    (v : ℕ→Parts) (hv : WidthBank sharedSlots W v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready sharedSlots v s) (ha : a.Ready s) :
    ∃ cost t output finalWord, Executes input tape (denominatorCode 0 1) cost s t ∧
      cost≤denominatorCost n W xs.length ∧ RationalDataflow.Ready sharedSlots output t ∧ a.Ready t ∧
      output 0=⟨SharedTable.denominator a.get,0,1⟩ ∧
      WidthBank sharedSlots (sharedWidth n W) output ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  have hB : W≤sumWidth n W := by unfold sumWidth; nlinarith
  have hone : (Parts.literal (1:ℚ)).Width (sumWidth n W) :=
    (show (Parts.literal (1:ℚ)).Width 1 from by unfold Parts.Width Parts.literal; decide).mono (hW.trans hB)
  obtain ⟨c0,t0,e0,h0,b0,f0⟩ := literal_executes sharedSlots 0 (by decide) (Parts.literal 1) v
    (sumWidth n W) hone (hv.mono hB) input tape s hs
  have before (k : ℕ) (hk : k<n) : WidthBank sharedSlots (sumWidth n W)
      (programIterate a 1 (denominatorStep 0 1) (denominatorStart v 0) k) := by
    apply (denominator_iterate_width a sharedSlots 0 1 (by decide) W hW haWidth v hv (by decide) k).mono
    unfold sumWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right (W+1) (by omega)) 1
  have body (k : ℕ) (hk : k<n) (st : Store)
      (hst : RationalDataflow.Ready sharedSlots
        (programLoaded a 1 (denominatorStep 0 1) (denominatorStart v 0) k) st) :=
    denominator_executes sharedSlots 0 1 (by decide) (by decide) _ (sumWidth n W)
      (denominator_loaded_width a sharedSlots 0 1 (by decide) W hW haWidth v hv (by decide) k hk.le)
      input tape st hst
  obtain ⟨c1,t,finalWord,e1,b1,a1,hw,hl,h1⟩ := program_executes a sharedSlots 1 (by decide)
    (NatAssign.code (denominatorStage 0 1)) (denominatorStep 0 1) (denominatorStart v 0)
    (sumWidth n W) (stageCost (sumWidth n W)) (hmeta.mono hB) before input tape body xs origin
    (hlen.trans hB) t0 hn
    ((f0.tapes 201 (outside_workspace sharedSlots 201 (by decide))).trans hcount)
    b0 (ha.arithmetic_frame sharedSlots f0 b0.2)
  refine ⟨c0+c1,t,programIterate a 1 (denominatorStep 0 1) (denominatorStart v 0) n,
    finalWord,e0.seq e1,?_,b1,a1,?_,?_,hw,hl⟩
  · unfold denominatorCost
    omega
  · rw [denominator_iterate_accumulator a 0 1 (by decide) v n,denominatorPrefix_eq_product]
    rfl
  · apply (denominator_iterate_width a sharedSlots 0 1 (by decide) W hW haWidth v hv (by decide) n).mono
    unfold sharedWidth sumWidth
    nlinarith

#print axioms denominator_pass_executes
end Maxwell.Continuum.RationalDataflow.PartArray
