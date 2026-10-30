import Maxwell.Continuum.RationalDataflowArrayProgram
import Maxwell.Continuum.RationalDataflowArraySum
import Maxwell.Continuum.RationalDataflowDenominatorStage

/-! The actual denominator product is accumulated without rational normalization. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def denominatorPrefix {n : ℕ} (a : Table n) : ℕ→ℕ
  | 0 => 1
  | k+1 => (a.getD (n-1-k)).denominator*denominatorPrefix a k

def denominatorStart (v : ℕ→Parts) (accumulator : ℕ) : ℕ→Parts :=
  Function.update v accumulator (Parts.literal 1)

theorem denominator_iterate_accumulator {n : ℕ} (a : Table n) (accumulator entry : ℕ)
    (hne : accumulator≠entry) (v : ℕ→Parts) (k : ℕ) :
    programIterate a entry (denominatorStep accumulator entry) (denominatorStart v accumulator)
      k accumulator=⟨denominatorPrefix a k,0,1⟩ := by
  induction k with
  | zero => simp [programIterate,denominatorStart,denominatorPrefix,Parts.literal]
  | succ k ih =>
    simp only [programIterate,denominatorStep,Function.update_self,
      Function.update_of_ne hne,ih,denominatorPrefix]

theorem denominator_iterate_width {n : ℕ} (a : Table n) (S : Finset ℕ)
    (accumulator entry : ℕ) (hne : accumulator≠entry) (W : ℕ) (hW : 1≤W)
    (ha : ∀ i, (a.get i).Width W) (v : ℕ→Parts) (hv : WidthBank S W v)
    (hacc : accumulator∈S) (k : ℕ) :
    WidthBank S (sumWidth k W)
      (programIterate a entry (denominatorStep accumulator entry) (denominatorStart v accumulator) k) := by
  have hbase (k : ℕ) : W≤sumWidth k W := by unfold sumWidth; nlinarith
  have hmono (k : ℕ) : sumWidth k W≤sumWidth (k+1) W := by unfold sumWidth; nlinarith
  induction k with
  | zero =>
    apply (hv.mono (hbase 0)).update accumulator
    exact (show (Parts.literal (1:ℚ)).Width 1 from by unfold Parts.Width Parts.literal; decide).mono (hW.trans (hbase 0))
  | succ k ih =>
    let state := programIterate a entry (denominatorStep accumulator entry) (denominatorStart v accumulator) k
    have he := a.getD_width W hW ha (n-1-k)
    have before := (ih.mono (hmono k)).update entry (he.mono (hbase (k+1)))
    have hp := (RationalAccumulator.bits_mul_le (a.getD (n-1-k)).denominator (state accumulator).positive).trans
      (Nat.add_le_add he.2.2 (ih accumulator hacc).1)
    have hp' : ((a.getD (n-1-k)).denominator*(state accumulator).positive).bits.length≤sumWidth (k+1) W :=
      hp.trans (by unfold sumWidth; nlinarith)
    have hnew : (⟨(a.getD (n-1-k)).denominator*(state accumulator).positive,
        (state accumulator).negative,(state accumulator).denominator⟩:Parts).Width (sumWidth (k+1) W) :=
      ⟨hp',(ih accumulator hacc).2.1.trans (hmono k),(ih accumulator hacc).2.2.trans (hmono k)⟩
    simpa only [programIterate,denominatorStep,Function.update_self,Function.update_of_ne hne]
      using before.update accumulator hnew

theorem denominator_loaded_width {n : ℕ} (a : Table n) (S : Finset ℕ)
    (accumulator entry : ℕ) (hne : accumulator≠entry) (W : ℕ) (hW : 1≤W)
    (ha : ∀ i, (a.get i).Width W) (v : ℕ→Parts) (hv : WidthBank S W v)
    (hacc : accumulator∈S) (k : ℕ) (hk : k≤n) :
    WidthBank S (sumWidth n W)
      (programLoaded a entry (denominatorStep accumulator entry) (denominatorStart v accumulator) k) := by
  have hmono : sumWidth k W≤sumWidth n W := by
    unfold sumWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right (W+1) (by omega)) 1
  exact ((denominator_iterate_width a S accumulator entry hne W hW ha v hv hacc k).mono hmono).update
    entry ((a.getD_width W hW ha _).mono (by unfold sumWidth; nlinarith))

theorem denominatorPrefix_eq_product {n : ℕ} (a : Table n) :
    denominatorPrefix a n=∏ i : Fin n, (a.get i).denominator := by
  have hp (k : ℕ) : denominatorPrefix a k=∏ j∈Finset.range k, (a.getD (n-1-j)).denominator := by
    induction k with
    | zero => simp [denominatorPrefix]
    | succ k ih => rw [denominatorPrefix,ih,Finset.prod_range_succ,Nat.mul_comm]
  rw [hp,Finset.prod_range_reflect (fun j => (a.getD j).denominator) n]
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Table.getD,dite_eq_left i.isLt]

def denominatorCode (accumulator entry : ℕ) : Code :=
  .seq (NatAssign.code (literalStage accumulator (Parts.literal 1)))
    (programCode entry (NatAssign.code (denominatorStage accumulator entry)))

def denominatorCost (n W wordLength : ℕ) : ℕ :=
  stageCost (sumWidth n W)+(n+1)*(13*wordLength+15)+
    n*(2^20*(sumWidth n W+5)^2+stageCost (sumWidth n W))

theorem denominator_product_executes {n : ℕ} (a : Table n) (S : Finset ℕ)
    (accumulator entry : ℕ) (hacc : accumulator∈S) (hentry : entry∈S) (hne : accumulator≠entry)
    (W : ℕ) (hW : 1≤W) (hmeta : a.MetadataWidth W) (haWidth : ∀ i, (a.get i).Width W)
    (v : ℕ→Parts) (hv : WidthBank S W v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ cost t output, Executes input tape (denominatorCode accumulator entry) cost s t ∧
      cost≤denominatorCost n W xs.length ∧ RationalDataflow.Ready S output t ∧ a.Ready t ∧
      output accumulator=⟨∏ i : Fin n, (a.get i).denominator,0,1⟩ := by
  have hB : W≤sumWidth n W := by unfold sumWidth; nlinarith
  have hone : (Parts.literal (1:ℚ)).Width (sumWidth n W) :=
    (show (Parts.literal (1:ℚ)).Width 1 from by unfold Parts.Width Parts.literal; decide).mono (hW.trans hB)
  obtain ⟨c0,t0,e0,h0,b0,f0⟩ := literal_executes S accumulator hacc (Parts.literal 1) v
    (sumWidth n W) hone (hv.mono hB) input tape s hs
  have before (k : ℕ) (hk : k<n) : WidthBank S (sumWidth n W)
      (programIterate a entry (denominatorStep accumulator entry) (denominatorStart v accumulator) k) := by
    apply (denominator_iterate_width a S accumulator entry hne W hW haWidth v hv hacc k).mono
    unfold sumWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right (W+1) (by omega)) 1
  have body (k : ℕ) (hk : k<n) (st : Store)
      (hst : RationalDataflow.Ready S
        (programLoaded a entry (denominatorStep accumulator entry) (denominatorStart v accumulator) k) st) :=
    denominator_executes S accumulator entry hacc hentry _ (sumWidth n W)
      (denominator_loaded_width a S accumulator entry hne W hW haWidth v hv hacc k hk.le)
      input tape st hst
  have hout : 201∉workspace S := outside_workspace S 201 (by decide)
  obtain ⟨c1,t,_,e1,b1,a1,_,_,h1⟩ := program_executes a S entry hentry
    (NatAssign.code (denominatorStage accumulator entry)) (denominatorStep accumulator entry)
    (denominatorStart v accumulator) (sumWidth n W) (stageCost (sumWidth n W))
    (hmeta.mono hB) before input tape body xs origin (hlen.trans hB) t0 hn
    ((f0.tapes 201 hout).trans hcount) b0 (ha.arithmetic_frame S f0 b0.2)
  refine ⟨c0+c1,t,programIterate a entry (denominatorStep accumulator entry)
    (denominatorStart v accumulator) n,e0.seq e1,?_,b1,a1,?_⟩
  · unfold denominatorCost
    omega
  · rw [denominator_iterate_accumulator a accumulator entry hne v n,denominatorPrefix_eq_product]

#print axioms denominator_product_executes
end Maxwell.Continuum.RationalDataflow.PartArray
