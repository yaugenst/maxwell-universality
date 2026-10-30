import Maxwell.Continuum.ProfileRoundedTable
import Maxwell.Continuum.RationalDataflowArrayOutputFrame

/-! The rounded-coefficient producer preserves a disjoint second buffer and
the runtime metadata needed by the following endpoint-correction pass. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

def roundedStoreProtected : List ℕ := [200,202,203,204,205,216,661]

theorem roundedStore_protects :
    roundedStoreProtected.all (fun i => roundedStoreCode.protectsTape i)=true := by decide

theorem roundedStore_keep {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (e : Executes input tape roundedStoreCode cost s t) (i : ℕ) (hi : i∈roundedStoreProtected) :
    t.val.tapes i=s.val.tapes i :=
  e.protectsTape i (List.all_eq_true.mp roundedStore_protects i hi)

theorem roundedStore_spare_ready {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (e : Executes input tape roundedStoreCode cost s t) {n m : ℕ}
    {a : PartArray.Table n} {b : PartArray.Table m} (ha : a.Ready s)
    (hdis : a.SeparatedFrom b) (i : Fin m) (x : Parts)
    (hm : t.val.memory=b.writeMemory i x s.val.memory)
    (hb : (b.set i x).OutputReady t) : a.Ready t := by
  refine ⟨hb.scratch,hb.seven,
    BankArray.word_of_eq (roundedStore_keep e 200 (by simp [roundedStoreProtected])) ha.width,
    BankArray.word_of_eq (roundedStore_keep e 202 (by simp [roundedStoreProtected])) ha.basePositive,
    BankArray.word_of_eq (roundedStore_keep e 203 (by simp [roundedStoreProtected])) ha.baseNegative,
    BankArray.word_of_eq (roundedStore_keep e 204 (by simp [roundedStoreProtected])) ha.baseDenominator,
    BankArray.word_of_eq (roundedStore_keep e 205 (by simp [roundedStoreProtected])) ha.clock,?_,?_,?_⟩
  · rw [hm]
    exact b.writeMemory_preserves i x ha.positive (hdis _ (by simp))
  · rw [hm]
    exact b.writeMemory_preserves i x ha.negative (hdis _ (by simp))
  · rw [hm]
    exact b.writeMemory_preserves i x ha.denominator (hdis _ (by simp))

theorem inputReady_count700 {n : ℕ} {a : PartArray.Table n} {s t : Store} (h : a.Ready s)
    (f : CountedShifted.Frame 700 s t) : a.Ready t := by
  have keep (i : ℕ) (hi : i≠700) := f.2.2.2.2.2.1 i hi
  have hz : BankArray.Scratch t.val := by
    rcases h.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨blank_of_eq (keep 0 (by decide)) h0,blank_of_eq (keep 1 (by decide)) h1,
      blank_of_eq (keep 2 (by decide)) h2,blank_of_eq (keep 3 (by decide)) h3,
      blank_of_eq (keep 5 (by decide)) h5,blank_of_eq (keep 6 (by decide)) h6,
      blank_of_eq (keep 8 (by decide)) h8,blank_of_eq (keep 9 (by decide)) h9⟩
  refine ⟨hz,blank_of_eq (keep 7 (by decide)) h.seven,
    BankArray.word_of_eq (keep 200 (by decide)) h.width,
    BankArray.word_of_eq (keep 202 (by decide)) h.basePositive,
    BankArray.word_of_eq (keep 203 (by decide)) h.baseNegative,
    BankArray.word_of_eq (keep 204 (by decide)) h.baseDenominator,
    BankArray.word_of_eq (keep 205 (by decide)) h.clock,?_,?_,?_⟩
  · simpa only [f.2.2.1] using h.positive
  · simpa only [f.2.2.1] using h.negative
  · simpa only [f.2.2.1] using h.denominator

theorem tableMetadata_separatedFrom {n m : ℕ} {a b : PartArray.Table n}
    (h : tableMetadata a b) (c : PartArray.Table m) (hs : c.SeparatedFrom a) :
    c.SeparatedFrom b := by
  simpa only [PartArray.Table.SeparatedFrom,h.1,h.2.1,h.2.2.1,h.2.2.2.1] using hs

#print axioms roundedStore_spare_ready
#print axioms inputReady_count700
end Maxwell.Continuum.Profile.Runtime
