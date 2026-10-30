import Maxwell.Continuum.RationalDataflowArrayMap

/-! Executed duplication of a raw shared-denominator table. The fixed
program preserves both numerator channels exactly; it performs no rational
normalization and needs no arithmetic trace supplied by the caller. -/

namespace Maxwell.Continuum.RationalDataflow.PartArray

open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def copyCode : Code := mapCode .done 1

theorem copy_values {n : ℕ} (a : Table n) (v : ℕ→Parts) :
    mapValues a .done 1 v=a.get := by
  funext i
  have he : n-i.val=(n-1-i.val)+1 := by omega
  have hi : n-1-(n-1-i.val)=i.val := by omega
  simp only [mapValues,he,iterate,Control.evaluate,Function.update_self,hi,Table.getD,
    dite_eq_left i.isLt]

private theorem copy_width {n : ℕ} (a : Table n) (v : ℕ→Parts) (B : ℕ)
    (hB : 0<B) (ha : ∀ i, (a.get i).Width B) (hv : WidthBank {1} B v) (k : ℕ) :
    WidthBank {1} B (iterate a 1 .done v k) := by
  induction k with
  | zero => exact hv
  | succ k ih => exact ih.update 1 (a.getD_width B hB ha _)

private theorem getD_valid {n : ℕ} (a : Table n) (ha : ∀ i, (a.get i).Valid) (i : ℕ) :
    (a.getD i).Valid := by
  unfold Table.getD
  split_ifs with hi
  · exact ha _
  · exact Parts.literal_valid 0

private theorem copy_good {n : ℕ} (a : Table n) (v : ℕ→Parts)
    (ha : ∀ i, (a.get i).Valid) (hv : Good {1} v) (k : ℕ) :
    Good {1} (iterate a 1 .done v k) := by
  induction k with
  | zero => exact hv
  | succ k ih => exact ih.update 1 (getD_valid a ha _)

def copyCost (n B : ℕ) : ℕ := 2^23*(n+1)*(B+5)^2

theorem copy_executes {n : ℕ} (a b : Table n) (v : ℕ→Parts) (B : ℕ)
    (hB : 0<B) (haWidth : ∀ i, (a.get i).Width B) (haValid : ∀ i, (a.get i).Valid)
    (hvWidth : WidthBank {1} B v) (hvGood : Good {1} v)
    (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth B)
    (hslot : B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : SharedConversion.Ready {1} v s) (ha : a.Ready s) (hb : b.OutputReady s) :
    ∃ cost t finalWord, Executes input tape copyCode cost s t ∧ cost≤copyCost n B ∧
      SharedConversion.Ready {1} (iterate a 1 .done v n) t ∧ a.Ready t ∧
      (b.filled a.get 0).OutputReady t ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length := by
  have hw := copy_width a v B hB haWidth hvWidth
  have hg := copy_good a v haValid hvGood
  obtain ⟨cost,t,word,he,hcost,hs',ha',hb',hword,hl⟩ := map_executes a b {1} (by simp)
    .done trivial 1 (by simp) v B hB haMeta hbMeta hslot hsep hdisjoint
    (fun k _ => hw k)
    (fun k _ => (hw k).update 1 (a.getD_width B hB haWidth _))
    (fun k _ => (hg k).update 1 (getD_valid a haValid _)) (fun _ _ => trivial)
    input tape xs origin hlen s hn hcount hs ha hb
  refine ⟨cost,t,word,he,?_,hs',ha',?_,hword,hl⟩
  · simp only [mapStepCost,Control.steps,Nat.zero_mul,Nat.add_zero] at hcost
    have hlin : 13*xs.length+15≤16*(B+5)^2 := by nlinarith only [hlen]
    have hquad : 1≤(B+5)^2 := by nlinarith
    unfold copyCost
    nlinarith only [hcost,hlin,hquad,Nat.mul_le_mul_left (n+1) hlin,
      Nat.mul_le_mul_left n hquad]
  · simpa only [copy_values] using hb'

theorem copy_computes {n : ℕ} (a b : Table n) (v : ℕ→Parts) (B : ℕ)
    (hB : 0<B) (haWidth : ∀ i, (a.get i).Width B) (haValid : ∀ i, (a.get i).Valid)
    (hvWidth : WidthBank {1} B v) (hvGood : Good {1} v)
    (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth B)
    (hslot : B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : SharedConversion.Ready {1} v s) (ha : a.Ready s) (hb : b.OutputReady s) :
    ∃ t,
      (runPriced (copyCode.compile.next input tape) (copyCost n B+1) s.val).finished=
        some (t.place copyCode.size) ∧
      (runPriced (copyCode.compile.next input tape) (copyCost n B+1) s.val).instructions≤copyCost n B ∧
      a.Ready t ∧ (b.filled a.get 0).OutputReady t ∧
      ∀ i, (b.filled a.get 0).get i=a.get i := by
  obtain ⟨cost,t,_,he,hcost,_,ha',hb',_,_⟩ := copy_executes a b v B hB haWidth haValid
    hvWidth hvGood haMeta hbMeta hslot hsep hdisjoint input tape xs origin hlen s hn hcount hs ha hb
  obtain ⟨hrun,hsteps⟩ := he.compiled_run (copyCost n B+1) (by omega)
  exact ⟨t,hrun,hsteps ▸ hcost,ha',hb',Table.filled_get b a.get (fun i => (haWidth i).mono hslot)⟩

#print axioms copy_executes
#print axioms copy_computes

end Maxwell.Continuum.RationalDataflow.PartArray
