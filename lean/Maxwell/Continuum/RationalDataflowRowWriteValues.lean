import Maxwell.Continuum.RationalDataflowRowWritePlan

/-! Exact contents and metadata of the actual row-write output arrays. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem Table.set_get {n : ℕ} (b : Table n) (i : Fin n) (x : Parts)
    (hx : x.Width (addressValue b.width)) : (b.set i x).get i=x := by
  have hp := FixedWidth.bits_value (addressValue b.width) x.positive.bits hx.1
  have hn := FixedWidth.bits_value (addressValue b.width) x.negative.bits hx.2.1
  have hd := FixedWidth.bits_value (addressValue b.width) x.denominator.bits hx.2.2
  simp [Table.set,Table.get,Vector.get,Fin.cast,hp,hn,hd]

theorem Table.set_get_ne {n : ℕ} (b : Table n) (i j : Fin n) (x : Parts) (hij : i≠j) :
    (b.set i x).get j=b.get j := by
  have hval : i.val≠j.val := fun h => hij (Fin.ext h)
  simp [Table.set,Table.get,Vector.get,Fin.cast,hval]

theorem Table.setD_get_ne {n : ℕ} (b : Table n) (i : ℕ) (j : Fin n) (x : Parts) (hij : i≠j.val) :
    (b.setD i x).get j=b.get j := by
  unfold Table.setD
  split_ifs with hi
  · exact b.set_get_ne ⟨i,hi⟩ j x (by intro h; exact hij (congrArg Fin.val h))
  · rfl

theorem rowWriteTable_get_unchanged {n : ℕ} (b : Table n) (stride row : ℕ)
    (plan : List (ℕ×ℕ)) (v : ℕ→Parts) (j : Fin n)
    (hj : ∀x∈plan,stride*row+x.1≠j.val) :
    (rowWriteTable stride row plan v b).get j=b.get j := by
  induction plan generalizing b with
  | nil => rfl
  | cons x rest ih =>
    rw [rowWriteTable,ih _ (fun y hy => hj y (by simp [hy])),Table.setD_get_ne]
    exact hj x (by simp)

theorem rowWriteTable_metadata {n : ℕ} (b : Table n) (stride row : ℕ)
    (plan : List (ℕ×ℕ)) (v : ℕ→Parts) :
    (rowWriteTable stride row plan v b).width=b.width ∧
    (rowWriteTable stride row plan v b).basePositive=b.basePositive ∧
    (rowWriteTable stride row plan v b).baseNegative=b.baseNegative ∧
    (rowWriteTable stride row plan v b).baseDenominator=b.baseDenominator ∧
    (rowWriteTable stride row plan v b).clock=b.clock := by
  induction plan generalizing b with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons x rest ih =>
    simp only [rowWriteTable]
    have h := ih (b.setD (stride*row+x.1) (v x.2))
    unfold Table.setD at h ⊢
    split_ifs at h ⊢ with hi
    · exact h
    · exact h

theorem Table.MetadataWidth.rowWrite {n : ℕ} {b : Table n} {W : ℕ}
    (h : b.MetadataWidth W) (stride row : ℕ) (plan : List (ℕ×ℕ)) (v : ℕ→Parts) :
    (rowWriteTable stride row plan v b).MetadataWidth W := by
  obtain ⟨hw,hp,hn,hd,hc⟩ := rowWriteTable_metadata b stride row plan v
  exact ⟨by simpa only [hw] using h.width,by simpa only [hp] using h.basePositive,
    by simpa only [hn] using h.baseNegative,by simpa only [hd] using h.baseDenominator,
    by simpa only [hc] using h.clock⟩

theorem Table.Separated.rowWrite {n : ℕ} {b : Table n}
    (h : b.Separated) (stride row : ℕ) (plan : List (ℕ×ℕ)) (v : ℕ→Parts) :
    (rowWriteTable stride row plan v b).Separated := by
  obtain ⟨hw,hp,hn,hd,_⟩ := rowWriteTable_metadata b stride row plan v
  simpa only [Table.Separated,hw,hp,hn,hd] using h

theorem Table.SeparatedFrom.rowWrite {n m : ℕ} {a : Table n} {b : Table m}
    (h : a.SeparatedFrom b) (stride row : ℕ) (plan : List (ℕ×ℕ)) (v : ℕ→Parts) :
    a.SeparatedFrom (rowWriteTable stride row plan v b) := by
  obtain ⟨hw,hp,hn,hd,_⟩ := rowWriteTable_metadata b stride row plan v
  simpa only [Table.SeparatedFrom,hw,hp,hn,hd] using h

#print axioms Table.set_get
#print axioms rowWriteTable_get_unchanged
end Maxwell.Continuum.RationalDataflow.PartArray
