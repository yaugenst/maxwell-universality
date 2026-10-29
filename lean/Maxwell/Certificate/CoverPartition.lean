import Maxwell.Certificate.Coverage

namespace Maxwell.Certificate.FrozenCover

def rootBox : Box := ⟨![0, 0, 0], ![1, 1, 1]⟩

def quarterBox (ix iy iz : Fin 4) : Box :=
  ⟨![(ix.val : ℚ) / 4, (iy.val : ℚ) / 4, (iz.val : ℚ) / 4],
    ![((ix.val : ℚ) + 1) / 4, ((iy.val : ℚ) + 1) / 4,
      ((iz.val : ℚ) + 1) / 4]⟩

private theorem quarter_covers {t : ℝ} (hlo : 0 ≤ t) (hhi : t ≤ 1) :
    ∃ i : Fin 4, ((i.val : ℚ) / 4 : ℚ) ≤ t ∧
      t ≤ (((i.val : ℚ) + 1) / 4 : ℚ) := by
  by_cases h1 : t ≤ 1/4
  · exact ⟨0, by norm_num; exact ⟨hlo, h1⟩⟩
  · by_cases h2 : t ≤ 1/2
    · exact ⟨1, by norm_num; constructor <;> linarith⟩
    · by_cases h3 : t ≤ 3/4
      · exact ⟨2, by norm_num; constructor <;> linarith⟩
      · exact ⟨3, by norm_num; constructor <;> linarith⟩

/-- The sixty-four closed quarter boxes cover every real point of the root,
including the outer boundary and all shared faces. -/
theorem root_to_quarters {x : Fin 3 → ℝ} (hx : rootBox.Contains x) :
    ∃ ix iy iz : Fin 4, (quarterBox ix iy iz).Contains x := by
  have hc (i : Fin 3) : 0 ≤ x i ∧ x i ≤ 1 := by
    have hi := hx i
    fin_cases i <;> simpa [rootBox] using hi
  obtain ⟨ix, hix⟩ := quarter_covers (hc 0).1 (hc 0).2
  obtain ⟨iy, hiy⟩ := quarter_covers (hc 1).1 (hc 1).2
  obtain ⟨iz, hiz⟩ := quarter_covers (hc 2).1 (hc 2).2
  refine ⟨ix, iy, iz, ?_⟩
  intro i
  fin_cases i
  · simpa [quarterBox] using hix
  · simpa [quarterBox] using hiy
  · simpa [quarterBox] using hiz

end Maxwell.Certificate.FrozenCover
