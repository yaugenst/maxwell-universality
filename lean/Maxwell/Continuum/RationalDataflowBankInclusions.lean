import Maxwell.Continuum.RationalDataflowProgram

/-! Logical subbanks and component width recovery are independent of the
arithmetic algorithm that produced the stored rational parts. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost

theorem ids_mono {S T : Finset ℕ} (h:S⊆T) : ids S⊆ids T := by
  intro k hk
  rcases Finset.mem_union.mp hk with hp|hw
  · obtain ⟨i,hi,hk⟩:=Finset.mem_biUnion.mp hp
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,h hi,hk⟩)
  · exact Finset.mem_union_right _ hw

theorem widthBank_of_naturals (S : Finset ℕ) (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ)
    (agree:∀k∈ids S,n k=dataValues v k) (width:∀k∈ids S,(n k).bits.length≤B) : WidthBank S B v := by
  intro i hi
  have hp:positivePort i∈ids S:=cell_mem hi (by simp [cellPorts])
  have hn:negativePort i∈ids S:=cell_mem hi (by simp [cellPorts])
  have hd:denominatorPort i∈ids S:=cell_mem hi (by simp [cellPorts])
  have p:=width _ hp
  have n:=width _ hn
  have d:=width _ hd
  rw [agree _ hp,dataValues_positive] at p
  rw [agree _ hn,dataValues_negative] at n
  rw [agree _ hd,dataValues_denominator] at d
  exact ⟨p,n,d⟩

#print axioms widthBank_of_naturals
end Maxwell.Continuum.RationalDataflow
