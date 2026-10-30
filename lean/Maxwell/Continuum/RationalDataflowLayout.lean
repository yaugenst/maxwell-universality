import Maxwell.Continuum.RationalDataflowParts

/-! Shared logical registers and disjoint arithmetic scratch tapes. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 1500000

def positivePort (i : ℕ) : ℕ := 1000+3*i
def negativePort (i : ℕ) : ℕ := 1000+3*i+1
def denominatorPort (i : ℕ) : ℕ := 1000+3*i+2
def cellPorts (i : ℕ) : Finset ℕ := {positivePort i,negativePort i,denominatorPort i}
def ports (S : Finset ℕ) : Finset ℕ := S.biUnion cellPorts
def temporaryPorts : Finset ℕ := {100,101,102,103,104,105,106}
def workPorts : Finset ℕ := temporaryPorts∪RationalMagnitude.ids
def ids (S : Finset ℕ) : Finset ℕ := ports S∪workPorts
def workspace (S : Finset ℕ) : Finset ℕ := {0,1,2,3}∪ids S

def dataValues (v : ℕ→Parts) (i : ℕ) : ℕ :=
  if i<1000 then 0 else
    if (i-1000)%3=0 then (v ((i-1000)/3)).positive else
    if (i-1000)%3=1 then (v ((i-1000)/3)).negative else (v ((i-1000)/3)).denominator

def Ready (S : Finset ℕ) (v : ℕ→Parts) (s : Store) : Prop :=
  NatAssign.Bank (ids S) (dataValues v) s.val ∧ NatAssign.Scratch s.val

theorem positivePort_ge (i : ℕ) : 1000≤positivePort i := by unfold positivePort; omega
theorem negativePort_ge (i : ℕ) : 1000≤negativePort i := by unfold negativePort; omega
theorem denominatorPort_ge (i : ℕ) : 1000≤denominatorPort i := by unfold denominatorPort; omega

@[simp] theorem dataValues_positive (v : ℕ→Parts) (i : ℕ) : dataValues v (positivePort i)=(v i).positive := by
  have hg : ¬positivePort i<1000 := by have := positivePort_ge i; omega
  have hd : (positivePort i-1000)/3=i := by unfold positivePort; omega
  have hm : (positivePort i-1000)%3=0 := by unfold positivePort; omega
  simp [dataValues,hg,hd,hm]

@[simp] theorem dataValues_negative (v : ℕ→Parts) (i : ℕ) : dataValues v (negativePort i)=(v i).negative := by
  have hg : ¬negativePort i<1000 := by have := negativePort_ge i; omega
  have hd : (negativePort i-1000)/3=i := by unfold negativePort; omega
  have hm : (negativePort i-1000)%3=1 := by unfold negativePort; omega
  simp [dataValues,hg,hd,hm]

@[simp] theorem dataValues_denominator (v : ℕ→Parts) (i : ℕ) : dataValues v (denominatorPort i)=(v i).denominator := by
  have hg : ¬denominatorPort i<1000 := by have := denominatorPort_ge i; omega
  have hd : (denominatorPort i-1000)/3=i := by unfold denominatorPort; omega
  have hm : (denominatorPort i-1000)%3=2 := by unfold denominatorPort; omega
  simp [dataValues,hg,hd,hm]

theorem dataValues_small (v : ℕ→Parts) {i : ℕ} (hi : i<1000) : dataValues v i=0 := by
  simp only [dataValues,ite_eq_left hi]

theorem cell_mem {i : ℕ} {S : Finset ℕ} (hi : i∈S) : cellPorts i⊆ids S := by
  intro t ht
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,hi,ht⟩)

theorem ids_ge (S : Finset ℕ) (i : ℕ) (hi : i∈ids S) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with hp | hw
  · obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hp
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact (by omega : 4 ≤ 1000).trans (positivePort_ge r)
    · exact (by omega : 4 ≤ 1000).trans (negativePort_ge r)
    · exact (by omega : 4 ≤ 1000).trans (denominatorPort_ge r)
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hw
    omega

theorem dataValues_width (S : Finset ℕ) (v : ℕ→Parts) (B : ℕ)
    (hv : ∀ i∈S, (v i).Width B) (i : ℕ) (hi : i∈ids S) : (dataValues v i).bits.length≤B := by
  rcases Finset.mem_union.mp hi with hp | hw
  · obtain ⟨r,hr,ht⟩ := Finset.mem_biUnion.mp hp
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · simpa using (hv r hr).1
    · simpa using (hv r hr).2.1
    · simpa using (hv r hr).2.2
  · have hsmall : i<1000 := by
      simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hw
      omega
    simp [dataValues_small v hsmall]

theorem values_unchanged (ins : List NatAssign.Instruction) (v : ℕ→ℕ) (i : ℕ)
    (hi : ∀ a∈ins, a.target≠i) : NatAssign.values ins v i=v i := by
  induction ins generalizing v with
  | nil => rfl
  | cons a rest ih =>
    rw [NatAssign.values,ih (a.update v) (fun b hb => hi b (by simp [hb]))]
    exact Function.update_of_ne (hi a (by simp)).symm _ _

#print axioms dataValues_width
#print axioms values_unchanged

end Maxwell.Continuum.RationalDataflow
