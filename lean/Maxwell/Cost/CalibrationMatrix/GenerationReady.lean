import Maxwell.Cost.CalibrationMatrix.GenerationData

namespace Maxwell.Cost.CalibrationMatrix.Generation
open Structured BankArray
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

def matrix (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) :=
  integerMatrix (stencilMatrix (radixCubeEmbedding R) (rationalEdgeAverage material) z) D

def readyCode (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) : Code :=
  .seq GeneratedCoordinates.code (GeneratedEntry.code material z D)

/-- Generate the exact signed integer matrix entry directly from the live
row-major cursor and the fixed finite material table. -/
theorem generate_ready (input : List Bool) (tape : ℕ → Bool) (R : ℕ)
    (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) (d : Data R)
    (i j : Fin (3*cubeWidth R^3)) (index : List Bool)
    (hindex : addressValue index = i.val*(3*cubeWidth R^3)+j.val)
    (hfit : d.radix.length+d.dimension.length+index.length+1 ≤ addressValue d.width)
    (s : Store) (hs : Stored d index s.val) (hb : Workspace s.val) :
    ∃ cost t, cost ≤ 5000*(d.radix.length+d.dimension.length+index.length+3)^2+
        GeneratedEntry.costCap material z D (addressValue d.width) ∧
      Executes input tape (readyCode material z D) cost s t ∧
      Ready t.val (dotValues ((matrix R material z D).positive i j)
        ((matrix R material z D).negative i j)) ∧
      (∀ k ∈ work, k ≠ 30 → k ≠ 31 → Blank t.val k) ∧
      t.val.memory = s.val.memory ∧ Frame s.val t.val := by
  obtain ⟨a,m,raw,direction,hca,ea,hop,hrd,hcd,hredge,hcedge,hrlen,hdlen,hmblank,hf⟩ :=
    GeneratedCoordinates.executes input tape R i j d.radix d.dimension index
      d.radix_value d.dimension_value hindex s hs.radix hs.dimension hs.index
      (fun k hk => hb k (Finset.mem_union_left _ (Finset.mem_union_left _ hk)))
  have baseBlank (k : ℕ) (hk : k ∈ work) (hout : k ∉ GeneratedCoordinates.work) : Blank m.val k :=
    hf.blank hout (hb k hk)
  have banks := GeneratedCoordinates.initial_banks d.clock raw direction m
    (hf.word (by decide) hs.clock) hop (by
      intro k hk h101 hraw
      have hout : k ∉ GeneratedCoordinates.work := by
        have hh : (TestInputs.domain \ {101}) ∩ GeneratedCoordinates.work ⊆
            GeneratedCoordinates.rawBanks := by decide
        intro hin
        exact hraw (hh (by simp [hk,h101,hin]))
      apply baseBlank k _ hout
      have hh : TestInputs.domain \ {101} ⊆ work := by decide
      exact hh (by simp [hk,h101]))
  have hraw : ∀ k, (raw k).length+1 ≤ addressValue d.width := fun k => by have := hrlen k; omega
  have hdir : direction.length ≤ addressValue d.width := by omega
  have workBlank : HeaderCoordinate.WorkBlank m.val := by
    intro k hk hk'
    exact baseBlank k (by simp [work]; omega) (by simp [GeneratedCoordinates.work,GeneratedCoordinates.rawBanks]; omega)
  have scratchBlank : HeaderCoordinate.ScratchBlank m.val := by
    intro k hk
    exact hmblank k (by simp [GeneratedCoordinates.work]; omega)
      (by simp [GeneratedCoordinates.rawBanks]; omega)
  obtain ⟨b,t,hcb,eb,hready,hclean,htwork,ht135,htscratch,ht90,hg⟩ :=
    GeneratedEntry.executes material z D R (addressValue d.width) d.clock direction raw
      d.width_two d.clock_length hraw hdir (radixCubeEmbedding R i).1
      (radixCubeEmbedding R j).1 hrd hcd input tape m banks hop.2.2.2.2.2.2.2
      (hf.word (by decide) hs.residue) (hf.word (by decide) hs.clock2)
      (hf.word (by decide) hs.clock5) (hf.word (by decide) hs.twenty)
      workBlank (baseBlank 135 (by decide) (by decide)) scratchBlank
      (baseBlank 90 (by decide) (by decide))
      (fun k hk hk' => baseBlank k (by simp [work]; omega)
        (by simp [GeneratedCoordinates.work,GeneratedCoordinates.rawBanks]; omega))
  have exactPair := entryChannels_binding (radixCubeEmbedding R) material z D i j
  rw [hredge,hcedge,exactPair] at hready
  refine ⟨a+b,t,by omega,ea.seq eb,hready,?_,hg.memory.trans hf.memory,?_⟩
  · intro k hk h30 h31
    by_cases hs : k < 10
    · exact htscratch k hs
    by_cases hc : k ∈ GeneratedCleanup.banks
    · exact hclean k hc
    by_cases hw : 80 ≤ k ∧ k ≤ 86
    · exact htwork k hw.1 hw.2
    by_cases h135 : k = 135
    · subst k; exact ht135
    by_cases h90 : k = 90
    · subst k; exact ht90
    have hremain : k = 37 ∨ k = 70 ∨ k = 71 ∨ k = 72 ∨ k = 123 ∨ k = 124 ∨ (32 ≤ k ∧ k ≤ 36) := by
      simp only [work,GeneratedCoordinates.work,GeneratedCoordinates.rawBanks,
        GeneratedCleanup.banks,List.mem_toFinset,Finset.mem_union,Finset.mem_range,
        Finset.mem_insert,Finset.mem_singleton,List.mem_cons,List.not_mem_nil,or_false] at hk hc
      omega
    apply RationalAccumulator.blank_of_eq (hg.tapes k (by omega) ?_)
    · by_cases hcoord : k ∈ GeneratedCoordinates.work
      · exact hmblank k hcoord (by simp [GeneratedCoordinates.rawBanks]; omega)
      · exact baseBlank k hk hcoord
    · have hh : ∀ q ∈ ({37,70,71,72,123,124,32,33,34,35,36} : Finset ℕ), q ∉ GeneratedEntry.changes := by decide
      apply hh k
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
  · refine ⟨hg.inputHead.trans hf.inputHead,hg.randomCursor.trans hf.randomCursor,
      hg.output.trans hf.output,?_⟩
    intro k hk
    have hcoord : k ∉ GeneratedCoordinates.work := fun h => hk
      (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hgen : k ∉ GeneratedEntry.changes := by
      have hh : GeneratedEntry.changes ⊆ work := by decide
      exact fun h => hk (hh h)
    have hlow : 3 ≤ k := by
      have hh : Finset.range 10 ⊆ work := by decide
      by_contra hn
      exact hk (hh (by simp; omega))
    exact (hg.tapes k hlow hgen).trans (hf.tapes k hcoord)

end Maxwell.Cost.CalibrationMatrix.Generation
