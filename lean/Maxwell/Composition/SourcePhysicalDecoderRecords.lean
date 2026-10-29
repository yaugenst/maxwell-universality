import Maxwell.Composition.SourcePhysicalDecoder
import Maxwell.Composition.SourceEnumeration
import Maxwell.Codec.Target

/-! Exact encoder order and right-block terminal selection for the physical
decoder. These identities concern the decoder emitted by the construction. -/
noncomputable section
namespace Maxwell.Composition.SourcePhysicalDecoderRecords
open Maxwell.Logical

theorem selected_index (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    (SourceEnumeration.vertexEquiv S precision (SourcePositive.inputCoordinate S precision i)).val =
      (sourceCircuit S precision).size+i.val := by
  simp only [SourcePositive.inputCoordinate,SourceEnumeration.vertexEquiv,
    Equiv.trans_apply,Equiv.sumCongr_apply]
  change (sourceCircuit S precision).size+((sourceCircuit S precision).circuit.inputIndex i).val = _
  rw [(sourceCircuit S precision).circuit.inputIndex_value]

theorem support_sort {m k : ℕ} (i : Fin m) :
    ((Finset.univ.image fun j : Fin k => finProdFinEquiv (i,j)).sort) =
      List.ofFn (fun j : Fin k => finProdFinEquiv (i,j)) := by
  let f : Fin k ↪ Fin (m*k) := ⟨fun j => finProdFinEquiv (i,j),by
    intro a b h
    exact (Prod.mk.inj (finProdFinEquiv.injective h)).2⟩
  have hs : ∀ a ∈ (Finset.univ : Finset (Fin k)), ∀ b ∈ (Finset.univ : Finset (Fin k)),
      a ≤ b ↔ f a ≤ f b := by
    intro a _ b _
    change a.val ≤ b.val ↔ a.val+k*i.val ≤ b.val+k*i.val
    omega
  have h := Finset.map_sort (s := Finset.univ) (r := (· ≤ ·)) (r' := (· ≤ ·)) f hs
  rw [Fin.sort_univ] at h
  rw [List.ofFn_eq_map]
  rw [Finset.map_eq_image] at h
  change (List.finRange k).map (fun j => finProdFinEquiv (i,j)) =
    (Finset.univ.image (fun j => finProdFinEquiv (i,j))).sort at h
  exact h.symm

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : P.spacing.minimumDistance ≤ d)
variable (qhat : SourcePhysicalDecoder.Local P → ℚ)
variable (v : SourceDecoration.Vertex S precision → ℚ) (format : Target.FixedPointFormat)

theorem row (i : Fin S.n) :
    Codec.decoderRowRecord (SourcePhysicalDecoder.decoder P S precision d ζ hζ hζ1 hd qhat v format) i =
      ⟨0,List.ofFn (fun j : SourcePhysicalDecoder.Local P =>
        (j.val+(Maxwell.Defect.ScalarDefect.edges P.defect).card*i.val,
          (Normalization.sourceScale S/Normalization.matrixScale S)*
            (v (SourcePhysicalDecoder.vertex S precision i)*qhat j)))⟩ := by
  unfold Codec.decoderRowRecord SourcePhysicalDecoder.decoder selectScaleDecoder
    SourcePhysicalDecoder.unscaled localModeDecoder
  simp only [id_eq,mul_zero,support_sort,List.map_ofFn]
  congr 2
  funext j
  dsimp only [Function.comp_def]
  rw [Equiv.symm_apply_apply]
  rfl

theorem row_encoding (i : Fin S.n) :
    let D := SourcePhysicalDecoder.decoder P S precision d ζ hζ hζ1 hd qhat v format
    Codec.rat (D.offset i) ++
      Codec.list (fun j => Codec.nat j.val ++ Codec.rat (D.weight i j)) ((D.support i).sort) =
    Codec.rat 0 ++ Codec.nat (Maxwell.Defect.ScalarDefect.edges P.defect).card ++
      (List.ofFn (fun j : SourcePhysicalDecoder.Local P =>
        Codec.nat (j.val+(Maxwell.Defect.ScalarDefect.edges P.defect).card*i.val) ++
          Codec.rat ((Normalization.sourceScale S/Normalization.matrixScale S)*
            (v (SourcePhysicalDecoder.vertex S precision i)*qhat j)))).flatten := by
  dsimp only
  unfold SourcePhysicalDecoder.decoder selectScaleDecoder SourcePhysicalDecoder.unscaled localModeDecoder
  simp only [id_eq,mul_zero,support_sort,Codec.list,List.length_ofFn]
  rw [List.flatMap, List.map_ofFn]
  rw [List.append_assoc]
  congr 4
  funext j
  dsimp only [Function.comp_def]
  rw [Equiv.symm_apply_apply]
  rfl

end Maxwell.Composition.SourcePhysicalDecoderRecords
