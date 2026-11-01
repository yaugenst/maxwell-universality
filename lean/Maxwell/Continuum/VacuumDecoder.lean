import Maxwell.Continuum.CompleteDecoder
import Maxwell.Continuum.Main
import Maxwell.Cost.FiniteDecoder.Words
import Maxwell.Codec.OutputWidth
import Maxwell.Codec.RationalShort

/-! The same complete decoder executes the zero-source format with no samples.
Its cost is linear in the output dimension up to three binary-length factors. -/

namespace Maxwell.Continuum.VacuumDecoder
open Maxwell.Cost.DecoderParser Maxwell.Continuum.Realization
set_option maxRecDepth 4096

theorem offset_short (S : Source.SparseSystem) (B : ℕ) (hB : 1≤B) (i : Fin S.n) :
    Source.ShortRational B ((vacuumDecoder S).offset i) := by
  exact Source.ShortRational.mono Source.ShortRational.zero (by exact_mod_cast hB)

theorem output_width (S : Source.SparseSystem) :
    decoderWidth (vacuumDecoder S)+2≤4 := by
  have h := decoderWidth_bound (vacuumDecoder S) 1 0
    (offset_short S 1 le_rfl) (by intro i j;exact Fin.elim0 j)
    (by intro i; simp [vacuumDecoder])
  omega

theorem description_length (S : Source.SparseSystem) :
    (Cost.FiniteDecoder.description (vacuumDecoder S)).length≤16*(S.n+1)*(S.n.bits.length+2) := by
  have h := Cost.FiniteDecoder.description_length (vacuumDecoder S) (S.n.bits.length+1) 0
    (by omega) (by simp [vacuumDecoder]) (by simp [vacuumDecoder]) (by simp [vacuumDecoder])
    (by simp) (offset_short S _ (by omega))
    (by intro i j;exact Fin.elim0 j) (by intro i;simp [vacuumDecoder])
  simpa only [Nat.zero_add,Nat.mul_one,Nat.add_assoc] using h

theorem cost_le (S : Source.SparseSystem) :
    CompleteDecoder.vacuumCost (vacuumDecoder S)+1≤
      500000000*(S.n+1)*(S.n.bits.length+2)^3 := by
  have hw := Cost.FiniteDecoder.description_width (vacuumDecoder S) (S.n.bits.length+1) 0
    (by omega) (by simp [vacuumDecoder]) (by simp [vacuumDecoder]) (by simp [vacuumDecoder])
    (by simp) (offset_short S _ (by omega))
    (by intro i j;exact Fin.elim0 j) (by intro i;simp [vacuumDecoder])
  have hc := Cost.FiniteDecoder.costCap_bounded (vacuumDecoder S) (S.n.bits.length+1) 0 hw
    (by simp [vacuumDecoder,Target.FixedPointFormat.width])
    (by simp [vacuumDecoder]) (by simp [vacuumDecoder])
    (offset_short S _ (by omega)) (by intro i j;exact Fin.elim0 j)
    (by intro i;simp [vacuumDecoder])
  change Cost.FiniteDecoder.costCap (vacuumDecoder S)≤320000*
    ((Cost.FiniteDecoder.description (vacuumDecoder S)).length+1)*49*(S.n.bits.length+2)^2 at hc
  have hd := description_length S
  have hb : 1≤(S.n+1)*(S.n.bits.length+2) := by nlinarith
  have hbound : (Cost.FiniteDecoder.description (vacuumDecoder S)).length+1≤
      17*(S.n+1)*(S.n.bits.length+2) := by nlinarith only [hd,hb]
  have hc' := hc.trans (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 320000 hbound)))
  have hp : 1≤(S.n+1)*(S.n.bits.length+2)^3 :=
    Nat.mul_pos (by omega) (pow_pos (by omega) _)
  unfold CompleteDecoder.vacuumCost
  nlinarith only [hc',hp]

theorem decodes (S : Source.SparseSystem) (C : Constants) (hC : 4≤C.wordCoefficient) :
    Decodes CompleteDecoder.program (vacuumBytes S) (vacuumDecoder S) (wordBudget C S)
      (CompleteDecoder.vacuumCost (vacuumDecoder S)+1) := by
  intro w
  obtain ⟨stop,he,ho,hr⟩ := CompleteDecoder.vacuum_run (vacuumDecoder S) w (fun _ => false)
  have hl : 1≤Parameters.inputLog S.nnz := Parameters.inputLog_pos S.nnz
  have hw : decoderWidth (vacuumDecoder S)+2≤wordBudget C S :=
    (output_width S).trans (hC.trans (Nat.le_mul_of_pos_right _ hl))
  refine ⟨stop,?_,ho.mono hw,hr⟩
  simpa only [vacuumBytes,List.cons_append] using he

#print axioms cost_le
#print axioms decodes

end Maxwell.Continuum.VacuumDecoder
