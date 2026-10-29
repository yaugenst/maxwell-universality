import Maxwell.Cost.NormalizeCoefficient.Correctness
import Maxwell.Cost.Structured.Rename

namespace Maxwell.Cost.NormalizeSource.Rhs
open Structured RationalAccumulator

def permutation : Equiv.Perm ℕ := (Equiv.swap 80 86).trans (Equiv.swap 81 87)

def normalizeCode : Code := .call (NormalizeCoefficient.code.compile.renameTapes permutation)

private theorem perm_other (i : ℕ) (h80 : i ≠ 80) (h81 : i ≠ 81) (h86 : i ≠ 86) (h87 : i ≠ 87) :
    permutation i = i ∧ permutation.symm i = i := by
  simp [permutation, Equiv.swap_apply_def, h80, h81, h86, h87]

/-- The same finite rounding kernel reads the saved source scale on 86/87.
The matrix scale on 80/81 is preserved by this static tape renaming. -/
theorem normalizes (input : List Bool) (tape : ℕ → Bool) (q : Codec.RationalPair)
    (scaleNum scaleDen precision B : ℕ) (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 →
      (NormalizeCoefficient.values q scaleNum scaleDen precision i).bits.length ≤ B)
    (s : Store) (hbank : Bank s.val (fun _ => 0)) (hready : Scratch s.val 0)
    (hfour : Blank s.val 4)
    (hnum : s.val.tapes 12 = BitTape.atEnd q.numerator.natAbs.bits)
    (hden : s.val.tapes 13 = BitTape.atEnd q.denominator.bits)
    (hsign : s.val.registers 23 = decide (q.numerator < 0))
    (hscaleN : Word s.val 86 scaleNum) (hscaleD : Word s.val 87 scaleDen)
    (hpower : Word s.val 82 (2^precision)) :
    ∃ cost, ∃ t : Store, cost ≤ 110000*(B+2)^2+1 ∧ Executes input tape normalizeCode cost s t ∧
      SignedRound.Output t.val (Logical.Rounding.nearest precision
        (q.value / ((scaleNum : ℚ)/scaleDen))).numerator ∧
      Bank t.val (fun _ => 0) ∧ Scratch t.val 0 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧
      NormalizeCoefficient.Frame s.val t.val := by
  let u := s.renameTapes permutation.symm
  have uk (i : ℕ) (h80 : i ≠ 80) (h81 : i ≠ 81) (h86 : i ≠ 86) (h87 : i ≠ 87) :
      u.val.tapes i = s.val.tapes i := by
    simp only [u, Store.renameTapes, BitRAMState.renameTapes, Equiv.symm_symm, Function.comp_apply,
      (perm_other i h80 h81 h86 h87).1]
  have ub : Bank u.val (fun _ => 0) := by
    intro i hi hj
    exact word_of_eq (uk i (by omega) (by omega) (by omega) (by omega)) (hbank i hi hj)
  have ur : Scratch u.val 0 :=
    ⟨blank_of_eq (uk 0 (by decide) (by decide) (by decide) (by decide)) hready.1,
      word_of_eq (uk 1 (by decide) (by decide) (by decide) (by decide)) hready.2.1,
      blank_of_eq (uk 2 (by decide) (by decide) (by decide) (by decide)) hready.2.2.1,
      blank_of_eq (uk 3 (by decide) (by decide) (by decide) (by decide)) hready.2.2.2⟩
  obtain ⟨c, v, hc, ev, hvout, hvb, hvr, hv12, hv13, hvf⟩ := NormalizeCoefficient.normalizes
    input tape q scaleNum scaleDen precision B hscaleNum hscaleDen hbits u ub ur
    (blank_of_eq (uk 4 (by decide) (by decide) (by decide) (by decide)) hfour)
    ((uk 12 (by decide) (by decide) (by decide) (by decide)).trans hnum)
    ((uk 13 (by decide) (by decide) (by decide) (by decide)).trans hden) hsign
    (by simpa [u, Store.renameTapes, BitRAMState.renameTapes, permutation, Equiv.swap_apply_def, Word] using hscaleN)
    (by simpa [u, Store.renameTapes, BitRAMState.renameTapes, permutation, Equiv.swap_apply_def, Word] using hscaleD)
    (word_of_eq (uk 82 (by decide) (by decide) (by decide) (by decide)) hpower)
  let t := v.renameTapes permutation
  have tk (i : ℕ) (h80 : i ≠ 80) (h81 : i ≠ 81) (h86 : i ≠ 86) (h87 : i ≠ 87) :
      t.val.tapes i = v.val.tapes i := by
    simp only [t, Store.renameTapes, BitRAMState.renameTapes, Function.comp_apply,
      (perm_other i h80 h81 h86 h87).2]
  refine ⟨c+1, t, by omega, ?_, ?_, ?_, ?_,
    (tk 12 (by decide) (by decide) (by decide) (by decide)).trans hv12,
    (tk 13 (by decide) (by decide) (by decide) (by decide)).trans hv13, ?_⟩
  · simpa only [u, t, normalizeCode, Store.renameTapes_symm] using ev.renamed_call permutation
  · obtain ⟨origin, ho, hs⟩ := hvout
    exact ⟨origin, (tk 4 (by decide) (by decide) (by decide) (by decide)).trans ho, hs⟩
  · intro i hi hj
    exact word_of_eq (tk i (by omega) (by omega) (by omega) (by omega)) (hvb i hi hj)
  · exact ⟨blank_of_eq (tk 0 (by decide) (by decide) (by decide) (by decide)) hvr.1,
      word_of_eq (tk 1 (by decide) (by decide) (by decide) (by decide)) hvr.2.1,
      blank_of_eq (tk 2 (by decide) (by decide) (by decide) (by decide)) hvr.2.2.1,
      blank_of_eq (tk 3 (by decide) (by decide) (by decide) (by decide)) hvr.2.2.2⟩
  · refine ⟨hvf.1, hvf.2.1, hvf.2.2.1, hvf.2.2.2.1, hvf.2.2.2.2.1, ?_, hvf.2.2.2.2.2.2⟩
    intro i hi h12 h13 hb
    have hp (j : ℕ) (hj : j = permutation.symm i) :
        5 ≤ j ∧ j ≠ 12 ∧ j ≠ 13 ∧ (j < 30 ∨ 36 < j) := by
      subst j
      simp only [permutation, Equiv.symm_trans_apply, Equiv.symm_swap, Equiv.swap_apply_def]
      split_ifs <;> omega
    have hh := hp (permutation.symm i) rfl
    have ht := hvf.2.2.2.2.2.1 (permutation.symm i) hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
    simpa only [t, u, Store.renameTapes, BitRAMState.renameTapes, Equiv.symm_symm,
      Function.comp_apply, Equiv.apply_symm_apply] using ht

end Maxwell.Cost.NormalizeSource.Rhs
