import Maxwell.Continuum.ParameterOuterInitialData

namespace Maxwell.Continuum.Parameters.OuterInitial
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

theorem executes (v : ℕ→ℕ) (B : ℕ) (hℓ : 0<v 2200)
    (hw : ∀ i∈ids,(v i).bits.length≤B)
    (input : List Bool) (randomTape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input randomTape code cost s t ∧ cost≤costBound v B ∧
      NatAssign.Bank ids (result v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀ i∈ids,(result v i).bits.length≤searchWidth v B) ∧
      Word t.val 2206 (initialExponent (v 2201) (v 2200)) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨pc,u,ep,hp,bu,su,fu⟩ := NatAssign.executes ids ids_ge setup setup_valid v input randomTape s hb hs
  have hp' : pc≤3000*8^setup.length*(B+3)^2 := by
    have hh := NatAssign.price_bound ids setup setup_valid v (B+1)
      (fun i hi => (hw i hi).trans (by omega)) (by
        simp [setup,GeometricAdapter.clearGeo,Rational.clear,NatAssign.Instruction.literalWidth])
    simpa only [Nat.add_assoc] using hp.trans hh
  have bu' : NatAssign.Bank (Rational.ids extra) (prepared v) u.val :=
    fun i hi => bu i (Finset.mem_union_left _ hi)
  have wu : ∀ i∈Rational.ids extra,(prepared v i).bits.length≤preparedWidth B :=
    fun i hi => prepared_width v B hw i (Finset.mem_union_left _ hi)
  have zu : ∀ i∈Geometric.extra,Blank u.val i := by
    intro i hi
    have hu := bu i (Finset.mem_union_right _ hi)
    change Word u.val i (prepared v i) at hu
    rw [prepared_zero v i (Finset.mem_union_left _ hi)] at hu
    exact (RationalAccumulator.zero_word_iff_blank _ _).mp hu
  obtain ⟨_,_,h2,h3⟩ := prepared_fields v
  have eg := GeometricAdapter.executes extra extra_ge 1 8 2202 2203 2204 2205
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (prepared v) 4 (preparedWidth B) (by decide) (by decide)
    (by rw [h2];decide) (by rw [h3];positivity) wu input randomTape u bu' su zu
  simp only [h2,h3,Geometric.exponent_eq_clog] at eg
  obtain ⟨gc,a,eg,hg,ba,sa,za,wa,fa⟩ := eg
  change NatAssign.Bank (Rational.ids extra) (searched v) a.val at ba
  change ∀ i∈Rational.ids extra,(searched v i).bits.length≤searchWidth v B at wa
  have hsa := searched_fields v
  obtain ⟨cc,t,ec,hc,bt,st,ft⟩ := Rational.choice_executes extra extra_ge .maximum
    2201 2202 2204 2205 2206 2207 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (searched v) (searchWidth v B) wa
    (by rw [hsa.2.1];decide) (by rw [hsa.2.2.2];decide)
    (Rational.after_common _ _ _ _ 35 (by decide))
    (Rational.after_common _ _ _ _ 36 (by decide)) input randomTape a ba sa
  rw [chosen] at bt
  change NatAssign.Bank (Rational.ids extra) (result v) t.val at bt
  have wchoice := Rational.choice_width .maximum (searched v 2201) (searched v 2202)
    (searched v 2204) (searched v 2205) (searchWidth v B)
    (wa 2201 (by decide)) (wa 2202 (by decide)) (wa 2204 (by decide)) (wa 2205 (by decide))
  rw [chosen] at wchoice
  have wt : ∀ i∈Rational.ids extra,(result v i).bits.length≤searchWidth v B :=
    Rational.after_width extra (searched v) 2206 2207 _ _ _ wa le_rfl wchoice
  have zresult (i : ℕ) (hi : i∈Geometric.extra) : result v i=0 := by
    have hz := prepared_zero v i (Finset.mem_union_left _ hi)
    simp only [Geometric.extra,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simpa [result,searched,Rational.after,Rational.common] using hz
  have zt (i : ℕ) (hi : i∈Geometric.extra) : Blank t.val i := by
    apply RationalAccumulator.blank_of_eq (ft.tapes i ?_) (za i (Finset.mem_union_left _ hi))
    simp only [Geometric.extra,Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [Rational.workspace,Rational.common,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  refine ⟨pc+(gc+cc),t,ep.seq (eg.seq ec),Nat.add_le_add hp' (Nat.add_le_add hg hc),?_,st,?_,?_,
    (fu.mono (by decide +kernel)).trans
      ((fa.mono (by decide +kernel)).trans (ft.mono (by decide +kernel)))⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact bt i hi
    · rw [zresult i hi]
      exact (RationalAccumulator.zero_word_iff_blank _ _).mpr (zt i hi)
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact wt i hi
    · simp [zresult i hi]
  · simpa [result,Rational.after,Rational.common] using bt 2206 (by decide)

#print axioms executes

end Maxwell.Continuum.Parameters.OuterInitial
