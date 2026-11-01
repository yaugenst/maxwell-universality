import Maxwell.Continuum.SourceRoutingGeometryStartupPlan

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryStartup
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3200000
set_option maxRecDepth 20000

def code : Code := .seq (NatAssign.code instructions) (WordCopyAppend.code 718 1251 (List.replicate 12 false))
def inputWidth {q : ℕ} (h : GeometryHistory.Plan q) (backward : ℕ) : ℕ :=
  h.following.following.bound+h.width.bits.length+backward.bits.length+16
def cost {q : ℕ} (h : GeometryHistory.Plan q) (backward : ℕ) : ℕ :=
  2^74*(inputWidth h backward+3)^2

theorem initial_width {q : ℕ} (h : GeometryHistory.Plan q) (backward i : ℕ) :
    (initial h backward i).bits.length ≤ inputWidth h backward := by
  by_cases hi : i∈GeometryArithmetic.ids
  · have hs:=GeometrySort.seed_width (h.following.following.layer (2*q)) (2*q+1) 0 (Nat.zero_le _) i hi
    have bound:=h.following.following.layer_bound (2*q) le_rfl
    simp only [initial,hi,ite_true]
    exact hs.trans (bound.trans (by unfold inputWidth;omega))
  · simp only [initial,hi,ite_false]
    split_ifs
    · unfold inputWidth;omega
    · unfold inputWidth;omega
    · change 0≤_;omega

theorem initial_bank {q : ℕ} (h : GeometryHistory.Plan q) (backward : ℕ) (s : BitRAMState)
    (bank : NatAssign.Bank GeometryArithmetic.ids
      (GeometrySort.seed (h.following.following.layer (2*q)) (2*q+1) 0) s)
    (widthWord : Word s 711 h.width) (backwardWord : Word s 717 backward)
    (fresh : ∀i∈({1250,1252,1260}:Finset ℕ),Blank s i) :
    NatAssign.Bank ids (initial h backward) s := by
  intro i hi
  by_cases hg : i∈GeometryArithmetic.ids
  · simpa only [initial,hg,ite_true] using bank i hg
  have hp : i∈ports:=by simpa only [ids,Finset.mem_union,hg,false_or] using hi
  simp only [ports,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · simpa [initial,GeometryArithmetic.ids,controls,Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts] using widthWord
  · simpa [initial,GeometryArithmetic.ids,controls,Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts] using backwardWord
  all_goals simpa [initial,GeometryArithmetic.ids,controls,
    Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts] using
    (RationalAccumulator.zero_word_iff_blank _ _).mpr (fresh _ (by decide))

theorem executes {q : ℕ} (h : GeometryHistory.Plan q) (backward : ℕ)
    (start : h.base=backward+12*h.stride) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids
      (GeometrySort.seed (h.following.following.layer (2*q)) (2*q+1) 0) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (metadata : GeometrySort.Metadata (h.following.following.layer (2*q)) s.val)
    (backwardWord : Word s.val 717 backward)
    (fresh : ∀i∈({1250,1251,1252,1260}:Finset ℕ),Blank s.val i) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost h backward ∧
      NatAssign.Bank GeometryArithmetic.ids (GeometrySort.seed (h.layer 0) 1 0) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ GeometrySort.Metadata (h.layer 0) t.val ∧
      GeometryPath.OutputMetadata (outputWidth h) (outputBase h) (outputClock h) t.val ∧
      Word t.val 1260 backward ∧ BinaryPrecision.Frame work s.val t.val := by
  have lower (i : ℕ) (hi : i∈ids) : 4 ≤ i:=by
    rcases Finset.mem_union.mp hi with hi|hi
    · have hh:=GeometryArithmetic.ids_lower i hi;omega
    · simp only [ports,Finset.mem_insert,Finset.mem_singleton] at hi;omega
  obtain ⟨steps,a,he,hc,ba,za,fa⟩:=NatAssign.executes ids lower instructions valid (initial h backward)
    input tape s (initial_bank h backward s.val bank metadata.width backwardWord (fun i hi=>fresh i (by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢;tauto))) (scratch ready)
  have price:=NatAssign.price_bound ids instructions valid (initial h backward) (inputWidth h backward)
    (fun i _=>initial_width h backward i) (by
      simp [instructions,NatAssign.Instruction.literalWidth,inputWidth]
      change 4≤_
      omega)
  have framA : BinaryPrecision.Frame work s.val a.val:=fa.mono (by decide)
  have readyA : GeometryArray.Ready a.val:=
    ⟨⟨za 0 (by decide),za 1 (by decide),za 2 (by decide),za 3 (by decide),
      RationalAccumulator.blank_of_eq (framA.tapes 5 (by decide)) ready.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (framA.tapes 6 (by decide)) ready.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (framA.tapes 8 (by decide)) ready.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (framA.tapes 9 (by decide)) ready.scratch.2.2.2.2.2.2.2⟩,
      RationalAccumulator.blank_of_eq (framA.tapes 7 (by decide)) ready.seven,
      RationalAccumulator.blank_of_eq (framA.tapes 37 (by decide)) ready.pack⟩
  obtain ⟨t,et,clock,ft⟩:=WordCopyAppend.executes 718 1251 (by decide) input tape h.clock (List.replicate 12 false) a
    (BankArray.word_of_eq (framA.tapes 718 (by decide)) metadata.clock)
    (RationalAccumulator.blank_of_eq (fa.tapes 1251 (by decide)) (fresh 1251 (by decide)))
  have frame:=framA.trans (ft.mono (by decide))
  refine ⟨steps+(24*h.clock.length+10*(List.replicate 12 false).length+28),t,he.seq et,?_,?_,
    readyA.of_tapes (fun j hj=>ft.tapes j (by simp only [Finset.mem_singleton];omega)),
    RationalAccumulator.blank_of_eq ((ft.tapes 1249 (by decide)).trans (fa.tapes 1249 (by decide))) privateBlank,
    ⟨RationalAccumulator.word_of_eq (frame.tapes 711 (by decide)) metadata.width,
      BankArray.word_of_eq (frame.tapes 718 (by decide)) metadata.clock⟩,
    ⟨?_,?_,clock⟩,?_,frame⟩
  · have main:=hc.trans price
    change steps≤3000*8^18*(inputWidth h backward+2)^2 at main
    have width : h.clock.length ≤ inputWidth h backward:=by
      rw [h.clock_length]
      dsimp [inputWidth,GeometryHistory.Plan.bound,GeometryHistory.Plan.width]
      omega
    simp only [List.length_replicate]
    unfold cost
    nlinarith only [main,width]
  · intro i hi
    apply RationalAccumulator.word_of_eq (ft.tapes i (by
      have hlow:=GeometryArithmetic.ids_lower i hi
      simp only [GeometryArithmetic.ids,controls,Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
        Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
      simp only [Finset.mem_singleton];omega))
    rw [←values_seed h backward start i hi]
    exact ba i (Finset.mem_union_left _ hi)
  · exact RationalAccumulator.word_of_eq (ft.tapes 1250 (by decide))
      (by simpa only [(values_outputs h backward).1] using ba 1250 (by decide))
  · exact RationalAccumulator.word_of_eq (ft.tapes 1252 (by decide))
      (by simpa only [(values_outputs h backward).2.1] using ba 1252 (by decide))
  · exact RationalAccumulator.word_of_eq (ft.tapes 1260 (by decide))
      (by simpa only [(values_outputs h backward).2.2] using ba 1260 (by decide))

#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.GeometryStartup
