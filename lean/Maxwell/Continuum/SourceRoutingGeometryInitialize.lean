import Maxwell.Continuum.SourceRoutingGeometryStartupMachine

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryStartup
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2600000
set_option maxRecDepth 20000

def freshPorts : Finset ℕ := {1242,1250,1251,1252,1253,1255,1256,1257,1258,1260}

theorem prepares {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)
    (h : GeometryHistory.Plan (2*half)) (backward : ℕ)
    (start : h.base=backward+12*h.stride) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (runtime : GeometryHistory.Runtime h.following.following (PhaseKeys.last data.colors) (2*(2*half)) s)
    (backwardWord : Word s.val 717 backward)
    (first : GeometryHistory.Stored h (PhaseKeys.first data.colors) (2*(2*half)) s.val.memory)
    (second : GeometryHistory.Stored h.following (PhaseKeys.middle data.colors) (2*(2*half)) s.val.memory)
    (inverse : BitArray.Represents s.val.memory backward h.width
      (IncidenceEncoding.words h.width (GeometryPhase.targets data.target.symm)))
    (fresh : ∀i∈freshPorts,Blank s.val i) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost h backward ∧
      GeometryEmission.State data (plan h backward start) 0 0 t ∧ Blank t.val 1258 ∧
      BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨steps,t,he,hc,bank,ready,privateBlank,metadata,output,backwardWord',frame⟩:=
    executes h backward start input tape s runtime.bank runtime.ready runtime.privateBlank runtime.metadata
      backwardWord (fun i hi=>fresh i (by
        simp only [freshPorts,Finset.mem_insert,Finset.mem_singleton] at hi ⊢;tauto))
  have blank (j : ℕ) (hj : j∈freshPorts) (outside : j∉work) : Blank t.val j:=
    RationalAccumulator.blank_of_eq (frame.tapes j outside) (fresh j hj)
  have zero (j : ℕ) (hj : j∈freshPorts) (outside : j∉work) : Word t.val j 0:=
    (RationalAccumulator.zero_word_iff_blank _ _).mpr (blank j hj outside)
  have archive : GeometryEmission.Archive data (plan h backward start) t.val:=by
    refine ⟨metadata,output,backwardWord',?_,?_,?_,?_⟩
    all_goals rw [frame.memory]
    · exact first
    · exact second
    · exact runtime.stored
    · exact inverse
  exact ⟨steps,t,he,hc,⟨⟨⟨0,Nat.mul_pos h.positive h.positive⟩,bank⟩,ready,privateBlank,archive,
    zero 1255 (by decide) (by decide),zero 1253 (by decide) (by decide),zero 1257 (by decide) (by decide),
    blank 1242 (by decide) (by decide),blank 1256 (by decide) (by decide)⟩,
    blank 1258 (by decide) (by decide),frame⟩

#print axioms prepares
end Maxwell.Cost.RoutingPorts.Complete.GeometryStartup
