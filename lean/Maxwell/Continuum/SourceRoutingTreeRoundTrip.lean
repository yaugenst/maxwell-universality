import Maxwell.Continuum.SourceRoutingAssemblyStart
import Maxwell.Continuum.SourceRoutingAssemblyInitial

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.RoundTrip
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000

def reverseValues (v : ℕ→ℕ) (total : ℕ) : ℕ→ℕ :=
  AssemblyStart.output (Traversal.values v (total-1))
def code : Code := .seq Traversal.loadedCode (.seq AssemblyStart.code AssemblyTraversal.loadedCode)
def cost (heap rows total : ℕ) : ℕ :=
  Traversal.cost heap rows total+44*total.bits.length+48+
    2^102*(Traversal.width heap rows total+2)^2+
    AssemblyTraversal.cost heap rows total+15*total.bits.length+17

theorem reverse_setup (v : ℕ→ℕ) (heap rows total : ℕ) (setup : Traversal.Setup v heap rows total) :
    AssemblyTraversal.Setup (reverseValues v total) heap rows total := by
  have hp : total-1+1=total := by have ht:=setup.positive;omega
  have coords:=Traversal.coordinates v heap (2^(total+rows)) (total+rows+1) rows total
    setup.coordinates (total-1) (by omega)
  simp only [hp,Nat.sub_self,Nat.zero_add] at coords
  have pop:=Traversal.population v setup.population setup.coordinates.two (total-1)
  rw [hp] at pop
  refine ⟨setup.positive,
    AssemblyStart.coordinates _ _ _ _ rows total setup.positive coords,
    AssemblyStart.population _ total setup.positive pop.1 pop.2,
    AssemblyStart.zero _ (Traversal.quotient_zero v setup.zero (total-1)),?_⟩
  have words:=AssemblyStart.words _ (Traversal.width heap rows total)
    (Traversal.words v heap rows total setup.coordinates setup.population setup.words (total-1) (by omega))
  intro i hi
  exact (words i hi).trans (by
    dsimp only [Traversal.width,AssemblyTraversal.width,AssemblyTraversal.baseWidth,
      Level.uniformWidth,AssemblyLevel.uniformWidth]
    omega)

theorem reverse_depth (v : ℕ→ℕ) (total : ℕ) (hdepth : v 810=total) :
    reverseValues v total 810=total := by
  have keep (d : ℕ) : Traversal.values v d 810=v 810 := by
    induction d with
    | zero => rfl
    | succ d ih =>
        exact (Level.Advance.output_other _ 810 (by decide)).trans
          ((Level.values_other _ _ 810 (by decide)).trans ih)
  exact (AssemblyStart.output_other _ 810 (by decide)).trans ((keep _).trans hdepth)

theorem executes (v : ℕ→ℕ) (heap rows total : ℕ) (root : Targets.Target rows total)
    (setup : Traversal.Setup v heap rows total) (depth : v 810=total)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank Division.ids v s.val) (hz : PrivateVisit.Clean s)
    (h839 : Blank s.val 839) (h831 : Blank s.val 831) (h830 : Blank s.val 830)
    (outputs : Traversal.Prefix heap rows total root 1 s.val.memory)
    (leaves : AssemblyTraversal.Frontier heap rows total root 0 s.val.memory) :
    ∃steps t,Executes input tape code steps s t ∧ steps ≤ cost heap rows total ∧
      AssemblyTraversal.State (reverseValues v total) heap rows total root total s.val t ∧ Blank t.val 830 := by
  have initial : Traversal.State v heap rows total root 0 s.val s :=
    ⟨hb,hz,h839,h831,outputs,Traversal.Frame.refl _,Memory.Frame.refl _ _ _⟩
  obtain ⟨c0,a,e0,h0,sa,a830⟩:=Traversal.loaded_executes v heap rows total root setup depth input tape
    s.val s initial h830
  have hp : total-1+1=total := by have ht:=setup.positive;omega
  have pop:=Traversal.population v setup.population setup.coordinates.two (total-1)
  obtain ⟨c1,b,e1,h1,bb,zb,b839,f1⟩:=AssemblyStart.executes (Traversal.values v (total-1))
    (Traversal.width heap rows total) pop.2 (Traversal.quotient_zero v setup.zero (total-1))
    (Traversal.words v heap rows total setup.coordinates setup.population setup.words (total-1) (by omega))
    input tape a sa.bank sa.clean sa.scratch
  have leavesA:=AssemblyTraversal.Frontier.preserve heap rows total root s.val.memory a.val.memory sa.memory leaves
  have initialReverse : AssemblyTraversal.State (reverseValues v total) heap rows total root 0 s.val b := by
    refine ⟨bb,zb,b839,RationalAccumulator.blank_of_eq (f1.tapes 831 (by decide)) sa.counter,?_,?_,
      sa.frame.trans (Traversal.Frame.of_level (Level.Frame.of_arithmetic f1)),?_⟩
    · simpa only [Nat.sub_zero,f1.memory,hp] using sa.outputs
    · simpa only [f1.memory] using leavesA
    · simpa only [f1.memory] using sa.memory
  have b830:=RationalAccumulator.blank_of_eq (f1.tapes 830 (by decide)) a830
  obtain ⟨c2,t,e2,h2,st,t830⟩:=AssemblyTraversal.loaded_executes (reverseValues v total) heap rows total root
    (reverse_setup v heap rows total setup) (reverse_depth v total depth) input tape s.val b initialReverse b830
  exact ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),by dsimp only [cost];omega,st,t830⟩

#print axioms reverse_setup
#print axioms executes
end Maxwell.Cost.RoutingPorts.Complete.Tree.RoundTrip
