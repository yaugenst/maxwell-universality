import Maxwell.Cost.SplitNode.Common
import Maxwell.Cost.ChildPermutation.Public

namespace Maxwell.Cost.SplitNode
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

/-- One fixed finite program computes the colors and both child permutations. -/
def code : Code := .seq BinarySplit.code (.seq ChildPermutation.prepareCode ChildPermutation.passCode)

def costCap (layout : Layout) (k : ℕ) (clock : List Bool) : ℕ :=
  BinarySplit.costCap layout.split (2*(2^k)) clock +
    (ChildPermutation.prepareCost (layout.child (2*(2^k))) k clock +
      ChildPermutation.passCost (layout.child (2*(2^k))) k)

theorem executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (data : ChildPermutation.Data k) (clock : List Bool)
    (hcolors : data.colors=BinarySplit.colors k data.target)
    (hw : layout.split.route.width=k+2) (hc : clock.length=layout.split.route.width)
    (hs : layout.split.Separated (2*(2^k))) (hcs : (layout.child (2*(2^k))).Separated k)
    (s : Store) (hn : Word s.val 96 (2*(2^k)).bits)
    (h94 : Blank s.val 94) (h95 : Blank s.val 95) (h97 : Blank s.val 97)
    (cfg : DoublingInit.Config layout.split.half [] clock s.val)
    (saved : BinarySplit.Saved layout.split s.val) (work : DoublingInit.Workspace s.val)
    (hf : BitArray.Represents s.val.memory layout.split.forward layout.split.route.width
      (DoublingPass.words layout.split.route.width (Vector.ofFn data.target)))
    (hb : BitArray.Represents s.val.memory layout.split.backward layout.split.route.width
      (DoublingPass.words layout.split.route.width (Vector.ofFn data.target.symm)))
    (bases : ∀ i : Fin 4, Word s.val (122+i.val) (layout.childBases i).bits)
    (h87 : Blank s.val 87) (h120 : Blank s.val 120) (h121 : Blank s.val 121)
    (h126 : Blank s.val 126) (h127 : Blank s.val 127) (h128 : Blank s.val 128) :
    ∃ cost t childClock, cost≤costCap layout k clock ∧ Executes input tape code cost s t ∧
      ChildPermutation.Config (layout.child (2*(2^k))) [] clock childClock t.val ∧
      childClock.length=(layout.child (2*(2^k))).childWidth ∧
      ChildPermutation.Workspace t.val ∧ Blank t.val 126 ∧
      ChildPermutation.Represents (layout.child (2*(2^k))) t.val.memory data
        (ChildPermutation.finalOutputs (layout.child (2*(2^k))).childWidth data) ∧
      Word t.val 96 (2*(2^k)).bits ∧ BinarySplit.Saved layout.split t.val ∧
      Frame s.val t.val ∧ MemoryFrame layout k s.val.memory t.val.memory := by
  obtain ⟨ac,a,hac,ea,acfg,awork,a94,a95,a97,an,asaved,acolors,af,_,aframe,amem⟩ :=
    BinarySplit.executes k input tape layout.split data.target clock hw hc hs s hn h94 h95 h97 cfg saved work hf hb
  have keepA (i : ℕ) (hi : 98 ≤ i) := BinarySplit.cycle_keep aframe i hi
  have a87 : Blank a.val 87 := RationalAccumulator.blank_of_eq
    (aframe.2.2.2.1 87 (by omega)
      (by simp [DoublingPass.RoundPrivate,DoublingPass.Private]) (by omega) (by omega)) h87
  have before : ChildPermutation.Before (layout.child (2*(2^k))) clock a.val := by
    refine ⟨?_,acfg.index,acfg.clock,acfg.newJump,?_,asaved.1,?_⟩
    · simpa only [BinarySplit.finalLayout,CycleSplit.colorLayout,DoublingPass.layoutAfter_width,Layout.child] using acfg.width
    · simpa only [BinarySplit.finalLayout,CycleSplit.colorLayout,show Nat.bits 1=[true] from rfl] using acfg.newMinimum
    · intro i
      exact BankArray.word_of_eq (keepA (122+i.val) (by omega)) (by simpa only [Layout.child_outputBase] using bases i)
  obtain ⟨bc,b,childClock,hbc,eb,bcfg,hchild,bn,bwork,bframe⟩ :=
    ChildPermutation.prepare_executes k input tape (layout.child (2*(2^k))) clock hw hc a before awork an
      (RationalAccumulator.blank_of_eq (keepA 120 (by omega)) h120)
      (RationalAccumulator.blank_of_eq (keepA 121 (by omega)) h121)
      (RationalAccumulator.blank_of_eq (keepA 127 (by omega)) h127)
      (RationalAccumulator.blank_of_eq (keepA 128 (by omega)) h128) a87
  have b126 : Blank b.val 126 := RationalAccumulator.blank_of_eq
    ((bframe.2.2.2.2.1 126 (by simp [ChildPermutation.MetadataPrivate])).trans (keepA 126 (by omega))) h126
  obtain ⟨cc,c,hcc,ec,ccfg,cwork,c126,crep,cframe,cmem⟩ :=
    ChildPermutation.prepares k input tape (layout.child (2*(2^k))) data clock childClock hw hc hchild hcs
      b bn b126 bcfg bwork
      (by simpa only [bframe.2.1,Layout.child] using af)
      (by simpa only [bframe.2.1,Layout.child,hcolors] using acolors)
  have keepB (i : ℕ) (hi : ¬ChildPermutation.MetadataPrivate i) := bframe.2.2.2.2.1 i hi
  have keepC (i : ℕ) (h10 : 10 ≤ i) (hi : i≠81) (hj : i≠126) (hp : ¬ChildPermutation.Private i) :=
    cframe.2.2.2.1 i (Or.inr h10) hi hj hp
  have cn : Word c.val 96 (2*(2^k)).bits := BankArray.word_of_eq
    ((keepC 96 (by omega) (by omega) (by omega) (by simp [ChildPermutation.Private,DoublingInit.Private,DoublingPass.Private])).trans
      (keepB 96 (by simp [ChildPermutation.MetadataPrivate]))) an
  have csaved : BinarySplit.Saved layout.split c.val := BinarySplit.saved_of_tapes
    (fun i hi hj => (keepC i (by omega) (by omega) (by omega)
      (by simp only [ChildPermutation.Private,DoublingInit.Private,DoublingPass.Private]; omega)).trans
        (keepB i (by dsimp [ChildPermutation.MetadataPrivate]; omega))) asaved
  refine ⟨ac+(bc+cc),c,childClock,by dsimp only [costCap]; omega,ea.seq (eb.seq ec),
    ccfg,hchild,cwork,c126,crep,cn,csaved,
    (Frame.of_split aframe).trans ((Frame.of_prepare bframe).trans (Frame.of_child cframe)),?_⟩
  intro p hp hc'
  exact (cmem p hc').trans ((congrFun bframe.2.1 p).trans (amem p hp))

end Maxwell.Cost.SplitNode
