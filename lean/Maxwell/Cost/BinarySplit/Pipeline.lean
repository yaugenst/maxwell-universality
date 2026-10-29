import Maxwell.Cost.BinarySplit.Frames

namespace Maxwell.Cost.BinarySplit
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing
open Coloring.NumericSplit

/-- The node builds both pairings, then computes their alternating-cycle colors. -/
def code : Code := .seq HalfPair.passCode
  (.seq conjugateCode (.seq ConjugatePass.passCode (.seq cycleCode CycleSplit.code)))

def costCap (layout : Layout) (n : ℕ) (clock : List Bool) : ℕ :=
  HalfPair.passCost layout.half n + (conjugateCost layout clock +
    (ConjugatePass.passCost layout.conjugate n + (cycleCost layout clock + CycleSplit.costCap layout.cycle n)))

def colors (k : ℕ) (target : Equiv.Perm (Fin (2*(2^k)))) : Vector Bool (2*(2^k)) :=
  Doubling.indexedColors (Equiv.refl _) (halfSwap (2^k)) (target.symm * halfSwap (2^k) * target)

def finalLayout (layout : Layout) (n : ℕ) : DoublingPass.Layout :=
  CycleSplit.colorLayout (DoublingPass.layoutAfter layout.route n.bits.length) layout.pairing

theorem executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (target : Equiv.Perm (Fin (2*(2^k)))) (clock : List Bool)
    (hw : layout.route.width=k+2) (hc : clock.length=layout.route.width)
    (hs : layout.Separated (2*(2^k))) (s : Store)
    (hnword : Word s.val 96 (2*(2^k)).bits) (h94 : Blank s.val 94)
    (h95 : Blank s.val 95) (h97 : Blank s.val 97)
    (cfg : DoublingInit.Config layout.half [] clock s.val)
    (saved : Saved layout s.val) (work : DoublingInit.Workspace s.val)
    (hf : BitArray.Represents s.val.memory layout.forward layout.route.width
      (DoublingPass.words layout.route.width (Vector.ofFn target)))
    (hb : BitArray.Represents s.val.memory layout.backward layout.route.width
      (DoublingPass.words layout.route.width (Vector.ofFn target.symm))) :
    ∃ cost t, cost≤costCap layout (2*(2^k)) clock ∧ Executes input tape code cost s t ∧
      DoublingPass.Config (finalLayout layout (2*(2^k))) [] clock t.val ∧
      DoublingInit.Workspace t.val ∧ Blank t.val 94 ∧ Blank t.val 95 ∧ Blank t.val 97 ∧
      Word t.val 96 (2*(2^k)).bits ∧ Saved layout t.val ∧
      BitArray.Represents t.val.memory (finalLayout layout (2*(2^k))).newJump 1
        (ColorPass.colorWords (colors k target)) ∧
      BitArray.Represents t.val.memory layout.forward layout.route.width
        (DoublingPass.words layout.route.width (Vector.ofFn target)) ∧
      BitArray.Represents t.val.memory layout.backward layout.route.width
        (DoublingPass.words layout.route.width (Vector.ofFn target.symm)) ∧
      CycleSplit.Frame s.val t.val ∧ MemoryFrame layout (2*(2^k)) s.val.memory t.val.memory := by
  let n := 2*(2^k)
  have hfit : n.bits.length=layout.route.width := by simpa only [n,HalfPair.array_bits_length] using hw.symm
  have hn : n≤2^layout.route.width := by
    rw [← hfit]
    exact Nat.le_of_lt (by simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self n)
  have hpos : 0<layout.route.width := by omega
  obtain ⟨pc,p,hpc,ep,pcfg,pwork,p94,pa,pframe,pmem⟩ :=
    HalfPair.prepares k input tape layout.half clock hw hc s hnword h94 cfg work
  have pf : BitArray.Represents p.val.memory layout.forward layout.route.width
      (DoublingPass.words layout.route.width (Vector.ofFn target)) :=
    represents_outside pmem (hs 0 2 (by decide)) hf
  have pb : BitArray.Represents p.val.memory layout.backward layout.route.width
      (DoublingPass.words layout.route.width (Vector.ofFn target.symm)) :=
    represents_outside pmem (hs 1 2 (by decide)) hb
  have psaved := saved_of_cycle (CycleSplit.Frame.of_init pframe) saved
  obtain ⟨a,ea,acfg,asaved,awork,aframe⟩ := to_conjugate layout clock input tape p pcfg psaved pwork
  have anword : Word a.val 96 n.bits := BankArray.word_of_eq
    ((aframe.keep 96 (by omega) (by omega) (by omega) (by omega)).trans (init_keep pframe 96 (by omega))) hnword
  have a94 : Blank a.val 94 := RationalAccumulator.blank_of_eq
    (aframe.keep 94 (by omega) (by omega) (by omega) (by omega)) p94
  have arA : BitArray.Represents a.val.memory layout.conjugate.oldMinimum layout.conjugate.width
      (DoublingPass.words layout.conjugate.width (Vector.ofFn (halfSwap (2^k)))) := by
    simpa only [aframe.2.2.1,HalfPair.Represents,HalfPair.array_eq_words,Layout.half,Layout.conjugate,hw] using pa
  obtain ⟨cc,c,hcc,ec,ccfg,cwork,c94,cf,ca,cb,cr,cframe,cmem⟩ :=
    ConjugatePass.prepares input tape layout.conjugate target (halfSwap (2^k)) clock
      hpos hn hc hs.conjugate a anword a94 acfg.route awork.1
      (by simpa only [aframe.2.2.1,Layout.conjugate] using pf) arA
      (by simpa only [aframe.2.2.1,Layout.conjugate] using pb)
  have ckeep37 : c.val.tapes 37=a.val.tapes 37 := cframe.2.2.2.1 37
    (by omega) (by omega) (by simp [DoublingPass.Private]) (by omega)
  have ccfg' : DoublingInit.Config ⟨layout.conjugate,layout.pairing,layout.conjugated⟩ [] clock c.val :=
    ⟨ccfg,BankArray.word_of_eq (conjugate_keep cframe 98 (by omega)) acfg.inputA,
      BankArray.word_of_eq (conjugate_keep cframe 99 (by omega)) acfg.inputB⟩
  have csaved := saved_of_cycle (CycleSplit.Frame.of_finish cframe) asaved
  obtain ⟨d,ed,dcfg,dsaved,dwork,dframe⟩ := to_cycle layout clock input tape c ccfg' csaved
    ⟨cwork,RationalAccumulator.blank_of_eq ckeep37 awork.2⟩
  have dnword : Word d.val 96 n.bits := BankArray.word_of_eq
    ((dframe.keep 96 (by omega) (by omega) (by omega) (by omega)).trans (conjugate_keep cframe 96 (by omega))) anword
  have d94 : Blank d.val 94 := RationalAccumulator.blank_of_eq
    (dframe.keep 94 (by omega) (by omega) (by omega) (by omega)) c94
  have keepD (i : ℕ) (hi : 95 ≤ i) : d.val.tapes i=s.val.tapes i :=
    (dframe.keep i (by omega) (by omega) (by omega) (by omega)).trans
      ((conjugate_keep cframe i hi).trans
        ((aframe.keep i (by omega) (by omega) (by omega) (by omega)).trans (init_keep pframe i hi)))
  obtain ⟨zc,z,hzc,ez,zcfg,zwork,z94,z95,z97,znword,zcolors,zframe,zmem⟩ :=
    CycleSplit.executes input tape layout.cycle (halfSwap (2^k)) (target.symm * halfSwap (2^k) * target)
      clock hpos hn (by change n.bits.length≤layout.route.width; omega) hc hs.cycle d dnword d94
      (RationalAccumulator.blank_of_eq (keepD 95 (by omega)) h95)
      (RationalAccumulator.blank_of_eq (keepD 97 (by omega)) h97) dcfg dwork
      (by simpa only [dframe.2.2.1,DoublingInit.permutation,Layout.conjugate,Layout.cycle] using ca)
      (by simpa only [dframe.2.2.1,DoublingInit.permutation,Layout.conjugate,Layout.cycle] using cr)
  have zf := (hs.apart_route 0).represents zmem
    (show BitArray.Represents d.val.memory layout.forward layout.route.width
      (DoublingPass.words layout.route.width (Vector.ofFn target)) by simpa only [dframe.2.2.1,Layout.conjugate] using cf)
  have zb := (hs.apart_route 1).represents zmem
    (show BitArray.Represents d.val.memory layout.backward layout.route.width
      (DoublingPass.words layout.route.width (Vector.ofFn target.symm)) by simpa only [dframe.2.2.1,Layout.conjugate] using cb)
  refine ⟨pc+(conjugateCost layout clock+(cc+(cycleCost layout clock+zc))),z,?_,?_,
    zcfg,zwork,z94,z95,z97,znword,saved_of_cycle zframe dsaved,zcolors,zf,zb,?_,?_⟩
  · dsimp only [costCap]; omega
  · exact ep.seq (ea.seq (ec.seq (ed.seq ez)))
  · exact (CycleSplit.Frame.of_init pframe).trans (aframe.cycle.trans
      ((CycleSplit.Frame.of_finish cframe).trans (dframe.cycle.trans zframe)))
  · exact (MemoryFrame.of_half pmem).trans ((MemoryFrame.of_eq aframe.2.2.1).trans
      ((MemoryFrame.of_conjugate cmem).trans ((MemoryFrame.of_eq dframe.2.2.1).trans (MemoryFrame.of_cycle zmem))))

end Maxwell.Cost.BinarySplit
