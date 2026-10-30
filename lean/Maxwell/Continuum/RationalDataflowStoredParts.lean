import Maxwell.Continuum.RationalDataflowWordReplace
import Maxwell.Continuum.RationalDataflowArrayFrame

/-! Charged copies of one unreduced rational register to three external tapes.
The instructions do not depend on the widths or values being saved. -/
namespace Maxwell.Continuum.RationalDataflow.StoredParts
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2000000

def ports (base : ℕ) : Finset ℕ := {base,base+1,base+2}

def Stored (base : ℕ) (x : Parts) (s : BitRAMState) : Prop :=
  Word s base x.positive ∧ Word s (base+1) x.negative ∧ Word s (base+2) x.denominator

def saveCode (base source : ℕ) : Code :=
  .seq (WordReplace.code (positivePort source) base)
    (.seq (WordReplace.code (negativePort source) (base+1))
      (WordReplace.code (denominatorPort source) (base+2)))

def restoreCode (base target : ℕ) : Code :=
  .seq (WordReplace.code base (positivePort target))
    (.seq (WordReplace.code (base+1) (negativePort target))
      (WordReplace.code (base+2) (denominatorPort target)))

theorem copy_frame {target : ℕ} {s t : BitRAMState} (h : WordReplace.Frame target s t) :
    BinaryPrecision.Frame {target} s t :=
  ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,fun i hi =>
    h.2.2.2.2.2.1 i (by simpa using hi)⟩

theorem Stored.frame {base : ℕ} {x : Parts} {s t : BitRAMState} {changed : Finset ℕ}
    (h : Stored base x s) (f : BinaryPrecision.Frame changed s t)
    (hd : Disjoint (ports base) changed) : Stored base x t := by
  have keep (i : ℕ) (hi : i∈ports base) : t.tapes i=s.tapes i :=
    f.tapes i (fun hm => Finset.disjoint_left.mp hd hi hm)
  exact ⟨word_of_eq (keep base (by simp [ports])) h.1,
    word_of_eq (keep (base+1) (by simp [ports])) h.2.1,
    word_of_eq (keep (base+2) (by simp [ports])) h.2.2⟩

theorem Stored.blank {base : ℕ} {s : BitRAMState}
    (h : ∀i∈ports base,Blank s i) : Stored base ⟨0,0,0⟩ s :=
  ⟨(zero_word_iff_blank _ _).mpr (h _ (by simp [ports])),
    (zero_word_iff_blank _ _).mpr (h _ (by simp [ports])),
    (zero_word_iff_blank _ _).mpr (h _ (by simp [ports]))⟩

theorem save_executes (S : Finset ℕ) (base source : ℕ) (hb : 107≤base) (hb' : base+2<1000)
    (ht : source∈S) (v : ℕ→Parts) (old : Parts) (B : ℕ)
    (hv : (v source).Width B) (ho : old.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hold : Stored base old s.val) :
    ∃cost t,Executes input tape (saveCode base source) cost s t ∧ cost≤63*(B+1) ∧
      Ready S v t ∧ Stored base (v source) t.val ∧
      BinaryPrecision.Frame (ports base) s.val t.val := by
  have hp := positivePort_ge source
  have hn := negativePort_ge source
  have hd := denominatorPort_ge source
  have sp : Word s.val (positivePort source) (v source).positive := by
    simpa using hs.1 (positivePort source) (cell_mem ht (by simp [cellPorts]))
  obtain ⟨s1,e1,w1,f1⟩ := WordReplace.executes _ _ (by omega : positivePort source≠base)
    input tape _ _ s sp hold.1
  have r1 := hs.wordReplace_frame (outside_workspace S base (Or.inr ⟨hb,by omega⟩)) f1
  have sn : Word s1.val (negativePort source) (v source).negative := by
    simpa using r1.1 (negativePort source) (cell_mem ht (by simp [cellPorts]))
  have o1 := word_of_eq (f1.2.2.2.2.2.1 (base+1) (by omega)) hold.2.1
  obtain ⟨s2,e2,w2,f2⟩ := WordReplace.executes _ _ (by omega : negativePort source≠base+1)
    input tape _ _ s1 sn o1
  have r2 := r1.wordReplace_frame (outside_workspace S (base+1) (Or.inr ⟨by omega,by omega⟩)) f2
  have sd : Word s2.val (denominatorPort source) (v source).denominator := by
    simpa using r2.1 (denominatorPort source) (cell_mem ht (by simp [cellPorts]))
  have o2 := word_of_eq (f2.2.2.2.2.2.1 (base+2) (by omega))
    (word_of_eq (f1.2.2.2.2.2.1 (base+2) (by omega)) hold.2.2)
  obtain ⟨t,e3,w3,f3⟩ := WordReplace.executes _ _ (by omega : denominatorPort source≠base+2)
    input tape _ _ s2 sd o2
  refine ⟨_,t,e1.seq (e2.seq e3),?_,
    r2.wordReplace_frame (outside_workspace S (base+2) (Or.inr ⟨by omega,hb'⟩)) f3,
    ⟨word_of_eq (f3.2.2.2.2.2.1 base (by omega))
      (word_of_eq (f2.2.2.2.2.2.1 base (by omega)) w1),
      word_of_eq (f3.2.2.2.2.2.1 (base+1) (by omega)) w2,w3⟩,
    ((copy_frame f1).mono (by simp [ports])).trans
      (((copy_frame f2).mono (by simp [ports])).trans ((copy_frame f3).mono (by simp [ports])))⟩
  rcases hv with ⟨hvp,hvn,hvd⟩
  rcases ho with ⟨hop,hon,hod⟩
  omega

private theorem bank_copy {S : Finset ℕ} {v : ℕ→ℕ} {target x : ℕ} {s t : BitRAMState}
    (h : NatAssign.Bank S v s) (w : Word t target x) (f : WordReplace.Frame target s t) :
    NatAssign.Bank S (Function.update v target x) t := by
  intro i hi
  by_cases he : i=target
  · subst i; simpa using w
  · simp only [Function.update_of_ne he]
    exact word_of_eq (f.2.2.2.2.2.1 i he) (h i hi)

theorem restore_executes (S : Finset ℕ) (base target : ℕ) (hb' : base+2<1000)
    (ht : target∈S) (v : ℕ→Parts) (x : Parts) (B : ℕ)
    (hv : (v target).Width B) (hx : x.Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hstore : Stored base x s.val) :
    ∃cost t,Executes input tape (restoreCode base target) cost s t ∧ cost≤63*(B+1) ∧
      Ready S (Function.update v target x) t ∧ Stored base x t.val ∧
      BinaryPrecision.Frame (cellPorts target) s.val t.val := by
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  have hpn : positivePort target≠negativePort target := by unfold positivePort negativePort; omega
  have hpd : positivePort target≠denominatorPort target := by unfold positivePort denominatorPort; omega
  have hnd : negativePort target≠denominatorPort target := by unfold negativePort denominatorPort; omega
  have op : Word s.val (positivePort target) (v target).positive := by
    simpa using hs.1 (positivePort target) (cell_mem ht (by simp [cellPorts]))
  obtain ⟨s1,e1,w1,f1⟩ := WordReplace.executes _ _ (by omega : base≠positivePort target)
    input tape _ _ s hstore.1 op
  have on : Word s1.val (negativePort target) (v target).negative :=
    word_of_eq (f1.2.2.2.2.2.1 _ hpn.symm) (by
      simpa using hs.1 (negativePort target) (cell_mem ht (by simp [cellPorts])))
  have s1n := word_of_eq (f1.2.2.2.2.2.1 (base+1) (by omega)) hstore.2.1
  obtain ⟨s2,e2,w2,f2⟩ := WordReplace.executes _ _ (by omega : base+1≠negativePort target)
    input tape _ _ s1 s1n on
  have od : Word s2.val (denominatorPort target) (v target).denominator :=
    word_of_eq (f2.2.2.2.2.2.1 _ hnd.symm) (word_of_eq (f1.2.2.2.2.2.1 _ hpd.symm) (by
      simpa using hs.1 (denominatorPort target) (cell_mem ht (by simp [cellPorts]))))
  have s2d := word_of_eq (f2.2.2.2.2.2.1 (base+2) (by omega))
    (word_of_eq (f1.2.2.2.2.2.1 (base+2) (by omega)) hstore.2.2)
  obtain ⟨t,e3,w3,f3⟩ := WordReplace.executes _ _ (by omega : base+2≠denominatorPort target)
    input tape _ _ s2 s2d od
  have frame : BinaryPrecision.Frame (cellPorts target) s.val t.val :=
    ((copy_frame f1).mono (by simp [cellPorts])).trans
      (((copy_frame f2).mono (by simp [cellPorts])).trans ((copy_frame f3).mono (by simp [cellPorts])))
  refine ⟨_,t,e1.seq (e2.seq e3),?_,?_,hstore.frame frame ?_,frame⟩
  · rcases hv with ⟨hvp,hvn,hvd⟩
    rcases hx with ⟨hxp,hxn,hxd⟩
    omega
  · constructor
    · have b := bank_copy (bank_copy (bank_copy hs.1 w1 f1) w2 f2) w3 f3
      change NatAssign.Bank (ids S) (writeParts (dataValues v) target x) t.val at b
      rwa [writeParts_dataValues] at b
    · intro i hi
      apply blank_of_eq (frame.tapes i _) (hs.2 i hi)
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton]
      omega
  · apply Finset.disjoint_left.mpr
    intro i hi hcell
    simp only [ports,cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi hcell
    omega

#print axioms save_executes
#print axioms restore_executes
end Maxwell.Continuum.RationalDataflow.StoredParts
