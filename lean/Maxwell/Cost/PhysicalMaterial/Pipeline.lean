import Maxwell.Cost.PhysicalMaterial.Preprocess
import Maxwell.Cost.PhysicalMaterial.GridEmit

namespace Maxwell.Cost.PhysicalMaterial.Pipeline
open Structured RationalAccumulator Maxwell.Spectral.Lattice
set_option maxHeartbeats 2400000

def scratch : Finset ℕ := CellEmit.work ∪ Scatter.work ∪ Descriptors.targets ∪ {302,303,328,329}
structure Ready (sn sd : ℕ) (s : Store) : Prop where
  period : Word s.val 243 20
  clock : Word s.val 249 16
  sigmaNumerator : Word s.val 260 sn
  sigmaDenominator : Word s.val 261 sd
  blank : ∀ j∈scratch, Blank s.val j

def work : Finset ℕ := Preprocess.work ∪ GridEmit.work
structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  tapes : ∀ j, j=4 ∨ 10≤j → j∉work → t.tapes j=s.tapes j

def code (points : List Scatter.Point) (material : Cell20→ℚ) : Code :=
  .seq (Preprocess.code points) (GridEmit.code material)
def costBound (nx ny nz n B : ℕ) (points : List Scatter.Point) (material : Cell20→ℚ) : ℕ :=
  Preprocess.costBound (nx*ny*nz) n B points+
    (nx+1)*(ny+1)*(nz+1)*(GridEmit.bodyBudget material B+156*B+174)

/-- A fixed finite material-generation program: actual dimensions and
anchor/strength descriptors are its only runtime geometric inputs. It
initializes and scatters a dense overlay, then emits all material cells in
codec order. The descriptor count is absent from the per-cell cost. -/
theorem executes {n : ℕ} (d : Descriptors.Data n) (nx ny nz B sn sd : ℕ)
    (l : Dense.Layout (nx*ny*nz)) (points : List Scatter.Point)
    (locations : Fin n→Scatter.Point→Fin (nx*ny*nz))
    (hd : d.Sized B) (hl : l.Sized B) (hwidth : d.width=l.width)
    (hsep : Scatter.SeparatedData d l) (hn : n<2^B) (hvolume : nx*ny*nz<2^B)
    (hindex : ∀ i p, p∈points → Scatter.flatIndex (Scatter.anchor d i) p ny nz=(locations i p).val)
    (hroom : ∀ i p, p∈points → ∀ j, 0≤(Scatter.anchor d i j:ℤ)+p j)
    (hsize : ∀ a : Fin 3, (![nx,ny,nz] a).bits.length≤B)
    (material : Cell20→ℚ) (hm : ∀ c, 0≤material c)
    (hmaterial : ∀ c, (material c).num.toNat.bits.length≤B ∧ (material c).den.bits.length≤B)
    (hsigma : sn.bits.length≤B ∧ sd.bits.length≤B) (hsd : 0<sd)
    (hden : ∀ i, 0<Descriptors.value d i 4)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready sn sd s)
    (hdata : Descriptors.Stored d s.val) (hmeta : DenseInit.Metadata l s.val)
    (hcount : Word s.val 304 n) (hr : PhysicalEmit.LowerReady 0 ![nx,ny,nz] B s.val) :
    ∃ cost t, cost≤costBound nx ny nz n B points material ∧ Executes input tape (code points material) cost s t ∧
      GridEmit.Ready l
        (Scatter.filledNums d l points locations (Scatter.zeroNums l) n)
        (Scatter.filledDens d l points locations (Scatter.oneDens l) n) sn sd t ∧
      Descriptors.Stored d t.val ∧ PhysicalEmit.LowerReady 0 ![nx,ny,nz] B t.val ∧
      Frame s.val t.val ∧ Dense.Outside l s.val t.val ∧
      t.val.output = (PhysicalEmit.gridWords ![nx,ny,nz]
        (GridEmit.records (Scatter.filledNums d l points locations (Scatter.zeroNums l) n)
          (Scatter.filledDens d l points locations (Scatter.oneDens l) n) material ny nz sn sd)).reverse ++ s.val.output := by
  have hp : Scatter.PointReady s.val :=
    ⟨(fun j hj => hs.blank j (by
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa using hj)))),
      hs.blank 37 (by decide),hs.blank 292 (by decide),hs.blank 322 (by decide),
      fun j => hs.blank (324+j.val) (by fin_cases j <;> decide)⟩
  have hv : Descriptors.Bank s.val (fun _=>0) := fun j =>
    (zero_word_iff_blank _ _).mpr (hs.blank (Descriptors.targetTape j) (by fin_cases j <;> decide))
  obtain ⟨pc,a,hpc,ep,har,had,hav,hal,_,_,_,_,fa,oa⟩ := Preprocess.executes d nx ny nz B l points locations
    hd hl hwidth hsep hn hvolume hindex hroom ⟨hsize 0,hsize 1,hsize 2⟩ input tape s hp hdata hmeta hv
    (hs.blank 302 (by decide)) (hs.blank 303 (by decide)) (hs.blank 328 (by decide)) (hs.blank 329 (by decide))
    hcount (hr.dimensions 0) (hr.dimensions 1) (hr.dimensions 2)
  let nums := Scatter.filledNums d l points locations (Scatter.zeroNums l) n
  let dens := Scatter.filledDens d l points locations (Scatter.oneDens l) n
  have hagr : GridEmit.Ready l nums dens sn sd a := by
    refine ⟨word_of_eq (fa.tapes 243 (by decide) (by decide)) hs.period,
      word_of_eq (fa.tapes 249 (by decide) (by decide)) hs.clock,
      word_of_eq (fa.tapes 260 (by decide) (by decide)) hs.sigmaNumerator,
      word_of_eq (fa.tapes 261 (by decide) (by decide)) hs.sigmaDenominator,?_,hal⟩
    intro j hj
    by_cases hj10 : j<10
    · exact har.1 j hj10
    · by_cases hj322 : j=322
      · subst j; exact har.2.2.2.1
      · apply blank_of_eq (fa.tapes j (Or.inr (by omega)) ?_)
          (hs.blank j (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hj))))
        have hdis : CellEmit.work ∩ Preprocess.work ⊆ Finset.range 10 ∪ {322} := by decide
        intro hh
        have hout := hdis (Finset.mem_inter.mpr ⟨hj,hh⟩)
        simp only [Finset.mem_union,Finset.mem_range,Finset.mem_singleton] at hout
        omega
  have hagrids : PhysicalEmit.LowerReady 0 ![nx,ny,nz] B a.val := by
    refine ⟨?_,?_,?_⟩
    · intro j
      apply word_of_eq (fa.tapes _ (by dsimp [PhysicalEmit.dimensionTape]; omega) ?_) (hr.dimensions j)
      fin_cases j <;> decide
    · intro j hj
      obtain ⟨v,hv,hw⟩ := hr.coordinates j hj
      refine ⟨v,hv,word_of_eq (fa.tapes _ (by dsimp [PhysicalEmit.coordinateTape]; omega) ?_) hw⟩
      fin_cases j <;> decide
    · intro j hj
      obtain ⟨v,hv,hw⟩ := hr.counters j hj
      refine ⟨v,hv,BankArray.word_of_eq (fa.tapes _ (by dsimp [PhysicalEmit.counterTape]; omega) ?_) hw⟩
      fin_cases j <;> decide
  have fit (i : Fin n) (j : Fin 5) : (Descriptors.value d i j).bits.length≤addressValue l.width := by
    rw [←hwidth]
    exact Descriptors.value_bits d i j s.val hdata
  have denseDen (i : Fin (nx*ny*nz)) : 0<addressValue (dens.get i) :=
    Scatter.filled_den_pos d l points locations (fun j=>fit j 4) hden i n
  have numBits (i : Fin (nx*ny*nz)) : (addressValue (nums.get i)).bits.length≤B :=
    ((CalibrationMatrix.canonical_length_le _).trans (hal.nums.length i).le).trans hl.2.1
  have denBits (i : Fin (nx*ny*nz)) : (addressValue (dens.get i)).bits.length≤B :=
    ((CalibrationMatrix.canonical_length_le _).trans (hal.dens.length i).le).trans hl.2.1
  obtain ⟨gc,t,hgc,eg,htr,htgrid,fg,hout⟩ := GridEmit.executes nx ny nz B sn sd l nums dens hl hvolume hsize
    material hm hsd denseDen (fun x y z _ _ _ =>
      ⟨(hmaterial (Emit.cell x y z)).1,(hmaterial (Emit.cell x y z)).2,hsigma.1,hsigma.2,numBits _,denBits _⟩)
    input tape a hagr hagrids
  have htd := Scatter.preserve_descriptors d l hsep had (Dense.Outside.of_memory l fg.memory)
    (fun j hj => fg.tapes j (by
      rcases hj with hj|hj|hj
      · subst j; decide
      · subst j; decide
      · obtain ⟨hlo,hhi⟩ := hj
        interval_cases j <;> decide))
  refine ⟨pc+gc,t,by dsimp only [costBound]; omega,ep.seq eg,htr,htd,htgrid,?_,
    oa.trans (Dense.Outside.of_memory l fg.memory),?_⟩
  · exact ⟨fg.inputHead.trans fa.inputHead,fg.randomCursor.trans fa.randomCursor,
      fun j hj hn => (fg.tapes j (fun hh=>hn (Finset.mem_union_right _ hh))).trans
        (fa.tapes j hj (fun hh=>hn (Finset.mem_union_left _ hh)))⟩
  · rw [hout,fa.output]

end Maxwell.Cost.PhysicalMaterial.Pipeline
