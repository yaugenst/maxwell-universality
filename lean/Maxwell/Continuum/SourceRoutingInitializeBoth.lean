import Maxwell.Continuum.SourceRoutingInitialize
import Maxwell.Continuum.SourceRoutingMemory

/-! Both sentinel arrays are produced from stored metadata and arbitrary
memory; all initialization cursors and the copied sentinel are reclaimed. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Initialize
open Structured
open RationalAccumulator (Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

theorem ready_of_keep {s t : BitRAMState} (h : Ready s)
    (keep : ∀i, i≤9 ∨ i=37 ∨ i=752 → t.tapes i=s.tapes i) : Ready t := by
  rcases h.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
  exact ⟨⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) h0,
    RationalAccumulator.blank_of_eq (keep 1 (by decide)) h1,
    RationalAccumulator.blank_of_eq (keep 2 (by decide)) h2,
    RationalAccumulator.blank_of_eq (keep 3 (by decide)) h3,
    RationalAccumulator.blank_of_eq (keep 5 (by decide)) h5,
    RationalAccumulator.blank_of_eq (keep 6 (by decide)) h6,
    RationalAccumulator.blank_of_eq (keep 8 (by decide)) h8,
    RationalAccumulator.blank_of_eq (keep 9 (by decide)) h9⟩,
    RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven,
    RationalAccumulator.blank_of_eq (keep 37 (by decide)) h.pack,
    RationalAccumulator.blank_of_eq (keep 752 (by decide)) h.probe⟩

theorem work_metadata (i : ℕ) (hi : i∈work) : 730 ≤ i ∨ i=37 := by
  simp only [work,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem array_preserved_by_fill {n m : ℕ} {target targetWidth source sourceWidth : ℕ}
    {s t : BitRAMState} (h : PositiveGraph.Initialize.Outside target targetWidth n s t)
    (values : Vector (List Bool) m) (hv : BitArray.Represents s.memory source sourceWidth values)
    (hsep : IncidenceEncoding.Separated source (m*sourceWidth) target (n*targetWidth)) :
    BitArray.Represents t.memory source sourceWidth values := by
  refine ⟨hv.length,?_⟩
  intro i j hj
  rw [h _]
  · exact hv.bits i j hj
  · have hi := Nat.mul_le_mul_right sourceWidth (show i.val+1≤m by omega)
    rcases hsep with hs|hs
    · left
      nlinarith only [hi,hs,hj]
    · right
      omega

def code : Code := .seq (.call (WordTransfer.clone 709 739))
  (.seq (fillCode false) (.seq (fillCode true) (.call (TapeOps.clear 739))))

def cost {n : ℕ} (l : Layout n) : ℕ :=
  2*PositiveGraph.Initialize.fillCost n (scale l)+21*n.bits.length+23

theorem initializes_both {n : ℕ} (l : Layout n)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready s.val) (hm : Metadata l s.val)
    (h730 : Blank s.val 730) (h732 : Blank s.val 732) (h739 : Blank s.val 739) :
    ∃steps t, Executes input tape code steps s t ∧ steps≤cost l ∧
      Ready t.val ∧ Metadata l t.val ∧ Blank t.val 730 ∧ Blank t.val 732 ∧ Blank t.val 739 ∧
      Stored l (Vector.replicate n n) (Vector.replicate n n) t.val ∧
      RoutingOutside l s.val t.val ∧ Frame work s.val t.val := by
  obtain ⟨co,hco⟩ := hm.count
  obtain ⟨vo,hvo⟩ := h739
  obtain ⟨a,ea,hat,fa⟩ := WordCall.clone 709 739 (by decide) input tape n.bits co vo s hco hvo
  have keepa (i : ℕ) (hi : i≠739) : a.val.tapes i=s.val.tapes i := by simp [hat,hi]
  have framea : Frame work s.val a.val := by
    refine ⟨fa.2.1,fa.2.2.2.1,fa.2.2.2.2.1,?_,?_⟩
    · intro i _ hi
      exact keepa i (by simp only [work,Finset.mem_insert,Finset.mem_singleton,not_or] at hi; omega)
    · intro i _ h24 h25 h26 h27 _ _
      exact fa.2.2.2.2.2.2 i h24 h25 h26 h27
  have ar := ready_of_keep hs (fun i hi => keepa i (by omega))
  have am := hm.frame framea work_metadata
  have a730 := RationalAccumulator.blank_of_eq (keepa 730 (by decide)) h730
  have a732 := RationalAccumulator.blank_of_eq (keepa 732 (by decide)) h732
  have a739 : RationalAccumulator.Word a.val 739 n := ⟨vo,by simp [hat]⟩
  obtain ⟨cb,b,eb,hcb,br,bm,b730,b732,b739,barray,boutside,fb⟩ :=
    fill_array l false input tape a ar am a730 a732 a739
  obtain ⟨cc,c,ec,hcc,cr,cm,c730,c732,c739,carray,coutside,fc⟩ :=
    fill_array l true input tape b br bm b730 b732 b739
  change BitArray.Represents b.val.memory l.forward n.bits.length (encode (Vector.replicate n n)) at barray
  change BitArray.Represents c.val.memory l.backward n.bits.length (encode (Vector.replicate n n)) at carray
  change PositiveGraph.Initialize.Outside l.forward n.bits.length n a.val b.val at boutside
  change PositiveGraph.Initialize.Outside l.backward n.bits.length n b.val c.val at coutside
  have cf := array_preserved_by_fill coutside _ barray l.separated
  obtain ⟨origin,ho⟩ := c739
  obtain ⟨t,et,htt,ft⟩ := WordCall.clear 739 input tape n.bits origin c ho
  have keept (i : ℕ) (hi : i≠739) : t.val.tapes i=c.val.tapes i := by simp [htt,hi]
  have framet : Frame work c.val t.val := by
    refine ⟨ft.2.1,ft.2.2.2.1,ft.2.2.2.2.1,?_,?_⟩
    · intro i _ hi
      exact keept i (by simp only [work,Finset.mem_insert,Finset.mem_singleton,not_or] at hi; omega)
    · intro i _ _ _ h26 h27 _ _
      exact ft.2.2.2.2.2.2 i h26 h27
  have tr := ready_of_keep cr (fun i hi => keept i (by omega))
  have outa : RoutingOutside l s.val a.val := RoutingOutside.of_memory fa.2.2.1
  have outb : RoutingOutside l a.val b.val := fun i hi _ => boutside i hi
  have outc : RoutingOutside l b.val c.val := fun i _ hi => coutside i hi
  have outt : RoutingOutside l c.val t.val := RoutingOutside.of_memory ft.2.2.1
  refine ⟨_,t,ea.seq (eb.seq (ec.seq et)),?_,tr,cm.frame framet work_metadata,
    RationalAccumulator.blank_of_eq (keept 730 (by decide)) c730,
    RationalAccumulator.blank_of_eq (keept 732 (by decide)) c732,
    ⟨origin+n.bits.length,by simp [htt]⟩,?_,outa.trans (outb.trans (outc.trans outt)),
    framea.trans (fb.trans (fc.trans framet))⟩
  · unfold cost
    omega
  · constructor
    · rw [ft.2.2.1]
      exact cf
    · rw [ft.2.2.1]
      exact carray

#print axioms initializes_both

end Maxwell.Cost.RoutingPorts.Complete.Initialize
