import Maxwell.Cost.SelectedParameters.GeometricAdapterValues

/-! A stored-rational caller adapter for the actual least-power search. Only
the fixed geometric base and port addresses occur in the finite program. -/
namespace Maxwell.Cost.SelectedParameters.GeometricAdapter
open Structured RationalAccumulator
set_option maxHeartbeats 2000000

def loadCost (B : ℕ) : ℕ := 3000*8^4*(B+2)^2
def finishCost (B : ℕ) : ℕ := 3000*8^17*(B+2)^2
def costBound (N A B : ℕ) : ℕ :=
  loadCost (inputWidth A B)+(Geometric.initialCost (inputWidth A B)+
    Geometric.searchCost N A (inputWidth A B)+finishCost (Geometric.width N A (inputWidth A B)))

/-- The caller may reuse either input port for an output. The geometric
workspace starts and finishes blank, and all other caller words survive. -/
theorem executes (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i)
    (a b c d num den : ℕ) (ha : 0 < a) (hab : a < b)
    (hc : c ∈ extra) (hd : d ∈ extra) (hnum : num ∈ extra) (hden : den ∈ extra) (_hne : num ≠ den)
    (v : ℕ → ℕ) (A B : ℕ) (haW : a.bits.length ≤ A) (hbW : b.bits.length ≤ A)
    (hcpos : 0 < v c) (hdpos : 0 < v d)
    (hwidth : ∀ i ∈ Rational.ids extra, (v i).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank (Rational.ids extra) v s.val) (hscratch : NatAssign.Scratch s.val)
    (hgeo : ∀ i ∈ Geometric.extra, Blank s.val i) :
    let N := Geometric.exponent a b (v c) (v d) ha hab hcpos hdpos
    ∃ cost t, Executes input tape (code a b c d num den) cost s t ∧ cost ≤ costBound N A B ∧
      NatAssign.Bank (Rational.ids extra) (Rational.after v num den (N,1)) t.val ∧
      NatAssign.Scratch t.val ∧ (∀ i ∈ Geometric.extra ∪ Rational.common, Blank t.val i) ∧
      (∀ i ∈ Rational.ids extra, (Rational.after v num den (N,1) i).bits.length ≤
        Geometric.width N A (inputWidth A B)) ∧ BinaryPrecision.Frame (workspace num den) s.val t.val := by
  let N := Geometric.exponent a b (v c) (v d) ha hab hcpos hdpos
  let C := inputWidth A B
  let W := Geometric.width N A C
  have hA : A ≤ C := by dsimp [C,inputWidth]; omega
  have hB : B ≤ C := by dsimp [C,inputWidth]; omega
  have hC : 1 ≤ C := by dsimp [C,inputWidth]; omega
  have hCW : C ≤ W := by dsimp [W,Geometric.width]; omega
  have hBW := hB.trans hCW
  have hc540 := hextra c hc
  have hd540 := hextra d hd
  have hn540 := hextra num hnum
  have he540 := hextra den hden
  have hstart : NatAssign.Bank (ids extra) (extend v) s.val := by
    intro i hi
    by_cases hg : i ∈ Geometric.extra
    · simpa only [extend,ite_eq_left hg] using (zero_word_iff_blank s.val i).mpr (hgeo i hg)
    · simpa only [extend,ite_eq_right hg] using hbank i ((Finset.mem_union.mp hi).resolve_right hg)
  have hstartW : ∀ i ∈ ids extra, (extend v i).bits.length ≤ C := by
    intro i hi
    by_cases hg : i ∈ Geometric.extra
    · simp [extend,hg]
    · simpa only [extend,ite_eq_right hg] using
        (hwidth i ((Finset.mem_union.mp hi).resolve_right hg)).trans hB
  have hload : ∀ inst ∈ loadInputs a b c d, inst.Valid (ids extra) := by
    simp [loadInputs,NatAssign.Instruction.Valid,ids,Rational.ids,Geometric.extra,hc,hd]
    omega
  obtain ⟨c1,u,e1,p1,b1,s1,f1⟩ := NatAssign.executes (ids extra) (ids_ge extra hextra)
    (loadInputs a b c d) hload (extend v) input tape s hstart hscratch
  rw [loaded_values a b c d hc540 hd540 v] at b1
  have p1' : c1 ≤ loadCost C := p1.trans (NatAssign.price_bound (ids extra) (loadInputs a b c d)
    hload (extend v) C hstartW (by simp [loadInputs,NatAssign.Instruction.literalWidth]; exact ⟨haW.trans hA,hbW.trans hA⟩))
  let w := loaded a b c d v
  have w520 : w 520 = a := by simp [w,loaded]
  have w521 : w 521 = b := by simp [w,loaded]
  have w522 : w 522 = v c := by simp [w,loaded]
  have w523 : w 523 = v d := by simp [w,loaded]
  have wWidth : ∀ i ∈ Geometric.ids, (w i).bits.length ≤ C := fun i hi =>
    loaded_width extra a b c d A B v hc hd haW hbW hwidth i (geo_subset extra hi)
  have wBank : NatAssign.Bank Geometric.ids w u.val := fun i hi => b1 i (geo_subset extra hi)
  have egeo := Geometric.executes w A C hC (by rw [w520];exact ha)
    (by rw [w520,w521];exact hab) (by rw [w522];exact hcpos) (by rw [w523];exact hdpos)
    wWidth (by rw [w520];exact haW) (by rw [w521];exact hbW) input tape u wBank s1
  simp only [w520,w521,w522,w523] at egeo
  obtain ⟨c2,r,e2,p2,b2,f2⟩ := egeo
  have midBank : NatAssign.Bank (ids extra) (searched v a b (v c) (v d) N) r.val := by
    intro i hi
    by_cases hg : i ∈ Geometric.ids
    · simpa only [searched,ite_eq_left hg] using b2.bank i hg
    · have hiExtra : i ∈ extra := by
        simp only [ids,Rational.ids,Geometric.ids,Rational.common,Finset.mem_union] at hi hg
        tauto
      have hi540 := hextra i hiExtra
      have hkeep2 : r.val.tapes i = u.val.tapes i := f2.tapes i (by
        simp only [Geometric.workspace,Finset.mem_insert,Finset.mem_singleton];omega)
      have hkeep1 : u.val.tapes i = s.val.tapes i := f1.tapes i (by
        simp [NatAssign.changes,loadInputs,NatAssign.Instruction.target];omega)
      simpa only [searched,ite_eq_right hg] using word_of_eq (hkeep2.trans hkeep1)
        (hbank i (Finset.mem_union_left _ hiExtra))
  have midWidth : ∀ i ∈ ids extra, (searched v a b (v c) (v d) N i).bits.length ≤ W := by
    intro i hi
    by_cases hg : i ∈ Geometric.ids
    · simpa only [searched,ite_eq_left hg] using Geometric.values_width a b (v c) (v d) N N A C le_rfl
        haW hbW ((hwidth c (Finset.mem_union_left _ hc)).trans hB)
        ((hwidth d (Finset.mem_union_left _ hd)).trans hB) i
    · have hgExtra : i ∉ Geometric.extra := fun hh => hg (Finset.mem_union_left _ hh)
      simpa only [searched,ite_eq_right hg] using
        (hwidth i ((Finset.mem_union.mp hi).resolve_right hgExtra)).trans hBW
  have hfinish : ∀ inst ∈ finish num den, inst.Valid (ids extra) := by
    simp [finish,clearGeo,Rational.clear,NatAssign.Instruction.Valid,ids,Rational.ids,Rational.common,
      Geometric.extra,hnum,hden]
    omega
  obtain ⟨c3,t,e3,p3,b3,s3,f3⟩ := NatAssign.executes (ids extra) (ids_ge extra hextra)
    (finish num den) hfinish (searched v a b (v c) (v d) N) input tape r midBank b2.scratch
  rw [finish_values] at b3
  have hW1 : 1 ≤ W := hC.trans hCW
  have p3' : c3 ≤ finishCost W := p3.trans (NatAssign.price_bound (ids extra) (finish num den)
    hfinish (searched v a b (v c) (v d) N) W midWidth
      (by simp [finish,clearGeo,Rational.clear,NatAssign.Instruction.literalWidth,hW1]))
  have finalBank : NatAssign.Bank (Rational.ids extra) (Rational.after v num den (N,1)) t.val := by
    intro i hi
    simpa only [extend,ite_eq_right (caller_not_geo extra hextra i hi)] using b3 i (Finset.mem_union_left _ hi)
  have finalBlank : ∀ i ∈ Geometric.extra ∪ Rational.common, Blank t.val i := by
    intro i hi
    rcases Finset.mem_union.mp hi with hg | hc
    · have hh := b3 i (Finset.mem_union_right _ hg)
      simp only [extend,ite_eq_left hg] at hh
      exact (zero_word_iff_blank t.val i).mp hh
    · have hh := finalBank i (Finset.mem_union_right _ hc)
      rw [Rational.after_common v num den (N,1) i hc] at hh
      exact (zero_word_iff_blank t.val i).mp hh
  have resultWidth : ∀ i ∈ Rational.ids extra, (Rational.after v num den (N,1) i).bits.length ≤ W := by
    apply Rational.after_width extra v num den (N,1) B W hwidth hBW
    have hnWidth := midWidth 526 (by simp [ids,Geometric.extra])
    simpa [searched,Geometric.ids,Geometric.extra,Geometric.values] using And.intro hnWidth hW1
  have fload : NatAssign.changes (loadInputs a b c d) ⊆ workspace num den := by
    intro i hi
    simp [NatAssign.changes,loadInputs,NatAssign.Instruction.target,workspace,Rational.workspace,
      Rational.common,Geometric.extra] at hi ⊢
    omega
  have fgeo : Geometric.workspace ⊆ workspace num den := by
    intro i hi
    simp only [Geometric.workspace,workspace,Rational.workspace,Rational.common,Geometric.extra,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    omega
  have ffinish : NatAssign.changes (finish num den) ⊆ workspace num den := by
    intro i hi
    simp [NatAssign.changes,finish,clearGeo,Rational.clear,NatAssign.Instruction.target,workspace,
      Rational.workspace,Rational.common,Geometric.extra] at hi ⊢
    omega
  refine ⟨c1+(c2+c3),t,e1.seq (e2.seq e3),?_,finalBank,s3,finalBlank,resultWidth,
    (f1.mono fload).trans ((f2.mono fgeo).trans (f3.mono ffinish))⟩
  exact Nat.add_le_add p1' (Nat.add_le_add p2 p3')

end Maxwell.Cost.SelectedParameters.GeometricAdapter
