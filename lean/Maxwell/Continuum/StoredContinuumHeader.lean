import Maxwell.Continuum.StoredNaturalEmission
import Maxwell.Continuum.ContinuumDescription

/-! The eight actual continuum header words are emitted by one fixed program.
The caller supplies stored runtime words, not a precomputed output bit list. -/
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
noncomputable def storedHeaderValues (p : Maxwell.Source.Parameters) (S : Maxwell.Source.SparseSystem)
    (hm : 0<S.nnz) (i : ℕ) : ℕ := (headerNats p S hm)[i-720]?.getD 0

private theorem eight_words (xs : List ℕ) (hlen : xs.length=8) :
    StoredNatural.bits StoredNatural.continuumHeaderPorts (fun i=>(xs[i-720]?).getD 0)=
      xs.flatMap Maxwell.Codec.nat := by
  have hm : StoredNatural.continuumHeaderPorts.map (fun i=>(xs[i-720]?).getD 0)=xs := by
    apply List.ext_getElem
    · simpa only [List.length_map,StoredNatural.continuumHeaderPorts,List.length_cons,List.length_nil] using hlen.symm
    · intro i hi hj
      have hi8 : i<8 := by simpa only [List.length_map,StoredNatural.continuumHeaderPorts,
        List.length_cons,List.length_nil] using hi
      have hp : StoredNatural.continuumHeaderPorts[i]'(by simpa only [List.length_map] using hi)=720+i := by
        interval_cases i <;> rfl
      simp only [List.getElem_map,hp,Nat.add_sub_cancel_left,List.getElem?_eq_getElem hj,Option.getD_some]
  change StoredNatural.continuumHeaderPorts.flatMap
    (fun i=>Maxwell.Codec.nat ((xs[i-720]?).getD 0))=_
  rw [←List.flatMap_map,hm]

theorem storedHeaderBits (p : Maxwell.Source.Parameters) (S : Maxwell.Source.SparseSystem)
    (hm : 0<S.nnz) :
    StoredNatural.bits StoredNatural.continuumHeaderPorts (storedHeaderValues p S hm)=
      (headerNats p S hm).flatMap Maxwell.Codec.nat := by
  exact eight_words (headerNats p S hm) rfl

theorem storedHeader_executes (p : Maxwell.Source.Parameters) (S : Maxwell.Source.SparseSystem)
    (hm : 0<S.nnz) (B : ℕ)
    (hw : ∀i∈StoredNatural.continuumHeaderPorts,(storedHeaderValues p S hm i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : ∀i∈StoredNatural.continuumHeaderPorts,
      RationalAccumulator.Word s.val i (storedHeaderValues p S hm i)) :
    ∃cost t,Executes input tape StoredNatural.continuumHeaderCode cost s t ∧ cost≤160*B+193 ∧
      t.val.output=((headerNats p S hm).flatMap Maxwell.Codec.nat).reverse++s.val.output ∧
      EmitNatural.Frame s t := by
  obtain ⟨cost,t,ex,hc,out,frame⟩ := StoredNatural.continuumHeader_executes
    (storedHeaderValues p S hm) B hw input tape s hs
  exact ⟨cost,t,ex,hc,by simpa only [storedHeaderBits] using out,frame⟩

#print axioms storedHeader_executes
end Maxwell.Continuum.RealizationParameters
