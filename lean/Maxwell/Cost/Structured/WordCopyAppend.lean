import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.WordCall
import Maxwell.Cost.BankArray.Common

/-! Copy a stored word and append a fixed literal suffix, charging all tape
motion and writes. Useful for clocks and record construction in either model. -/
namespace Maxwell.Cost.Structured.WordCopyAppend
open RationalAccumulator (Blank)

def code (source target : ℕ) (suffix : List Bool) : Code :=
  .seq (.call (WordTransfer.clone source target))
    (.seq (.call (ScanForward.program target))
      (.seq (BinaryPrecision.writeCode target suffix) (.call (Rewind.program target))))

theorem executes (source target : ℕ) (different : source≠target)
    (input : List Bool) (tape : ℕ→Bool) (bits suffix : List Bool) (s : Store)
    (stored : BankArray.Word s.val source bits) (blank : Blank s.val target) :
    ∃t,Executes input tape (code source target suffix) (24*bits.length+10*suffix.length+28) s t ∧
      BankArray.Word t.val target (bits++suffix) ∧ BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨origin,hs⟩:=stored
  obtain ⟨dest,hd⟩:=blank
  obtain ⟨a,ea,atapes,af⟩:=WordCall.clone source target different input tape bits origin dest s hs hd
  have aWord : a.val.tapes target=BitTape.shifted bits dest:=by simp [atapes]
  have scanned:=ScanForward.shifted_steps target dest input tape bits a.val a.property aWord
  let b:=Store.ofState (ScanForward.finish target bits.length a.val)
  have eb : Executes input tape (.call (ScanForward.program target)) (5*bits.length+4) a b:=
    .call _ _ _ _ scanned.1 rfl
  obtain ⟨c,ec,hc,fc⟩:=BinaryPrecision.write_executes target input tape suffix bits dest b scanned.2.1
  have rewound:=WordTransfer.rewind_shifted target dest input tape (bits++suffix) c.val c.property hc
  let t:=Store.ofState (Rewind.finishAt target dest c.val)
  have et : Executes input tape (.call (Rewind.program target)) (4*(bits++suffix).length+6) c t:=
    .call _ _ _ _ rewound.1 rfl
  have fa : BinaryPrecision.Frame {target} s.val a.val:=
    ⟨af.1,af.2.1,af.2.2.1,af.2.2.2.1,af.2.2.2.2.1,by
      intro i hi
      have ne : i≠target:=by simpa using hi
      simp [atapes,ne]⟩
  have fb : BinaryPrecision.Frame {target} a.val b.val:=
    ⟨scanned.2.2.1,scanned.2.2.2.1,scanned.2.2.2.2.1,scanned.2.2.2.2.2.1,
      scanned.2.2.2.2.2.2.1,by
      intro i hi
      have ne : i≠target:=by simpa using hi
      exact scanned.2.2.2.2.2.2.2.1 i ne ne⟩
  have ft : BinaryPrecision.Frame {target} c.val t.val:=by
    refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
    intro i hi
    have ne : i≠target:=by simpa using hi
    simp [t,Store.ofState,Rewind.finishAt,ne]
  refine ⟨t,?_,⟨dest,rewound.2⟩,fa.trans (fb.trans (fc.trans ft))⟩
  convert ea.seq (eb.seq (ec.seq et)) using 1 <;> first | rfl | simp only [List.length_append];omega

#print axioms executes
end Maxwell.Cost.Structured.WordCopyAppend
