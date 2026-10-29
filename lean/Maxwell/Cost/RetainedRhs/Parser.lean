import Maxwell.Cost.NormalizedRecordParser.Header
import Maxwell.Cost.Structured.Rename
import Maxwell.Cost.BinaryPrecision

/-! A literal finite parser for the exact RHS archive retained by the source
compiler. It reads work tape508 and never rebinds the immutable input. -/
namespace Maxwell.Cost.RetainedRhs
open Structured NormalizedRecordParser
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def signCopy : BitRAM := ⟨[.bitNot 360 23, .bitNot 360 360, .halt]⟩
def signCopyFinish (s : BitRAMState) : BitRAMState :=
  {s with pc := 2, registers := Function.update s.registers 360 (s.registers 23)}

private theorem signCopy_executes (input : List Bool) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call signCopy) 3 s (Store.ofState (signCopyFinish s.val)) := by
  apply Executes.call signCopy s (signCopyFinish s.val) 2
  · apply executeInstructions_sound (instructions := 2)
    simp [executeInstructions, BitRAM.next, signCopy, signCopyFinish, s.property,
      BitRAMState.setRegister]
  · rfl

private theorem rewind (target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (bits : List Bool) (s : Store) (ht : s.val.tapes target = BitTape.atEnd bits) :
    Executes input tape (.call (Rewind.program target)) (4*bits.length+6) s
      (Store.ofState (Rewind.finish target s.val)) ∧
    (Rewind.finish target s.val).tapes target = BitTape.ofList bits :=
  ⟨.call _ s _ _ (Rewind.atEnd_steps target input tape bits s.val s.property ht)
    (by simp [Rewind.program, Rewind.finish]), Rewind.finish_tape target bits s.val ht⟩

def baseCode : Code := .seq (.call signProgram)
  (.seq (readNatural 360) (.seq (readNatural 361)
    (.seq (.call (Rewind.program 360))
      (.seq (.call (Rewind.program 361)) (.call signCopy)))))

def wire (negative : Bool) (numerator denominator : ℕ) : List Bool :=
  negative :: (Codec.nat numerator ++ Codec.nat denominator)

private theorem base_executes (input : List Bool) (tape : ℕ → Bool)
    (negative : Bool) (numerator denominator : ℕ) (preceding suffix : List Bool) (s : Store)
    (hsource : s.val.tapes 85 = cursor (preceding ++ (wire negative numerator denominator ++ suffix)) preceding.length)
    (h10 : s.val.tapes 10 = BitTape.blank)
    (hnum : s.val.tapes 360 = BitTape.blank) (hden : s.val.tapes 361 = BitTape.blank) :
    ∃ cost t, Executes input tape baseCode cost s t ∧
      cost ≤ 38*(numerator.bits.length+denominator.bits.length)+53 ∧
      t.val.tapes 85 = cursor (preceding ++ (wire negative numerator denominator ++ suffix))
        (preceding.length+(wire negative numerator denominator).length) ∧
      t.val.tapes 360 = BitTape.ofList numerator.bits ∧
      t.val.tapes 361 = BitTape.ofList denominator.bits ∧
      t.val.registers 360 = negative ∧ t.val.tapes 10 = BitTape.blank ∧
      BinaryPrecision.Frame {360,361,85} s.val t.val := by
  have hbit : (s.val.tapes 85).read = some negative := by
    rw [hsource]
    simp [wire, BitTape.read, BitTape.ofList]
  let a := Store.ofState (signFinish negative s.val)
  have ea := sign_executes input tape negative s hbit
  let pn := preceding ++ [negative]
  have ha : a.val.tapes 85 = cursor (pn ++ (Codec.nat numerator ++
      (Codec.nat denominator ++ suffix))) pn.length := by
    simp [a, Store.ofState, signFinish, hsource, pn, wire, List.append_assoc]
  obtain ⟨nc,b,en,hn,b85,b10,b360,bi,b23,bf⟩ := readNatural_executes 360
    (by decide) (by decide) input tape numerator pn (Codec.nat denominator ++ suffix) a ha
    (by simpa [a,Store.ofState,signFinish] using h10)
    (by simpa [a,Store.ofState,signFinish] using hnum)
  let pd := pn ++ Codec.nat numerator
  have hb : b.val.tapes 85 = cursor (pd ++ (Codec.nat denominator ++ suffix)) pd.length := by
    simpa [pd,List.append_assoc] using b85
  obtain ⟨dc,c,ed,hd,c85,c10,c361,ci,c23,cf⟩ := readNatural_executes 361
    (by decide) (by decide) input tape denominator pd suffix b hb b10
    ((bf.tapes 361 (by decide)).trans (by simpa [a,Store.ofState,signFinish] using hden))
  have c360 : c.val.tapes 360 = BitTape.atEnd numerator.bits :=
    (cf.tapes 360 (by decide)).trans b360
  obtain ⟨er,r360⟩ := rewind 360 input tape numerator.bits c c360
  let d := Store.ofState (Rewind.finish 360 c.val)
  have d361 : d.val.tapes 361 = BitTape.atEnd denominator.bits := by
    simpa [d,Store.ofState,Rewind.finish] using c361
  obtain ⟨es,r361⟩ := rewind 361 input tape denominator.bits d d361
  let e := Store.ofState (Rewind.finish 361 d.val)
  let t := Store.ofState (signCopyFinish e.val)
  have et := signCopy_executes input tape e
  have eh : e.val.registers 23 = negative := by
    simpa [e,d,a,Store.ofState,Rewind.finish,signFinish] using c23.trans b23
  have tailKeep (i : ℕ) (hi : i ≠ 360) (hj : i ≠ 361) :
      t.val.tapes i = c.val.tapes i := by
    simp [t,e,d,Store.ofState,signCopyFinish,Rewind.finish,hi,hj]
  refine ⟨4+(nc+(dc+(4*numerator.bits.length+6+(4*denominator.bits.length+6+3)))),t,
    ea.seq (en.seq (ed.seq (er.seq (es.seq et)))),by omega,?_,?_,?_,?_,?_,?_⟩
  · rw [tailKeep 85 (by decide) (by decide),c85]
    simp [pd,pn,wire,List.append_assoc]
    omega
  · simpa [t,e,d,Store.ofState,signCopyFinish,Rewind.finish] using r360
  · exact r361
  · simpa [t,Store.ofState,signCopyFinish] using eh
  · exact (tailKeep 10 (by decide) (by decide)).trans c10
  · refine ⟨cf.address.trans bf.address,?_,cf.memory.trans bf.memory,
      cf.randomCursor.trans bf.randomCursor,cf.output.trans bf.output,?_⟩
    · exact ci.trans bi
    · intro i hi
      have hi360 : i ≠ 360 := by simp_all
      have hi361 : i ≠ 361 := by simp_all
      have hi85 : i ≠ 85 := by simp_all
      exact (tailKeep i hi360 hi361).trans ((cf.tapes i (by simp [hi361,hi85])).trans
        ((bf.tapes i (by simp [hi360,hi85])).trans (by simp [a,Store.ofState,signFinish,hi85])))

/-- A fixed renaming uses only tape379 for the unary counter and reads the
reserved exact RHS archive508. -/
def ports : Equiv.Perm ℕ := (Equiv.swap 85 508).trans (Equiv.swap 10 379)

def code : Code := .call (baseCode.compile.renameTapes ports)

def price (q : ℚ) : ℕ := 38*(q.num.natAbs.bits.length+q.den.bits.length)+54

/-- Parse one exact original rational from the retained RHS. All archive
cells survive, and its actual head advances to the next record. -/
theorem executes (input : List Bool) (tape : ℕ → Bool)
    (q : ℚ) (preceding suffix : List Bool) (s : Store)
    (hsource : s.val.tapes 508 = cursor (preceding ++ (Codec.rat q ++ suffix)) preceding.length)
    (h379 : s.val.tapes 379 = BitTape.blank)
    (hnum : s.val.tapes 360 = BitTape.blank) (hden : s.val.tapes 361 = BitTape.blank) :
    ∃ cost t, Executes input tape code cost s t ∧ cost ≤ price q ∧
      t.val.tapes 508 = cursor (preceding ++ (Codec.rat q ++ suffix))
        (preceding.length+(Codec.rat q).length) ∧
      t.val.tapes 360 = BitTape.ofList q.num.natAbs.bits ∧
      t.val.tapes 361 = BitTape.ofList q.den.bits ∧
      t.val.registers 360 = decide (q.num < 0) ∧ t.val.tapes 379 = BitTape.blank ∧
      BinaryPrecision.Frame {360,361,508} s.val t.val := by
  let p := ports
  have h85 : p 85 = 508 := by decide
  have h10 : p 10 = 379 := by decide
  have h360 : p 360 = 360 := by decide
  have h361 : p 361 = 361 := by decide
  have h508 : p.symm 508 = 85 := by decide
  have hzero : p.symm 379 = 10 := by decide
  have h360' : p.symm 360 = 360 := by decide
  have h361' : p.symm 361 = 361 := by decide
  have hwire : wire (decide (q.num < 0)) q.num.natAbs q.den = Codec.rat q := by
    simp [wire,Codec.rat,Codec.int]
  obtain ⟨cost,t,he,hcost,hs,hn,hd,hsg,hz,hf⟩ := base_executes input tape
    (decide (q.num < 0)) q.num.natAbs q.den preceding suffix (s.renameTapes p.symm)
    (by simpa only [Store.renameTapes,BitRAMState.renameTapes,Equiv.symm_symm,Function.comp_apply,h85,hwire] using hsource)
    (by simpa [Store.renameTapes,BitRAMState.renameTapes,h10] using h379)
    (by simpa [Store.renameTapes,BitRAMState.renameTapes,h360] using hnum)
    (by simpa [Store.renameTapes,BitRAMState.renameTapes,h361] using hden)
  have er := he.renamed_call p
  rw [Store.renameTapes_symm] at er
  refine ⟨cost+1,t.renameTapes p,er,by dsimp [price];omega,?_,?_,?_,hsg,?_,?_⟩
  · simpa only [Store.renameTapes,BitRAMState.renameTapes,Function.comp_apply,h508,hwire] using hs
  · simpa [Store.renameTapes,BitRAMState.renameTapes,h360'] using hn
  · simpa [Store.renameTapes,BitRAMState.renameTapes,h361'] using hd
  · simpa [Store.renameTapes,BitRAMState.renameTapes,hzero] using hz
  · refine ⟨hf.address,hf.inputHead,hf.memory,hf.randomCursor,hf.output,?_⟩
    intro i hi
    have hpi : p.symm i ∉ ({360,361,85} : Finset ℕ) := by
      intro hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with h | h | h
      · have heq := congrArg p h
        simp only [Equiv.apply_symm_apply,h360] at heq
        exact hi (by simp [heq])
      · have heq := congrArg p h
        simp only [Equiv.apply_symm_apply,h361] at heq
        exact hi (by simp [heq])
      · have heq := congrArg p h
        simp only [Equiv.apply_symm_apply,h85] at heq
        exact hi (by simp [heq])
    simpa [Store.renameTapes,BitRAMState.renameTapes,Function.comp_def] using hf.tapes (p.symm i) hpi

/-- Restore the two output tapes to the same exact blank state required by
another parse. Both scans and reverse erasures are charged. -/
def cleanupCode : Code := .seq (DecoderParser.clearWord 360) (DecoderParser.clearWord 361)

theorem cleanup_executes (input : List Bool) (tape : ℕ → Bool)
    (numerator denominator : ℕ) (s : Store)
    (hn : s.val.tapes 360 = BitTape.ofList numerator.bits)
    (hd : s.val.tapes 361 = BitTape.ofList denominator.bits) :
    ∃ t, Executes input tape cleanupCode
      (11*numerator.bits.length+10+(11*denominator.bits.length+10)) s t ∧
      t.val.tapes 360 = BitTape.blank ∧ t.val.tapes 361 = BitTape.blank ∧
      BinaryPrecision.Frame {360,361} s.val t.val := by
  obtain ⟨a,ea,a360,ai,af⟩ := DecoderParser.clearWord_steps 360 input tape numerator.bits s hn
  obtain ⟨t,et,t361,ti,tf⟩ := DecoderParser.clearWord_steps 361 input tape denominator.bits a
    ((af.tapes 361 (by decide)).trans hd)
  refine ⟨t,ea.seq et,(tf.tapes 360 (by decide)).trans a360,t361,?_⟩
  exact ⟨tf.address.trans af.address,ti.trans ai,tf.memory.trans af.memory,
    tf.randomCursor.trans af.randomCursor,tf.output.trans af.output,
    fun i hi => (tf.tapes i (by simp_all)).trans (af.tapes i (by simp_all))⟩

/-- The compiled finite parser terminates within its bit-operation cap. -/
theorem run (input : List Bool) (tape : ℕ → Bool)
    (q : ℚ) (preceding suffix : List Bool) (s : Store)
    (hsource : s.val.tapes 508 = cursor (preceding ++ (Codec.rat q ++ suffix)) preceding.length)
    (h379 : s.val.tapes 379 = BitTape.blank)
    (hnum : s.val.tapes 360 = BitTape.blank) (hden : s.val.tapes 361 = BitTape.blank) :
    ∃ t : Store, (runPriced (code.compile.next input tape) (price q+1) s.val).finished = some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (price q+1) s.val).instructions ≤ price q ∧
      t.val.tapes 508 = cursor (preceding ++ (Codec.rat q ++ suffix))
        (preceding.length+(Codec.rat q).length) ∧
      t.val.tapes 360 = BitTape.ofList q.num.natAbs.bits ∧
      t.val.tapes 361 = BitTape.ofList q.den.bits ∧
      t.val.registers 360 = decide (q.num < 0) ∧ t.val.tapes 379 = BitTape.blank ∧
      BinaryPrecision.Frame {360,361,508} s.val t.val := by
  obtain ⟨cost,t,he,hcost,ht⟩ := executes input tape q preceding suffix s hsource h379 hnum hden
  have hr := he.compiled_run (price q+1) (by omega)
  exact ⟨t,hr.1,hr.2 ▸ hcost,ht⟩

end Maxwell.Cost.RetainedRhs
