import Maxwell.Cost.DecoderParser.Schema

namespace Maxwell.Cost.DecoderParser
open Structured

theorem Ready.retained {depth target : ℕ} {s t : BitRAMState}
    (hr : Ready depth s) (hf : Frame {18,target} s t) (ht : target ≤ 44)
    (h10 : target ≠ 10) (h11 : target ≠ 11) : Ready depth t := by
  refine ⟨(hf.tapes 10 (by simp [h10.symm])).trans hr.1,
    (hf.tapes 11 (by simp [h11.symm])).trans hr.2.1,
    (hf.tapes 45 (by simp;omega)).trans hr.2.2.1,?_⟩
  intro i hi h60
  exact (hf.tapes i (by simp;omega)).trans (hr.2.2.2 i hi h60)

theorem retainedNat_steps (target : ℕ) (ht : 40 ≤ target ∧ target ≤ 44)
    (n : ℕ) (preceding suffix saved : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (hh : s.val.inputHead = preceding.length) (hr : Ready 0 s.val)
    (hb : s.val.tapes target = BitTape.blank) (hl : s.val.tapes 18 = BitTape.atEnd saved) :
    ∃ t : Store, Executes (preceding ++ (Codec.nat n ++ suffix)) randomTape
      (readNat target 18) (60*n.bits.length+57) s t ∧
      t.val.inputHead = s.val.inputHead + (Codec.nat n).length ∧
      t.val.tapes 18 = BitTape.atEnd (saved ++ Codec.nat n) ∧
      t.val.tapes target = BitTape.ofList n.bits ∧ Ready 0 t.val ∧ Frame {18,target} s.val t.val := by
  obtain ⟨t,he,hh',hw,hl',h10,h11,hf⟩ := readNat_steps target 18 (by omega) (by omega)
    (by decide) (by decide) (by omega) n preceding suffix saved randomTape s hh hr.1 hb hr.2.1 hl
  have hframe : Frame {18,target} s.val t.val := by
    refine ⟨hf.address,hf.memory,hf.randomCursor,hf.output,?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    by_cases hi10 : i = 10
    · subst i;exact h10.trans hr.1.symm
    by_cases hi11 : i = 11
    · subst i;exact h11.trans hr.2.1.symm
    exact hf.tapes i (by simp [natWork,hi.1,hi.2,hi10,hi11])
  exact ⟨t,he,hh',hl',hw,hr.retained hframe ht.2 (by omega) (by omega),hframe⟩

/-- Copy one binary metadata word while restoring the source head. -/
def copyWord (source target : ℕ) : Code := .seq (.call (Copy.program source target))
  (.seq (.call (Rewind.program source)) (.call (Rewind.program target)))

theorem copyWord_steps (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (bits : List Bool) (s : Store)
    (hs : s.val.tapes source = BitTape.ofList bits) (ht : s.val.tapes target = BitTape.blank) :
    ∃ t : Store, Executes input randomTape (copyWord source target) (15*bits.length+16) s t ∧
      t.val.tapes source = BitTape.ofList bits ∧ t.val.tapes target = BitTape.ofList bits ∧
      t.val.inputHead = s.val.inputHead ∧ Frame {target} s.val t.val := by
  obtain ⟨u,hu,hup,hw,hsrc,hf⟩ := Copy.simulation source target hne input randomTape s.val bits
    s.property (by rw [hs]; exact BitTape.ofList_represents bits)
  have hsu : u.tapes source = BitTape.atEnd bits := by
    simpa [hs,BitTape.ofList,BitTape.atEnd] using hsrc
  have htu : u.tapes target = BitTape.atEnd bits := by
    have hh := hw.blank (show s.val.tapes target = {BitTape.blank with head := (0:ℤ)} by
      simpa [BitTape.blank] using ht)
    simpa [BitTape.shiftedEnd,BitTape.shifted,BitTape.atEnd,BitTape.ofList] using hh
  have e1 := Executes.call (Copy.program source target) s u _ hu (by simp [Copy.program,hup])
  let v := Store.ofState (Rewind.finish source (Store.ofState u).val)
  have e2 := Executes.call (Rewind.program source) (Store.ofState u)
    (Rewind.finish source (Store.ofState u).val) _
    (Rewind.atEnd_steps source input randomTape bits (Store.ofState u).val rfl hsu)
    (by simp [Rewind.program,Rewind.finish])
  have htv : v.val.tapes target = BitTape.atEnd bits := by
    simpa [v,Store.ofState,Rewind.finish,hne.symm] using htu
  have e3 := Executes.call (Rewind.program target) v (Rewind.finish target v.val) _
    (Rewind.atEnd_steps target input randomTape bits v.val v.property htv)
    (by simp [Rewind.program,Rewind.finish])
  let t := Store.ofState (Rewind.finish target v.val)
  have hvs : v.val.tapes source = BitTape.ofList bits :=
    Rewind.finish_tape source bits (Store.ofState u).val hsu
  have hts : t.val.tapes source = BitTape.ofList bits := by
    simpa [t,Store.ofState,Rewind.finish,hne] using hvs
  refine ⟨t,?_,hts,Rewind.finish_tape target bits v.val htv,hf.2.1,?_⟩
  · convert e1.seq (e2.seq e3) using 1 <;> first | rfl | omega
  · refine ⟨hf.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
    intro i hi
    have hit : i ≠ target := by simpa using hi
    by_cases his : i = source
    · subst i; exact hts.trans hs.symm
    simpa [t,v,Store.ofState,Rewind.finish,hit,his] using hf.2.2.2.2.2.1 i his hit

/-- The top-level decoder list count is retained independently of its
working countdown copy. -/
def retainedList (target depth : ℕ) (body : Code) : Code :=
  .seq (readNat target 18) (.seq (copyWord target (46+depth))
    (.seq (Counted.code (46+depth) body) (clearWord (46+depth))))

def retainedListPrice {element : Shape} (p : Payload element → ℕ)
    (xs : List (Payload element)) : ℕ :=
  listPrice p xs + 15*xs.length.bits.length+16

theorem retainedList_steps (target depth : ℕ) (htarget : 40 ≤ target ∧ target ≤ 44)
    (element : Shape) (body : Code) (p : Payload element → ℕ)
    (hbody : Parses element body (depth+1) p)
    (hdepth : depth+1+element.height ≤ 14)
    (xs : List (Payload element)) (preceding suffix saved : List Bool)
    (randomTape : ℕ → Bool) (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hready : Ready depth s.val) (hblank : s.val.tapes target = BitTape.blank)
    (hlog : s.val.tapes 18 = BitTape.atEnd saved) :
    ∃ (cost : ℕ) (t : Store),
      Executes (preceding ++ (Codec.list (wire element) xs ++ suffix)) randomTape
        (retainedList target depth body) cost s t ∧ cost ≤ retainedListPrice p xs ∧
      t.val.inputHead = s.val.inputHead + (Codec.list (wire element) xs).length ∧
      t.val.tapes 18 = BitTape.atEnd (saved ++ Codec.list (wire element) xs) ∧
      t.val.tapes target = BitTape.ofList xs.length.bits ∧
      Frame {18,target} s.val t.val := by
  have hdlt : 46+depth < 60 := by omega
  let c := 46+depth
  let input := preceding ++ (Codec.list (wire element) xs ++ suffix)
  obtain ⟨u,hu,huh,huw,hul,hu10,hu11,huf⟩ := readNat_steps target 18
    (by omega) (by omega) (by decide) (by decide) (by omega)
    xs.length preceding (xs.flatMap (wire element) ++ suffix) saved randomTape s hhead
    hready.1 hblank hready.2.1 hlog
  have hui : preceding ++ (Codec.nat xs.length ++ (xs.flatMap (wire element) ++ suffix)) = input := by
    simp [input,Codec.list,List.append_assoc]
  rw [hui] at hu
  have hub : u.val.tapes c = BitTape.blank :=
    (huf.tapes c (by simp [natWork,c];omega)).trans (hready.2.2.2 c (by rfl) hdlt)
  obtain ⟨v,hv,hvs,hvc,hvh,hvf⟩ := copyWord_steps target c (by dsimp [c];omega)
    input randomTape xs.length.bits u huw hub
  have hvr : Ready (depth+1) v.val := by
    refine ⟨(hvf.tapes 10 (by simp [c];omega)).trans hu10,
      (hvf.tapes 11 (by simp [c];omega)).trans hu11,?_,?_⟩
    · exact (hvf.tapes 45 (by simp [c];omega)).trans
        ((huf.tapes 45 (by simp [natWork];omega)).trans hready.2.2.1)
    · intro i hi h60
      exact (hvf.tapes i (by simp [c];omega)).trans
        ((huf.tapes i (by simp [natWork];omega)).trans (hready.2.2.2 i (by omega) h60))
  have hvl : v.val.tapes 18 = BitTape.atEnd (saved ++ Codec.nat xs.length) :=
    (hvf.tapes 18 (by simp [c];omega)).trans hul
  obtain ⟨a,w,fw,hw,hwa,hwh,hwl,hwc,hwlen,hwf⟩ := records_steps element body depth p hbody hdepth xs
    xs.length.bits (preceding ++ Codec.nat xs.length) suffix (saved ++ Codec.nat xs.length)
    randomTape v (addressValue_bits _) hvc (by simp [hvh,huh,hhead]) hvr hvl
  have hwi : (preceding ++ Codec.nat xs.length) ++ (xs.flatMap (wire element) ++ suffix) = input := by
    simp [input,Codec.list,List.append_assoc]
  rw [hwi] at hw
  obtain ⟨t,ht,htc,hth,htf⟩ := clearWord_steps c input randomTape fw w hwc
  have htarget' : t.val.tapes target = BitTape.ofList xs.length.bits :=
    (htf.tapes target (by simp [c];omega)).trans
      ((hwf.tapes target (by simp;omega)).trans hvs)
  refine ⟨_,t,hu.seq (hv.seq (hw.seq ht)),?_,?_,?_,htarget',?_⟩
  · dsimp [retainedListPrice,listPrice];rw [hwlen];omega
  · simp only [Codec.list,List.length_append,Nat.cast_add];omega
  · have hh := (htf.tapes 18 (by simp [c];omega)).trans hwl
    simpa [Codec.list,List.append_assoc] using hh
  · refine ⟨htf.address.trans (hwf.address.trans (hvf.address.trans huf.address)),
      htf.memory.trans (hwf.memory.trans (hvf.memory.trans huf.memory)),
      htf.randomCursor.trans (hwf.randomCursor.trans (hvf.randomCursor.trans huf.randomCursor)),
      htf.output.trans (hwf.output.trans (hvf.output.trans huf.output)),?_⟩
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
    by_cases hic : i = c
    · subst i;exact htc.trans (hready.2.2.2 c (by rfl) hdlt).symm
    have h1 := htf.tapes i (by simpa using hic)
    have h2 := hwf.tapes i (by simp [hi.1,← show c=46+depth from rfl,hic])
    have h3 := hvf.tapes i (by simpa using hic)
    by_cases hi10 : i = 10
    · subst i;exact h1.trans (h2.trans (h3.trans (hu10.trans hready.1.symm)))
    by_cases hi11 : i = 11
    · subst i;exact h1.trans (h2.trans (h3.trans (hu11.trans hready.2.1.symm)))
    exact h1.trans (h2.trans (h3.trans
      (huf.tapes i (by simp [natWork,hi10,hi11,hi.1,hi.2]))))

end Maxwell.Cost.DecoderParser
