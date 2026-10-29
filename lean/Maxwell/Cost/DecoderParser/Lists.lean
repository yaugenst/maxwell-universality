import Maxwell.Cost.DecoderParser.Grammar
import Maxwell.Cost.Structured.Counted

namespace Maxwell.Cost.DecoderParser
open Structured

private theorem counter_frame (depth : ℕ) {s t : Store}
    (h : Counted.Frame (46+depth) s t) : Frame {18, 46+depth} s.val t.val := by
  refine ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  intro i hi
  exact h.2.2.2.2.2.1 i (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi; exact hi.2)

private theorem ready_counter (depth : ℕ) {s t : Store}
    (h : Counted.Frame (46+depth) s t) (hr : Ready (depth+1) s.val) : Ready (depth+1) t.val := by
  refine ⟨(h.2.2.2.2.2.1 10 (by omega)).trans hr.1,
    (h.2.2.2.2.2.1 11 (by omega)).trans hr.2.1,
    (h.2.2.2.2.2.1 45 (by omega)).trans hr.2.2.1, ?_⟩
  intro i hi h60
  exact (h.2.2.2.2.2.1 i (by omega)).trans (hr.2.2.2 i hi h60)

/-- The actual countdown consumes exactly one encoded element per pass.
Its binary word is read and decremented by the finite counter program. -/
theorem records_steps (element : Shape) (body : Code) (depth : ℕ)
    (price : Payload element → ℕ) (hbody : Parses element body (depth+1) price)
    (hdepth : depth+1+element.height ≤ 14)
    (values : List (Payload element)) (bits preceding suffix saved : List Bool)
    (randomTape : ℕ → Bool) (s : Store)
    (hvalue : addressValue bits = values.length)
    (hword : s.val.tapes (46+depth) = BitTape.ofList bits)
    (hhead : s.val.inputHead = preceding.length) (hready : Ready (depth+1) s.val)
    (hlog : s.val.tapes 18 = BitTape.atEnd saved) :
    ∃ (cost : ℕ) (t : Store) (finalWord : List Bool),
      Executes (preceding ++ (values.flatMap (wire element) ++ suffix)) randomTape
        (Counted.code (46+depth) body) cost s t ∧
      cost ≤ (values.length+1)*(13*bits.length+15)+(values.map price).sum ∧
      t.val.inputHead = s.val.inputHead + (values.flatMap (wire element)).length ∧
      t.val.tapes 18 = BitTape.atEnd (saved ++ values.flatMap (wire element)) ∧
      t.val.tapes (46+depth) = BitTape.ofList finalWord ∧ finalWord.length = bits.length ∧
      Frame {18,46+depth} s.val t.val := by
  induction values generalizing bits preceding saved s with
  | nil =>
    obtain ⟨t, ht, hw, hz, hf⟩ := Counted.test_executes (46+depth)
      (preceding ++ ([].flatMap (wire element) ++ suffix)) randomTape s bits hword
    have hfzero := hz.mpr hvalue
    refine ⟨_, t, subtractBit true bits, ht.seq (Executes.done hfzero), ?_, ?_, ?_, hw,
      subtractBit_length true bits, counter_frame depth hf⟩
    · simp
    · simpa using hf.2.1
    · simpa using (hf.2.2.2.2.2.1 18 (by omega)).trans hlog
  | cons x xs ih =>
    let input := preceding ++ ((x::xs).flatMap (wire element) ++ suffix)
    obtain ⟨u, hu, huw, huz, huf⟩ := Counted.test_executes (46+depth) input randomTape s bits hword
    have hpred : addressValue (subtractBit true bits) = xs.length := by
      rw [subtractBit_pred bits (by simp at hvalue; omega), hvalue]
      simp
    have htrue : u.val.registers 29 = true := by
      cases hh : u.val.registers 29 with
      | true => rfl
      | false => have := huz.mp hh; simp at hvalue; omega
    have hulog : u.val.tapes 18 = BitTape.atEnd saved :=
      (huf.2.2.2.2.2.1 18 (by omega)).trans hlog
    obtain ⟨a,v,hv,hac,hvh,hvl,hvf⟩ := hbody hdepth x preceding
      (xs.flatMap (wire element) ++ suffix) saved randomTape u (huf.2.1.trans hhead)
      (ready_counter depth huf hready) hulog
    have hvinput : preceding ++ (wire element x ++ (xs.flatMap (wire element) ++ suffix)) = input := by
      simp [input, List.append_assoc]
    rw [hvinput] at hv
    have hvcounter : v.val.tapes (46+depth) = BitTape.ofList (subtractBit true bits) :=
      (hvf.tapes (46+depth) (by simp; omega)).trans huw
    obtain ⟨b,t,fw,ht,hbc,hth,htl,htw,htlen,htf⟩ :=
      ih (subtractBit true bits) (preceding ++ wire element x) (saved ++ wire element x)
        v hpred hvcounter (by simp [hvh, huf.2.1, hhead])
        ((ready_counter depth huf hready).frame hvf) hvl
    have hi : (preceding ++ wire element x) ++ (xs.flatMap (wire element) ++ suffix) = input := by
      simp [input, List.append_assoc]
    rw [hi] at ht
    change Executes input randomTape
      (.seq (Counted.test (46+depth)) (.loop 29 (.seq body (Counted.test (46+depth))))) b v t at ht
    have hframe := (counter_frame depth huf).trans
      ((hvf.mono (by simp)).trans htf)
    cases ht with
    | seq restTest restLoop =>
      refine ⟨_, t, fw, hu.seq (Executes.more htrue (hv.seq restTest) restLoop), ?_, ?_, ?_,
        htw, htlen.trans (subtractBit_length true bits), hframe⟩
      · simp only [List.length_cons, List.map_cons, List.sum_cons, subtractBit_length] at *
        nlinarith
      · simp only [List.flatMap_cons, List.length_append, Nat.cast_add]
        have hheadU := huf.2.1
        omega
      · simpa [List.flatMap_cons, List.append_assoc] using htl

/-- Count-prefixed list parser, with a distinct literal counter per nesting
level and explicit cleanup before returning to the surrounding schema. -/
def listCode (depth : ℕ) (body : Code) : Code :=
  .seq (readNat (46+depth) 18)
    (.seq (Counted.code (46+depth) body) (clearWord (46+depth)))

def listPrice {element : Shape} (price : Payload element → ℕ)
    (values : List (Payload element)) : ℕ :=
  71*values.length.bits.length+67 +
    (values.length+1)*(13*values.length.bits.length+15)+(values.map price).sum

theorem parses_list (element : Shape) (body : Code) (depth : ℕ)
    (price : Payload element → ℕ) (hbody : Parses element body (depth+1) price) :
    Parses (.list element) (listCode depth body) depth (listPrice price) := by
  intro hd values preceding suffix saved randomTape s hh hr hl
  have hdchild : depth+1+element.height ≤ 14 := by dsimp [Shape.height] at hd; omega
  have hdlt : 46+depth < 60 := by omega
  let c := 46+depth
  obtain ⟨u,hu,huh,huw,hul,hu10,hu11,huf⟩ := readNat_steps c 18
    (by dsimp [c]; omega) (by dsimp [c]; omega) (by decide) (by decide) (by dsimp [c]; omega)
    values.length preceding (values.flatMap (wire element) ++ suffix) saved randomTape s hh
    hr.1 (hr.2.2.2 c (by rfl) hdlt) hr.2.1 hl
  have hur : Ready (depth+1) u.val := by
    refine ⟨hu10,hu11,(huf.tapes 45 (by simp [natWork,c]; omega)).trans hr.2.2.1,?_⟩
    intro i hi h60
    exact (huf.tapes i (by simp [natWork,c]; omega)).trans (hr.2.2.2 i (by omega) h60)
  obtain ⟨a,v,fw,hv,hva,hvh,hvl,hvw,hlen,hvf⟩ := records_steps element body depth price hbody hdchild values
    values.length.bits (preceding ++ Codec.nat values.length) suffix
    (saved ++ Codec.nat values.length) randomTape u (addressValue_bits _) huw
    (by simp [huh,hh]) hur hul
  obtain ⟨t,ht,htc,hth,htf⟩ := clearWord_steps c
    (preceding ++ (Codec.list (wire element) values ++ suffix)) randomTape fw v hvw
  have hi : (preceding ++ Codec.nat values.length) ++
      (values.flatMap (wire element) ++ suffix) =
      preceding ++ (Codec.list (wire element) values ++ suffix) := by
    simp [Codec.list,List.append_assoc]
  rw [hi] at hv
  have hui : preceding ++ (Codec.nat values.length ++ (values.flatMap (wire element) ++ suffix)) =
      preceding ++ (Codec.list (wire element) values ++ suffix) := by
    simp [Codec.list,List.append_assoc]
  rw [hui] at hu
  refine ⟨_,t,hu.seq (hv.seq ht),?_,?_,?_,?_⟩
  · dsimp [listPrice]
    rw [hlen]
    omega
  · simp only [wire,Codec.list,List.length_append,Nat.cast_add]
    omega
  · have hh := (htf.tapes 18 (by simp [c];omega)).trans hvl
    simpa [wire,Codec.list,List.append_assoc] using hh
  · refine ⟨htf.address.trans (hvf.address.trans huf.address),
      htf.memory.trans (hvf.memory.trans huf.memory),
      htf.randomCursor.trans (hvf.randomCursor.trans huf.randomCursor),
      htf.output.trans (hvf.output.trans huf.output),?_⟩
    intro i hi
    have hi18 : i ≠ 18 := by simpa using hi
    by_cases hic : i = c
    · subst i; exact htc.trans (hr.2.2.2 c (by rfl) hdlt).symm
    have h1 := htf.tapes i (by simpa using hic)
    have h2 := hvf.tapes i (by simp [hi18,← show c=46+depth from rfl,hic])
    by_cases hi10 : i = 10
    · subst i; exact h1.trans (h2.trans (hu10.trans hr.1.symm))
    by_cases hi11 : i = 11
    · subst i; exact h1.trans (h2.trans (hu11.trans hr.2.1.symm))
    exact h1.trans (h2.trans (huf.tapes i (by simp [natWork,hi10,hi11,hic,hi18])))

end Maxwell.Cost.DecoderParser
