import Maxwell.Cost.SourceCircuit.InitializeMetadata.Padding

namespace Maxwell.Cost.SourceCircuit.InitializeMetadata
open Structured
open RationalAccumulator (Blank Word word_of_eq blank_of_eq)

def banks : Finset ℕ := {37,90,91,92,93,95,100,107,108,109}
def work : Finset ℕ := {0,1,2,3} ∪ banks
def code : Code := .seq exponentCode (.seq clockCode
  (.seq (packCode 92 91) (.seq (packCode 19 95) (.call (WordTransfer.clone 19 100)))))

structure Result (n m p : ℕ) (s : BitRAMState) : Prop where
  scratch : BankArray.Scratch s
  seven : Blank s 7
  temporary : Blank s 37
  widthWord : Word s 90 (width m p)
  zeroBase : Word s 92 0
  zeroIndex : BankArray.Word s 91 (List.replicate (width m p) false)
  clock : Word s 93 (2^exponent m p)
  next : BankArray.Word s 95 (FixedWidth.bits (width m p) n.bits)
  counter : Word s 100 n
  cleared107 : Blank s 107
  cleared108 : Blank s 108
  cleared109 : Blank s 109

theorem executes (input : List Bool) (tape : ℕ → Bool) (n m p : ℕ) (hn : n ≤ m)
    (s : Store) (hd : Word s.val 19 n) (hm : Word s.val 79 m) (hp : Word s.val 84 p)
    (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (hb : ∀ i ∈ banks, Blank s.val i) :
    ∃ cost t, Executes input tape code cost s t ∧
      cost ≤ 20000*(m.size+p.size+6)^2 ∧ Result n m p t.val ∧ Preservation work s.val t.val := by
  have hbex (i : ℕ) (hi : i ∈ exponentWork) : Blank s.val i := by
    by_cases hsmall : i < 4
    · interval_cases i
      · exact hs.1
      · exact hs.2.1
      · exact hs.2.2.1
      · exact hs.2.2.2.1
    · apply hb i
      simp only [exponentWork, banks, Finset.mem_insert,Finset.mem_singleton] at hi ⊢
      omega
  obtain ⟨ac,a,ea,hac,ha90,ha107,ha108,hasmall,fa⟩ := exponent_executes input tape m p s hm hp hbex
  obtain ⟨bc,b,eb,hbc,hb90,hb93,hb107,hb108,hb109,fb⟩ := clock_executes input tape m p a ha90 ha107 ha108
    (blank_of_eq (fa.tapes 93 (by decide)) (hb 93 (by decide)))
    (blank_of_eq (fa.tapes 109 (by decide)) (hb 109 (by decide)))
  have fab : Frame work s.val b.val := (fa.mono (by decide)).trans (fb.mono (by decide))
  have bkeep (i : ℕ) (hi : i ∉ work) : b.val.tapes i = s.val.tapes i := fab.tapes i hi
  have bkeepBank (i : ℕ) (ha : i ∉ exponentWork) (hc : i ∉ clockWork) :
      b.val.tapes i = s.val.tapes i := (fb.tapes i hc).trans (fa.tapes i ha)
  have bs : BankArray.Scratch b.val := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact blank_of_eq (fb.tapes 0 (by decide)) (hasmall 0 (by decide))
    · exact blank_of_eq (fb.tapes 1 (by decide)) (hasmall 1 (by decide))
    · exact blank_of_eq (fb.tapes 2 (by decide)) (hasmall 2 (by decide))
    · exact blank_of_eq (fb.tapes 3 (by decide)) (hasmall 3 (by decide))
    · exact blank_of_eq (bkeep 5 (by decide)) hs.2.2.2.2.1
    · exact blank_of_eq (bkeep 6 (by decide)) hs.2.2.2.2.2.1
    · exact blank_of_eq (bkeep 8 (by decide)) hs.2.2.2.2.2.2.1
    · exact blank_of_eq (bkeep 9 (by decide)) hs.2.2.2.2.2.2.2
  have bz : Word b.val 92 0 := (RationalAccumulator.zero_word_iff_blank _ _).mpr
    (blank_of_eq (bkeepBank 92 (by decide) (by decide)) (hb 92 (by decide)))
  have hclockLength : (2^exponent m p).bits.length = width m p := by
    rw [Nat.size_eq_bits_len,Nat.size_pow]; rfl
  have hclockPos : 0 < (2^exponent m p).bits.length := by rw [hclockLength]; exact width_pos m p
  obtain ⟨zc,z,hzc,ez,hz91,zs,z7,z37,fz⟩ := pack 92 91 (by decide) (by decide) (by decide)
    input tape (Nat.bits 0) (2^exponent m p).bits hclockPos (by simp) b bz
    (by simpa only [RationalAccumulator.Word,BankArray.Word] using hb93)
    (blank_of_eq (bkeepBank 91 (by decide) (by decide)) (hb 91 (by decide)))
    (blank_of_eq (bkeep 7 (by decide)) h7)
    (blank_of_eq (bkeepBank 37 (by decide) (by decide)) (hb 37 (by decide))) bs
  have fsz : Preservation work s.val z.val :=
    (preservation_frame fab).trans (fz.mono (by decide))
  have z19 : Word z.val 19 n := word_of_eq (fsz.tapes 19 (by decide) (by decide)) hd
  have z93 : Word z.val 93 (2^exponent m p) :=
    word_of_eq (fz.tapes 93 (by decide) (by decide)) hb93
  have hfit : n.bits.length ≤ (2^exponent m p).bits.length := by
    rw [hclockLength,Nat.size_eq_bits_len]
    have hh := Nat.size_le_size hn
    dsimp [width,exponent]
    omega
  obtain ⟨nc,u,hnc,eu,hu95,us,u7,u37,fu⟩ := pack 19 95 (by decide) (by decide) (by decide)
    input tape n.bits (2^exponent m p).bits hclockPos hfit z z19
    (by simpa only [RationalAccumulator.Word,BankArray.Word] using z93)
    (blank_of_eq ((fz.tapes 95 (by decide) (by decide)).trans
      (bkeepBank 95 (by decide) (by decide))) (hb 95 (by decide))) z7 z37 zs
  have fsu : Preservation work s.val u.val := fsz.trans (fu.mono (by decide))
  obtain ⟨t,et,ht100,ft,ftsmall⟩ := DecoderConstants.cloneStored 19 100 (by decide) (by decide)
    (by decide) input tape n u
    (word_of_eq (fsu.tapes 19 (by decide) (by decide)) hd)
    (blank_of_eq ((fu.tapes 100 (by decide) (by decide)).trans
      ((fz.tapes 100 (by decide) (by decide)).trans
        (bkeepBank 100 (by decide) (by decide)))) (hb 100 (by decide)))
  have tk (i : ℕ) (hi : i ≠ 100) : t.val.tapes i = u.val.tapes i := by
    by_cases hsmall : i < 4
    · exact ftsmall i hsmall
    · exact ft.2.2.2.2.2.1 i (by omega) hi
  have ft' : Preservation work u.val t.val :=
    ⟨ft.2.1,ft.2.2.1,ft.2.2.2.1,ft.2.2.2.2.1,fun i _ hi => tk i (by
      simp only [work,banks,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
      omega)⟩
  refine ⟨_,t,ea.seq (eb.seq (ez.seq (eu.seq et))),?_,?_,fsu.trans ft'⟩
  · rw [hclockLength] at hzc hnc
    have hnsize := Nat.size_le_size hn
    simp only [Nat.size_eq_bits_len]
    dsimp [width,exponent] at hbc hzc hnc
    nlinarith only [hac,hbc,hzc,hnc,hnsize]
  · have tb (i : ℕ) (h100 : i ≠ 100) (h37 : i ≠ 37) (h95 : i ≠ 95) (h91 : i ≠ 91)
        (hi : i = 4 ∨ 10 ≤ i) : t.val.tapes i = b.val.tapes i :=
      (tk i h100).trans ((fu.tapes i hi (by simp; omega)).trans (fz.tapes i hi (by simp; omega)))
    refine ⟨scratch_transport us (fun i hi => tk i (by omega)),
      blank_of_eq (tk 7 (by decide)) u7,blank_of_eq (tk 37 (by decide)) u37,
      word_of_eq (tb 90 (by decide) (by decide) (by decide) (by decide) (by decide)) hb90,
      word_of_eq (tb 92 (by decide) (by decide) (by decide) (by decide) (by decide)) bz,
      ?_,word_of_eq (tb 93 (by decide) (by decide) (by decide) (by decide) (by decide)) hb93,
      ?_,ht100,
      blank_of_eq (tb 107 (by decide) (by decide) (by decide) (by decide) (by decide)) hb107,
      blank_of_eq (tb 108 (by decide) (by decide) (by decide) (by decide) (by decide)) hb108,
      blank_of_eq (tb 109 (by decide) (by decide) (by decide) (by decide) (by decide)) hb109⟩
    · have hz := BankArray.word_of_eq ((tk 91 (by decide)).trans
        (fu.tapes 91 (by decide) (by decide))) hz91
      simpa only [hclockLength,show Nat.bits 0 = [] from rfl,FixedWidth.bits_empty] using hz
    · simpa only [hclockLength] using BankArray.word_of_eq (tk 95 (by decide)) hu95

end Maxwell.Cost.SourceCircuit.InitializeMetadata
