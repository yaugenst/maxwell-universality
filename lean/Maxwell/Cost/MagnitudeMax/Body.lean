import Maxwell.Cost.MagnitudeMax.Parsed
import Maxwell.Cost.MagnitudeMax.Logger
import Maxwell.Cost.MagnitudeMax.Semantics

namespace Maxwell.Cost.MagnitudeMax

open Structured RationalAccumulator

def bankOf (p : Pair) (i : ℕ) : ℕ := if i = 30 then p.1 else if i = 31 then p.2 else 0

theorem after_bankOf (p : Pair) (q : ℚ) : after (bankOf p) q = bankOf (select p q) := by
  have hq : (q.num.natAbs : ℚ) / q.den = |q| := ofRational_value q
  have hv : ((loaded (bankOf p) q) 30 : ℚ) / (loaded (bankOf p) q) 31 = value p := by
    simp [loaded, bankOf, value]
  have hw : ((loaded (bankOf p) q) 32 : ℚ) / (loaded (bankOf p) q) 33 = |q| := by
    simpa only [loaded, Function.update_self, Function.update_of_ne (show (32 : ℕ) ≠ 33 by decide)] using hq
  unfold after updated selected
  rw [hv, hw]
  unfold select
  split_ifs <;> funext i <;>
    by_cases h30 : i = 30 <;> by_cases h31 : i = 31 <;>
    by_cases h32 : i = 32 <;> by_cases h33 : i = 33 <;>
    simp_all [replaced, loaded, bankOf, ofRational, Function.update_apply]

theorem select_pos (p : Pair) (q : ℚ) (h : 0 < p.2) : 0 < (select p q).2 := by
  unfold select
  split_ifs <;> first | exact h | exact q.pos

theorem select_width (p : Pair) (q : ℚ) (B : ℕ)
    (hp : p.1.bits.length ≤ B ∧ p.2.bits.length ≤ B)
    (hq : q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B) :
    (select p q).1.bits.length ≤ B ∧ (select p q).2.bits.length ≤ B := by
  unfold select
  split_ifs <;> first | exact hp | exact hq

namespace Body

def code : Code := .seq (.call ParseRat.program) (.seq parsedCode (.call Logger.program))

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.memory = s.memory ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, 4 ≤ i → i ≠ 10 → i ≠ 12 → i ≠ 13 → i ≠ 20 → (i < 30 ∨ 36 < i) →
    t.tapes i = s.tapes i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha, hm, hr, ho, ht⟩
  rcases k with ⟨ka, km, kr, ko, kt⟩
  exact ⟨ka.trans ha, km.trans hm, kr.trans hr, ko.trans ho,
    fun i h4 h10 h12 h13 h20 hb =>
      (kt i h4 h10 h12 h13 h20 hb).trans (ht i h4 h10 h12 h13 h20 hb)⟩

theorem parse_frame {s t : BitRAMState} (h : ParseRat.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun i _ h10 h12 h13 _ _ => h.2.2.2.2.1 i h10 h12 h13⟩

theorem update_frame {s t : BitRAMState} (h : MagnitudeMax.Frame s t) : Frame s t :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun i h4 _ _ _ _ hb => h.2.2.2.2.2.1 i h4 hb⟩

theorem log_frame {s t : BitRAMState} (h : LogRat.Frame s t) : Frame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun i _ h10 h12 h13 h20 _ => h.2.2.2.2 i h10 h12 h13 h20⟩

/-- One real parser/update/logger iteration. Every rational is retained in
canonical signed form even though the maximum comparison ignores its sign. -/
theorem executes (q : ℚ) (current : Pair) (B : ℕ) (preceding suffix archive : List Bool)
    (tape : ℕ → Bool) (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hpositive : 0 < current.2)
    (hcurrent : current.1.bits.length ≤ B ∧ current.2.bits.length ≤ B)
    (hq : q.num.natAbs.bits.length ≤ B ∧ q.den.bits.length ≤ B)
    (hbank : Bank s.val (bankOf current)) (hready : Scratch s.val 0)
    (hparser : LogRat.Ready s.val) (harchive : s.val.tapes 20 = BitTape.atEnd archive) :
    ∃ cost, ∃ t : Store, cost ≤ 11000 * (B + 2)^2 ∧
      Executes (preceding ++ (Codec.rat q ++ suffix)) tape code cost s t ∧
      t.val.inputHead = s.val.inputHead + (Codec.rat q).length ∧
      Bank t.val (bankOf (select current q)) ∧ Scratch t.val 0 ∧ LogRat.Ready t.val ∧
      t.val.tapes 20 = BitTape.atEnd (archive ++ Codec.rat q) ∧ Frame s.val t.val := by
  let input := preceding ++ (Codec.rat q ++ suffix)
  obtain ⟨p, hp, hppc, hphead, hpcount, hpnum, hpden, hpsign, hpf⟩ :=
    ParseRat.parse_rat_steps q preceding suffix tape s.val s.property hhead hparser.1 hparser.2.1 hparser.2.2
  let pS := Store.ofState p
  have hp' : Executes input tape (.call ParseRat.program) (17 * LogRat.width q + 21) s pS :=
    Executes.call _ _ _ _ hp (by
      simpa [hppc] using (show ParseRat.program.code[42]? = some .halt by decide))
  have hpb : Bank pS.val (bankOf current) := by
    intro i hi hi'
    exact word_of_eq (hpf.2.2.2.2.1 i (by omega) (by omega) (by omega)) (hbank i hi hi')
  have hpr : Scratch pS.val 0 :=
    ⟨blank_of_eq (hpf.2.2.2.2.1 0 (by decide) (by decide) (by decide)) hready.1,
      word_of_eq (hpf.2.2.2.2.1 1 (by decide) (by decide) (by decide)) hready.2.1,
      blank_of_eq (hpf.2.2.2.2.1 2 (by decide) (by decide) (by decide)) hready.2.2.1,
      blank_of_eq (hpf.2.2.2.2.1 3 (by decide) (by decide) (by decide)) hready.2.2.2⟩
  obtain ⟨c, u, hc, hu, hub, hur, husign, huf⟩ := parsed input tape (bankOf current) q B
    (by intro i hi; rcases hi with rfl | rfl <;> simp [bankOf, hcurrent]) hq.1 hq.2
    (by simpa [bankOf] using hpositive) (by simp [bankOf]) (by simp [bankOf])
    (by simp [bankOf]) (by simp [bankOf]) pS hpb hpr hpnum hpden
  have huth (i : ℕ) (hi : 4 ≤ i) (hj : i < 30 ∨ 36 < i) : u.val.tapes i = p.tapes i :=
    huf.2.2.2.2.2.1 i hi hj
  obtain ⟨t, ht, hthead, htlog, htparser, htf⟩ := Logger.steps input tape q archive u
    ((huth 10 (by decide) (Or.inl (by decide))).trans hpcount)
    ((huth 12 (by decide) (Or.inl (by decide))).trans hpnum)
    ((huth 13 (by decide) (Or.inl (by decide))).trans hpden)
    (husign.trans hpsign)
    ((huth 20 (by decide) (Or.inl (by decide))).trans
      ((hpf.2.2.2.2.1 20 (by decide) (by decide) (by decide)).trans harchive))
  refine ⟨(17 * LogRat.width q + 21) + (c + (28 * LogRat.width q + 68)), t,
    by dsimp [LogRat.width]; nlinarith [hq.1, hq.2], hp'.seq (hu.seq ht),
    hthead.trans (huf.2.1.trans hphead), ?_, ?_, htparser, htlog,
    ((parse_frame hpf).trans (update_frame huf)).trans (log_frame htf)⟩
  · rw [after_bankOf] at hub
    intro i hi hi'
    exact word_of_eq (htf.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)) (hub i hi hi')
  · exact ⟨blank_of_eq (htf.2.2.2.2 0 (by decide) (by decide) (by decide) (by decide)) hur.1,
      word_of_eq (htf.2.2.2.2 1 (by decide) (by decide) (by decide) (by decide)) hur.2.1,
      blank_of_eq (htf.2.2.2.2 2 (by decide) (by decide) (by decide) (by decide)) hur.2.2.1,
      blank_of_eq (htf.2.2.2.2 3 (by decide) (by decide) (by decide) (by decide)) hur.2.2.2⟩

end Body
end Maxwell.Cost.MagnitudeMax
