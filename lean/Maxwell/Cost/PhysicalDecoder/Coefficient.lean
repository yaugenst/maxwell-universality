import Maxwell.Cost.PhysicalDecoder.Arithmetic

/-! Exact canonical emission of a decoder coefficient from its runtime
mode, selected amplitude, and original normalization words. -/
namespace Maxwell.Cost.PhysicalDecoder.Coefficient
open Structured RationalAccumulator

def work : Finset ℕ := Arithmetic.work ∪ {220,221,222,223,230,231}

structure Frame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  tapes : ∀ i ∉ work,t.tapes i=s.tapes i

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,fun i hi => (k.tapes i hi).trans (h.tapes i hi)⟩

private theorem Frame.ofArithmetic {s t : BitRAMState} (h : Arithmetic.Frame s t) : Frame s t :=
  ⟨h.address,h.memory,h.inputHead,h.randomCursor,
    fun i hi => h.tapes i (fun hh => hi (Finset.mem_union_left _ hh))⟩

private theorem Frame.ofCanonical {s t : BitRAMState} (h : RationalCanonical.EmitFrame s t) : Frame s t := by
  refine ⟨h.address,h.memory,h.inputHead,h.randomCursor,?_⟩
  intro i hi
  exact h.tapes i (fun hh => hi ((by decide :
    ({0,1,2,3,4,220,221,222,223,228,229,230,231}:Finset ℕ) ⊆ work) hh))

private theorem Frame.ofClear {s t : BitRAMState} {target : ℕ}
    (ht : target ∈ work) (h : WordTransfer.Frame target target s t) : Frame s t := by
  refine ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,?_⟩
  intro i hi
  have hn : i ≠ target := by intro he; subst i; exact hi ht
  exact h.2.2.2.2.2.1 i hn hn

structure Ready (x : Arithmetic.Data) (s : Store) : Prop where
  words : ∀ i,Word s.val (350+i.val) (x i)
  blank : ∀ i ∈ work,Blank s.val i

def code : Code := .seq Arithmetic.code (.seq RationalCanonical.code
  (.seq (.call (TapeOps.clear 228)) (.call (TapeOps.clear 229))))
def costBound (B : ℕ) : ℕ := 100000000*(B+2)^3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem executes (x : Arithmetic.Data) (negative : Bool) (B : ℕ)
    (hv : Arithmetic.Valid x) (hB : Arithmetic.Bounded x B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready x s)
    (hsign : s.val.registers 23=negative) :
    ∃ cost t, cost ≤ costBound B ∧ Executes input tape code cost s t ∧
      t.val.output=(Codec.rat (Arithmetic.fraction x negative)).reverse++s.val.output ∧
      Ready x t ∧ Frame s.val t.val := by
  obtain ⟨c,a,hc,ea,an,ad,az,asign,af⟩ := Arithmetic.executes x B hB input tape s
    ⟨hs.words,fun i hi => hs.blank i (Finset.mem_union_left _ hi)⟩
  have extra (i : ℕ) (hi : i ∈ ({220,221,222,223,230,231}:Finset ℕ)) : Blank a.val i := by
    apply blank_of_eq (af.tapes i (by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide))
    exact hs.blank i (Finset.mem_union_right _ hi)
  have ar : RationalCanonical.NormalizeReady a.val (Arithmetic.numerator x) (Arithmetic.denominator x) :=
    ⟨an,ad,⟨(zero_word_iff_blank _ _).mpr (extra 220 (by decide)),
      (zero_word_iff_blank _ _).mpr (extra 221 (by decide)),extra 222 (by decide),extra 223 (by decide),
      fun i hi => az i (by interval_cases i <;> decide)⟩,extra 230 (by decide),extra 231 (by decide)⟩
  obtain ⟨d,b,hd,eb,bo,br,bf⟩ := RationalCanonical.executes input tape negative
    (Arithmetic.numerator x) (Arithmetic.denominator x) (Arithmetic.denominator_pos x hv) a ar
    (asign.trans hsign)
  obtain ⟨u,eu,uz,uf⟩ := RationalCanonical.clear_word 228 (Arithmetic.numerator x) input tape b br.numerator
  obtain ⟨t,et,tz,tf⟩ := RationalCanonical.clear_word 229 (Arithmetic.denominator x) input tape u
    (word_of_eq (uf.2.2.2.2.2.1 229 (by decide) (by decide)) br.denominator)
  have all : Frame s.val t.val := (Frame.ofArithmetic af).trans
    ((Frame.ofCanonical bf).trans ((Frame.ofClear (by decide) uf).trans (Frame.ofClear (by decide) tf)))
  have hnum := Arithmetic.numerator_bits x B hB
  have hden := Arithmetic.denominator_bits x B hB
  refine ⟨c+(d+((6*(Arithmetic.numerator x).bits.length+4)+(6*(Arithmetic.denominator x).bits.length+4))),
    t,?_,ea.seq (eb.seq (eu.seq et)),?_,⟨?_,?_⟩,all⟩
  · have hd' := hd.trans (RationalCanonical.costBound_polynomial _ _)
    have hb' : (Arithmetic.numerator x).size+(Arithmetic.denominator x).size+2 ≤ 8*B+2 := by
      simpa only [Nat.size_eq_bits_len] using (show (Arithmetic.numerator x).bits.length+
        (Arithmetic.denominator x).bits.length+2 ≤ 8*B+2 by omega)
    have hd'' : d ≤ 100000*(8*B+2)^3 := hd'.trans (by gcongr)
    unfold costBound
    nlinarith [Nat.zero_le (B^3)]
  · rw [tf.2.2.2.2.1,uf.2.2.2.2.1,bo,af.output,Arithmetic.fraction_value]
  · intro i
    exact word_of_eq (all.tapes (350+i.val) (by
      have := i.isLt
      simp only [work,Arithmetic.work,PhysicalMaterial.ArithmeticBank.work,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,not_or]
      omega)) (hs.words i)
  · intro i hi
    by_cases hi228 : i=228
    · subst i
      exact blank_of_eq (tf.2.2.2.2.2.1 228 (by decide) (by decide)) ((zero_word_iff_blank _ _).mp uz)
    by_cases hi229 : i=229
    · subst i
      exact (zero_word_iff_blank _ _).mp tz
    apply blank_of_eq ((tf.2.2.2.2.2.1 i hi229 hi229).trans (uf.2.2.2.2.2.1 i hi228 hi228))
    have hbkeep (hnot : i ∉ ({0,1,2,3,4,220,221,222,223,228,229,230,231}:Finset ℕ)) : Blank b.val i :=
      blank_of_eq (bf.tapes i hnot) (az i (by
        simp only [work,Arithmetic.work,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hnot
        simp only [Finset.mem_union,Finset.mem_singleton]
        tauto))
    by_cases hsmall : i<5
    · exact br.work.scratch i hsmall
    by_cases h220 : i=220
    · subst i; exact (zero_word_iff_blank _ _).mp br.work.first
    by_cases h221 : i=221
    · subst i; exact (zero_word_iff_blank _ _).mp br.work.second
    by_cases h222 : i=222
    · subst i; exact br.work.quotient
    by_cases h223 : i=223
    · subst i; exact br.work.remainder
    by_cases h230 : i=230
    · subst i; exact br.outputNumerator
    by_cases h231 : i=231
    · subst i; exact br.outputDenominator
    exact hbkeep (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega)

end Maxwell.Cost.PhysicalDecoder.Coefficient
