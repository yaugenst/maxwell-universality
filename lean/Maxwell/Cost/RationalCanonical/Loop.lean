import Maxwell.Cost.RationalCanonical.Step

namespace Maxwell.Cost.RationalCanonical
open Structured RationalAccumulator

/-- The Euclidean loop reads the presence bit of the canonical divisor word. -/
def testCode : Code := .atom (.readTape 221 80 81)
def tested (s : Store) : Store := Store.ofState (readTapeState s.val 221 80 81)
def loopCode : Code := .loop 81 (.seq stepCode testCode)
def gcdCode : Code := .seq testCode loopCode

structure GCDFrame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ ({0,1,2,3,4,220,221,222,223} : Finset ℕ) → t.tapes i = s.tapes i
  registers : ∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 →
    i ≠ 80 → i ≠ 81 → t.registers i = s.registers i

theorem GCDFrame.refl (s : BitRAMState) : GCDFrame s s :=
  ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl,fun _ _ _ _ _ _ _ _ => rfl⟩
theorem GCDFrame.trans {s t u : BitRAMState} (h : GCDFrame s t) (k : GCDFrame t u) :
    GCDFrame s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi),
    fun i hi h24 h25 h26 h27 h80 h81 => (k.registers i hi h24 h25 h26 h27 h80 h81).trans
      (h.registers i hi h24 h25 h26 h27 h80 h81)⟩
theorem GCDFrame.ofDivision {s t : BitRAMState}
    (h : DivisionFrame {0,1,2,3,4,220,221,222,223} s t) : GCDFrame s t :=
  ⟨h.address,h.memory,h.inputHead,h.randomCursor,h.output,h.tapes,
    fun i hi h24 h25 h26 h27 _ _ => h.registers i hi h24 h25 h26 h27⟩

theorem test (input : List Bool) (tape : ℕ → Bool) (s : Store) (a b : ℕ)
    (hs : Ready s.val a b) :
    Executes input tape testCode 3 s (tested s) ∧ Ready (tested s).val a b ∧
      (tested s).val.registers 81 = decide (b ≠ 0) ∧ GCDFrame s.val (tested s).val := by
  have he : Executes input tape testCode 3 s (tested s) := by
    apply Executes.atom (extra := 1)
    · simp [BitRAM.next,s.property,readTapeState]
    · simp [readTapeState,s.property]
  refine ⟨he,⟨hs.first,hs.second,hs.quotient,hs.remainder,hs.scratch⟩,?_,⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl,?_⟩⟩
  · obtain ⟨origin,ho⟩ := hs.second
    have hh : b.bits.head?.isSome = decide (b ≠ 0) := by
      by_cases hb : b = 0
      · simp [hb]
      · cases he : b.bits with
        | nil =>
          have hv := address_bits b
          simp [he,addressValue] at hv
          exact False.elim (hb hv.symm)
        | cons bit tail => simp [hb]
    simpa [tested,Store.ofState,readTapeState,ho] using hh
  · intro i _ _ _ _ _ h80 h81
    simp [tested,Store.ofState,readTapeState,h80,h81]

theorem loop (input : List Bool) (tape : ℕ → Bool) (B k a b : ℕ)
    (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B)
    (hz : (euclid k a b).2 = 0) (s : Store) (hs : Ready s.val a b)
    (htest : s.val.registers 81 = decide (b ≠ 0)) :
    ∃ cost t, cost ≤ 1+k*(2000*(2*B+2)^2+4) ∧
      Executes input tape loopCode cost s t ∧
      Ready t.val (euclid k a b).1 0 ∧ GCDFrame s.val t.val := by
  induction k generalizing a b s with
  | zero =>
    have hb0 : b = 0 := hz
    subst b
    refine ⟨1,s,by omega,.done ?_,hs,GCDFrame.refl _⟩
    simpa using htest
  | succ k ih =>
    by_cases hb0 : b = 0
    · subst b
      refine ⟨1,s,by omega,.done ?_,?_,GCDFrame.refl _⟩
      · simpa using htest
      · simpa using hs
    · have hbpos := Nat.pos_of_ne_zero hb0
      have heuc : euclid (k+1) a b = euclid k b (a%b) := by simp [euclid,hb0]
      rw [heuc] at hz ⊢
      obtain ⟨c,u,hc,eu,hu,fu⟩ := step input tape a b hbpos s hs
      obtain ⟨ev,hv,hvt,fv⟩ := test input tape u b (a%b) hu
      have hm : (a%b).bits.length ≤ B := by
        rw [Nat.size_eq_bits_len]
        exact (Nat.size_le_size (Nat.mod_lt a hbpos).le).trans (by simpa [Nat.size_eq_bits_len] using hb)
      obtain ⟨d,t,hd,et,ht,ft⟩ := ih b (a%b) hb hm hz (tested u) hv hvt
      refine ⟨1+(c+3)+d,t,?_,.more (by simpa [hb0] using htest) (eu.seq ev) et,
        ht,(GCDFrame.ofDivision fu).trans (fv.trans ft)⟩
      have hsum : a.bits.length+b.bits.length+2 ≤ 2*B+2 := by omega
      have hsquare := Nat.pow_le_pow_left hsum 2
      nlinarith

theorem gcd (input : List Bool) (tape : ℕ → Bool) (a b : ℕ) (s : Store)
    (hs : Ready s.val a b) :
    ∃ cost t, cost ≤ 4+2*b.size*(2000*(2*(a.size+b.size)+2)^2+4) ∧
      Executes input tape gcdCode cost s t ∧ Ready t.val (Nat.gcd a b) 0 ∧
      GCDFrame s.val t.val := by
  obtain ⟨et,ht,hb,ft⟩ := test input tape s a b hs
  have he := euclid_size a b
  obtain ⟨c,t,hc,ec,ht',fc⟩ := loop input tape (a.size+b.size) (2*b.size) a b
    (by simp only [Nat.size_eq_bits_len]; omega)
    (by simp only [Nat.size_eq_bits_len]; omega)
    (by rw [he]) (tested s) ht hb
  refine ⟨3+c,t,by omega,et.seq ec,?_,ft.trans fc⟩
  simpa only [he] using ht'

end Maxwell.Cost.RationalCanonical
