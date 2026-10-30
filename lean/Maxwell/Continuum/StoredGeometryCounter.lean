import Maxwell.Continuum.StoredGeometryState

/-! Charged counter installation and fixed removal of the one or two path
endpoints. Padded counter words are retained exactly, including at zero. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem Ready.counter_tapes {v : ℕ→ℕ} {s t : Store} (h : Ready v s)
    (c : ℕ) (hc : c∈({972,973}:Finset ℕ))
    (keep : ∀i,i≠c→t.val.tapes i=s.val.tapes i) : Ready v t := by
  have c_cases : c=972 ∨ c=973 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hc
  have kz (i : ℕ) (hi : i<10) := keep i (by omega)
  refine ⟨?_,⟨blank_of_eq (kz 0 (by decide)) h.scratch.1,
    blank_of_eq (kz 1 (by decide)) h.scratch.2.1,
    blank_of_eq (kz 2 (by decide)) h.scratch.2.2.1,
    blank_of_eq (kz 3 (by decide)) h.scratch.2.2.2.1,
    blank_of_eq (kz 5 (by decide)) h.scratch.2.2.2.2.1,
    blank_of_eq (kz 6 (by decide)) h.scratch.2.2.2.2.2.1,
    blank_of_eq (kz 8 (by decide)) h.scratch.2.2.2.2.2.2.1,
    blank_of_eq (kz 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩,
    blank_of_eq (kz 7 (by decide)) h.seven⟩
  intro i hi
  apply word_of_eq (keep i ?_) (h.bank i hi)
  simp only [ids,Finset.mem_erase,Finset.mem_Icc] at hi
  omega

theorem loadCounter_executes {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} {s : Store} (h : Context values base width B clock constants v s)
    (source counter : ℕ) (hs : source∈ids) (hc : counter∈({972,973}:Finset ℕ))
    (old : List Bool) (hold : BankArray.Word s.val counter old) (hOld : old.length≤B)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape (WordReplace.code source counter) cost s t ∧ cost≤21*B+21 ∧
      Context values base width B clock constants v t ∧
      BankArray.Word t.val counter (v source).bits ∧ ReadFrame {counter} s.val t.val := by
  have hcset : counter=972 ∨ counter=973 := by
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hc
  have hne : source≠counter := by
    simp only [ids,Finset.mem_erase,Finset.mem_Icc] at hs
    omega
  obtain ⟨t,ex,word,frame⟩ := WordReplace.executes source counter hne input tape (v source).bits old s
    (h.ready.bank source hs) hold
  have keep := frame.2.2.2.2.2.1
  refine ⟨_,t,ex,by have := h.wordWidth source hs;omega,
    ⟨h.ready.counter_tapes counter hc keep,h.wordWidth,?_,?_,h.fixed⟩,word,?_⟩
  · simpa only [frame.2.2.1] using h.array
  · exact BankArray.word_of_eq (keep 962 (by omega)) h.clockWord
  · exact ⟨frame.2.2.1,frame.2.1,frame.2.2.2.1,frame.2.2.2.2.1,
      fun k _ hk=>keep k (by simpa only [Finset.mem_singleton] using hk)⟩

def trimCounterCode (counter : ℕ) : ℕ→Code
  | 0 => .skip
  | k+1 => .seq (CountedShifted.test counter) (trimCounterCode counter k)

theorem trimCounter_executes {n base width B : ℕ} {values : Vector ℕ n} {clock : List Bool}
    {constants v : ℕ→ℕ} (counter k : ℕ) (hc : counter∈({972,973}:Finset ℕ))
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (s : Store)
    (h : Context values base width B clock constants v s)
    (hword : s.val.tapes counter=BitTape.shifted xs origin) (hk : k≤addressValue xs) :
    ∃t word,Executes input tape (trimCounterCode counter k) (k*(13*xs.length+14)+1) s t ∧
      Context values base width B clock constants v t ∧
      t.val.tapes counter=BitTape.shifted word origin ∧ word.length=xs.length ∧
      addressValue word=addressValue xs-k ∧ ReadFrame {counter} s.val t.val := by
  induction k generalizing xs s with
  | zero =>
    exact ⟨s,xs,by simpa only [trimCounterCode,Nat.zero_mul,Nat.zero_add] using
      (Executes.skip (input:=input) (randomTape:=tape) s),h,hword,rfl,by omega,
      ⟨rfl,rfl,rfl,rfl,fun _ _ _=>rfl⟩⟩
  | succ k ih =>
    obtain ⟨a,ex,wa,_,fa⟩ := CountedShifted.test_executes counter origin input tape s xs hword
    have hpositive : 0<addressValue xs := by omega
    have hvalue : addressValue (subtractBit true xs)=addressValue xs-1 := subtractBit_pred xs hpositive
    have hk' : k≤addressValue (subtractBit true xs) := by rw [hvalue];omega
    obtain ⟨t,word,et,ct,wt,wl,wv,ft⟩ := ih (subtractBit true xs) a (h.count_frame counter hc fa) wa hk'
    refine ⟨t,word,?_,ct,wt,(wl.trans (subtractBit_length true xs)),?_,?_⟩
    · change Executes input tape (.seq (CountedShifted.test counter) (trimCounterCode counter k)) _ s t
      convert ex.seq et using 1
      rw [subtractBit_length]
      ring
    · rw [wv,hvalue];omega
    · exact ⟨ft.memory.trans fa.2.2.1,ft.inputHead.trans fa.2.1,
        ft.randomCursor.trans fa.2.2.2.1,ft.output.trans fa.2.2.2.2.1,
        fun i hi hn=>(ft.tapes i hi hn).trans
          (fa.2.2.2.2.2.1 i (by simpa only [Finset.mem_singleton] using hn))⟩

#print axioms loadCounter_executes
#print axioms trimCounter_executes
end Maxwell.Continuum.GeometryOutput
