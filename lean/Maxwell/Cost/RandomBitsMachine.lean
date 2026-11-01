import Maxwell.Cost.Structured.CountedShifted
import Maxwell.Cost.TapeOps
import Maxwell.Cost.ParseNat

/-! A fixed runtime loop reads exactly the requested number of independent
random input bits and stores their little-endian word. -/

namespace Maxwell.Cost.RandomBitsMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def bits (randomTape : ℕ → Bool) (start n : ℕ) : List Bool :=
  (List.range n).map (fun i => randomTape (start+i))

theorem bits_succ (randomTape : ℕ → Bool) (start n : ℕ) :
    bits randomTape start (n+1)=bits randomTape start n++[randomTape (start+n)] := by
  simp [bits,List.range_succ]

theorem random_executes (input : List Bool) (randomTape : ℕ → Bool) (s : Store) :
    Executes input randomTape (Code.atom (.randomBit 30)) 2 s
      (Store.ofState {s.val.setRegister 30 (randomTape s.val.randomCursor) with
        randomCursor := s.val.randomCursor+1}) := by
  apply Executes.atom (extra := 0)
  · simp [BitRAM.next,s.property]
  · simp [BitRAMState.setRegister,s.property]

def body : Code := .seq (Code.atom (.randomBit 30))
  (.seq (Code.atom (.writeTape 241 30)) (Code.atom (.tapeRight 241)))

structure Frame (s t : BitRAMState) (countTape : ℕ := 240) (outputTape : ℕ := 241) : Prop where
  address : t.address=s.address
  inputHead : t.inputHead=s.inputHead
  memory : t.memory=s.memory
  output : t.output=s.output
  tapes : ∀i,i≠countTape → i≠outputTape → t.tapes i=s.tapes i

theorem body_executes (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (priorBits : List Bool) (origin : ℤ)
    (hp : s.val.tapes 241=BitTape.shiftedEnd priorBits origin) :
    ∃t, Executes input randomTape body 6 s t ∧
      t.val.tapes 241=BitTape.shiftedEnd (priorBits++[randomTape s.val.randomCursor]) origin ∧
      t.val.randomCursor=s.val.randomCursor+1 ∧ t.val.tapes 240=s.val.tapes 240 ∧ Frame s.val t.val := by
  let s1 := Store.ofState {s.val.setRegister 30 (randomTape s.val.randomCursor) with
    randomCursor := s.val.randomCursor+1}
  let s2 := Store.ofState (s1.val.setTape 241 ((s1.val.tapes 241).write (some (s1.val.registers 30))))
  let t := Store.ofState (s2.val.setTape 241
    {s2.val.tapes 241 with head := (s2.val.tapes 241).head+1})
  have h1 : Executes input randomTape (Code.atom (.randomBit 30)) 2 s s1 :=
    random_executes input randomTape s
  have h2 : Executes input randomTape (Code.atom (.writeTape 241 30)) 2 s1 s2 :=
    Executes.writeTape input randomTape s1 241 30
  have h3 : Executes input randomTape (Code.atom (.tapeRight 241)) 2 s2 t :=
    Executes.tapeRight input randomTape s2 241
  refine ⟨t,h1.seq (h2.seq h3),?_,rfl,?_,?_⟩
  · simpa [t,s2,s1,Store.ofState,BitRAMState.setTape,BitRAMState.setRegister,hp,BitTape.write] using
      BitTape.shiftedEnd_append_write priorBits origin (randomTape s.val.randomCursor)
  · simp [t,s2,s1,Store.ofState,BitRAMState.setTape,BitRAMState.setRegister]
  · refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro i _ hi
    simp [t,s2,s1,Store.ofState,BitRAMState.setTape,BitRAMState.setRegister,hi]

def code : Code := Counted.code 240 body

def cap (n : ℕ) : ℕ := (n+1)*(13*n.bits.length+15)+6*n

theorem executes (input : List Bool) (randomTape : ℕ → Bool) (n : ℕ)
    (countOrigin wordOrigin : ℤ) (s : Store)
    (hcount : s.val.tapes 240=BitTape.shifted n.bits countOrigin)
    (hblank : s.val.tapes 241={BitTape.blank with head := wordOrigin}) :
    ∃cost t, Executes input randomTape code cost s t ∧ cost≤cap n ∧
      t.val.tapes 241=BitTape.shiftedEnd (bits randomTape s.val.randomCursor n) wordOrigin ∧
      t.val.randomCursor=s.val.randomCursor+n ∧ Frame s.val t.val ∧
      ∃finalWord,t.val.tapes 240=BitTape.shifted finalWord countOrigin ∧
        finalWord.length=n.bits.length := by
  let invariant := fun remaining (t : Store) => remaining≤n ∧
    t.val.randomCursor=s.val.randomCursor+(n-remaining) ∧
    t.val.tapes 241=BitTape.shiftedEnd (bits randomTape s.val.randomCursor (n-remaining)) wordOrigin ∧
    Frame s.val t.val
  have stable : ∀r a b, Counted.Frame 240 a b → invariant r a → invariant r b := by
    intro r a b hf hi
    exact ⟨hi.1,hf.2.2.2.1.trans hi.2.1,
      (hf.2.2.2.2.2.1 241 (by decide)).trans hi.2.2.1,
      ⟨hf.1.trans hi.2.2.2.address,hf.2.1.trans hi.2.2.2.inputHead,
        hf.2.2.1.trans hi.2.2.2.memory,hf.2.2.2.2.1.trans hi.2.2.2.output,
        fun i h240 h241 => (hf.2.2.2.2.2.1 i h240).trans (hi.2.2.2.tapes i h240 h241)⟩⟩
  have step : ∀r xs a, invariant (r+1) a → a.val.tapes 240=BitTape.shifted xs countOrigin →
      addressValue xs=r → ∃cost b, Executes input randomTape body cost a b ∧
        invariant r b ∧ b.val.tapes 240=BitTape.shifted xs countOrigin ∧ cost≤6 := by
    intro r xs a hi hxs _
    obtain ⟨b,he,hb,hcursor,hcount',hf⟩ := body_executes input randomTape a
      (bits randomTape s.val.randomCursor (n-(r+1))) wordOrigin hi.2.2.1
    refine ⟨6,b,he,⟨by omega,?_,?_,?_⟩,hcount'.trans hxs,le_rfl⟩
    · rw [hcursor,hi.2.1]
      omega
    · rw [hb,hi.2.1,show n-r=(n-(r+1))+1 by omega,bits_succ]
    · exact ⟨hf.address.trans hi.2.2.2.address,hf.inputHead.trans hi.2.2.2.inputHead,
        hf.memory.trans hi.2.2.2.memory,hf.output.trans hi.2.2.2.output,
        fun i h240 h241 => (hf.tapes i h240 h241).trans (hi.2.2.2.tapes i h240 h241)⟩
  have hi : invariant n s := by
    refine ⟨le_rfl,by omega,?_,⟨rfl,rfl,rfl,rfl,fun _ _ _ => rfl⟩⟩
    simpa [bits] using hblank
  obtain ⟨cost,t,finalWord,he,ht,hfinal,hlength,_,hc⟩ := CountedShifted.executes 240 countOrigin body input randomTape invariant
    (fun _ => 6) stable step n n.bits s (addressValue_bits n) hcount hi
  refine ⟨cost,t,he,?_,?_,?_,ht.2.2.2,finalWord,hfinal,hlength⟩
  · simpa [cap,Nat.mul_comm] using hc
  · simpa using ht.2.2.1
  · simpa using ht.2.1

#print axioms body_executes
#print axioms executes

end Maxwell.Cost.RandomBitsMachine
