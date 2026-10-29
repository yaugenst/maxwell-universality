import Maxwell.Cost.DecoderParser.LoadMessages
import Maxwell.Cost.Structured.AddressWidth
import Maxwell.Cost.MemoryBit.Width

namespace Maxwell.Cost.DecoderAddressWidth
open Structured DecoderParser.LoadMessages
set_option maxRecDepth 8192

private theorem writeOne_visited (input : List Bool) (tape : ℕ→Bool)
    (address : List Bool) (b : Bool) (W : ℕ) (s t : Store)
    (hs : Address.Within W s.val) (hwidth : address.length ≤ W)
    (ha : s.val.tapes 61=BitTape.shiftedEnd address 0)
    (hb : inputBit input s.val.inputHead=b)
    (cost : ℕ) (run : Executes input tape writeOne cost s t) :
    Visited W input tape writeOne cost s t := by
  let f := Store.ofState (fetched s.val b)
  have ef : Executes input tape (.call fetch) 3 s f := by
    apply Executes.call fetch s (fetched s.val b) 2
    · apply executeInstructions_sound (instructions:=2)
      simp [executeInstructions,BitRAM.next,fetch,fetched,s.property,hb,BitRAMState.setRegister]
    · rfl
  have hf := ef.visited_noAddressPush (by decide) hs
  obtain ⟨r,hr,hrpc,_⟩ := MemoryBit.access_visited 61 (.writeMemory 28) (Or.inr rfl)
    input tape address 0 f.val f.property ha
  have hr' : VisitedPriced ((MemoryBit.program 61 (.writeMemory 28)).next input tape)
      (Address.Within W) _ f.val r := hr.mono (fun _ hh => hh.trans (max_le hf.finish hwidth))
  have eR := Visited.call _ f r _ hr' (by
    simp [MemoryBit.program,Address.load,hrpc,BitRAMInstruction.relocate])
  change Executes input tape (.seq _ (.seq _ _)) cost s t at run
  cases run with
  | seq first rest =>
    rcases ef.deterministic first with ⟨rfl,rfl⟩
    cases rest with
    | seq middle last =>
      rcases eR.execution.deterministic middle with ⟨rfl,rfl⟩
      exact hf.seq (eR.seq (last.visited_noAddressPush (by decide) eR.finish))

private theorem loader_loop_visited (input : List Bool) (tape : ℕ→Bool)
    (word address counter : List Bool) (B W : ℕ) (s : Store)
    (hs : Address.Within W s.val) (hBW : B ≤ W)
    (ha : s.val.tapes 61=BitTape.shiftedEnd address 0)
    (hwidth : address.length ≤ B) (hmax : addressValue address+word.length < 2^B)
    (hc : s.val.tapes 60=BitTape.ofList counter)
    (hvalue : 0 < word.length → addressValue counter+1=word.length)
    (hflag : s.val.registers 62=true ↔ 0 < word.length)
    (hread : SequentialWord input s.val.inputHead word) :
    ∃ cost t, Visited W input tape loop cost s t := by
  induction word generalizing address counter s with
  | nil =>
    have hf : s.val.registers 62=false := Bool.eq_false_iff.mpr (by
      intro hh
      have hz := hflag.mp hh
      simp at hz)
    exact ⟨1,s,.done hf hs⟩
  | cons b word ih =>
    have hbit : inputBit input s.val.inputHead=b := by
      have hh := hread 0 (by simp)
      change inputBit input (s.val.inputHead+0)=b at hh
      simpa only [add_zero] using hh
    obtain ⟨wc,w,_,ew,hwi,hwa,_,hwcounter,_⟩ := writeOne_steps input tape address b s ha hbit
    have eW := writeOne_visited input tape address b W s w hs (hwidth.trans hBW) ha hbit wc ew
    obtain ⟨c,ec,hct,hcz,hci,_,hca,_⟩ := countdown_steps input tape counter w (hwcounter.trans hc)
    have eC := ec.visited_noAddressPush (by decide) eW.finish
    have hcountervalue : addressValue counter=word.length := by
      have hh := hvalue (by simp)
      simp only [List.length_cons] at hh
      omega
    have hcv : 0 < word.length → addressValue (subtractBit true counter)+1=word.length := by
      intro hh
      rw [subtractBit_pred counter (by omega),hcountervalue]
      omega
    have hcf : c.val.registers 62=true ↔ 0 < word.length := by rw [hcz,hcountervalue];omega
    have hcw : (Increment.bits address).length ≤ B :=
      increment_length_bound address B hwidth (by simp only [List.length_cons] at hmax;omega)
    have hcmax : addressValue (Increment.bits address)+word.length < 2^B := by
      rw [Increment.bits_value]
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hmax
    have hcr : SequentialWord input c.val.inputHead word := by
      intro i hi
      have hh := hread (i+1) (by simpa using hi)
      simpa only [hci,hwi,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm,
        List.getElem_cons_succ] using hh
    obtain ⟨cost,t,et⟩ := ih (Increment.bits address) (subtractBit true counter) c eC.finish
      (hca.trans hwa) hcw hcmax hct hcv hcf hcr
    exact ⟨_,t,.more (hflag.mpr (by simp)) (eW.seq eC) et⟩

/-- Every message-loader prefix uses at most the binary width of the actual
loaded bit count, including every intermediate address-register push. -/
theorem load_word_visited (preceding word suffix : List Bool) (tape : ℕ→Bool)
    (s t : Store) (hhead : s.val.inputHead=preceding.length)
    (hcount : s.val.tapes 60=BitTape.ofList word.length.bits)
    (haddress : s.val.tapes 61=BitTape.blank) (cost : ℕ)
    (run : Executes (preceding++(word++suffix)) tape code cost s t) :
    Visited (max s.val.address.length word.length.bits.length)
      (preceding++(word++suffix)) tape code cost s t := by
  let input := preceding++(word++suffix)
  let W := max s.val.address.length word.length.bits.length
  obtain ⟨c,ec,hct,hcz,hci,_,hca,_⟩ := countdown_steps input tape word.length.bits s hcount
  have eC : Visited W input tape countdown _ s c :=
    ec.visited_noAddressPush (by decide) (le_max_left _ _)
  have hcv : 0 < word.length → addressValue (subtractBit true word.length.bits)+1=word.length := by
    intro hh
    rw [subtractBit_pred _ (by simpa only [addressValue_bits] using hh),addressValue_bits]
    omega
  have hcf : c.val.registers 62=true ↔ 0 < word.length := by rw [hcz,addressValue_bits];omega
  have ha : c.val.tapes 61=BitTape.shiftedEnd [] 0 := by
    simpa [BitTape.shiftedEnd,BitTape.shifted,BitTape.blank] using hca.trans haddress
  have hmax : addressValue []+word.length < 2^word.length.bits.length := by
    simpa only [addressValue,zero_add,Nat.size_eq_bits_len] using Nat.lt_size_self word.length
  obtain ⟨lc,u,eu⟩ := loader_loop_visited input tape word [] (subtractBit true word.length.bits)
    word.length.bits.length W c eC.finish (le_max_right _ _) ha (by simp) hmax hct hcv hcf (by
      rw [hci,hhead]
      exact sequentialWord_append preceding word suffix)
  exact (eC.seq eu).of_execution run

end Maxwell.Cost.DecoderAddressWidth
