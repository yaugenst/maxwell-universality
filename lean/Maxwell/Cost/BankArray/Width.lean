import Maxwell.Cost.BankArray.Read
import Maxwell.Cost.BankArray.Write
import Maxwell.Cost.ArrayAccess.Width

namespace Maxwell.Cost.BankArray
open Structured

/-- The persistent-bank wrapper inherits the checked indexed-read trace.
No array-content assumption is needed for this address-width guarantee. -/
theorem read_visited (widthBank indexBank baseBank clockBank : ℕ)
    (hw : 10 ≤ widthBank) (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank) (hc : 10 ≤ clockBank)
    (input : List Bool) (tape : ℕ→Bool) (width index base clock : List Bool)
    (hwidth : 0 < width.length) (s t : Store) (hscratch : Scratch s.val)
    (hwidthBank : Word s.val widthBank width) (hindexBank : Word s.val indexBank index)
    (hbaseBank : Word s.val baseBank base) (hclockBank : Word s.val clockBank clock)
    (cost : ℕ) (run : Executes input tape (readCode widthBank indexBank baseBank clockBank) cost s t) :
    Visited (ArrayAccess.addressWidth s.val width index base clock) input tape
      (readCode widthBank indexBank baseBank clockBank) cost s t := by
  obtain ⟨wbank,hwbank⟩ := hwidthBank
  obtain ⟨ibank,hibank⟩ := hindexBank
  obtain ⟨bbank,hbbank⟩ := hbaseBank
  obtain ⟨cbank,hcbank⟩ := hclockBank
  rcases hscratch with ⟨⟨ao,h0⟩,⟨wo,h1⟩,⟨zo,h2⟩,⟨yo,h3⟩,
    ⟨io,h5⟩,⟨co,h6⟩,⟨bo,h8⟩,⟨saved,h9⟩⟩
  obtain ⟨p,ep,hp,_⟩ := prepare_executes widthBank indexBank baseBank clockBank hw hi hb hc
    input tape width index base clock wo io bo co wbank ibank bbank cbank s h1 h5 h8 h6
    hwbank hibank hbbank hcbank
  let W := ArrayAccess.addressWidth s.val width index base clock
  have hP : Visited W input tape (prepare widthBank indexBank baseBank clockBank) _ s p :=
    ep.visited_noAddressPush rfl (le_max_left _ _)
  have hready : ArrayAccess.Ready p.val width index base ao wo zo yo io bo saved := by
    constructor
    · simpa [hp] using h0
    · simp [hp]
    · simpa [hp] using h2
    · simpa [hp] using h3
    · simp [hp]
    · simp [hp]
    · simpa [hp] using h9
  change Executes input tape (.seq _ (.seq _ _)) cost s t at run
  cases run with
  | seq first rest =>
    rcases ep.deterministic first with ⟨rfl,rfl⟩
    cases rest with
    | seq middle last =>
      have hR := ArrayAccess.read_visited input tape width index base clock
        ao wo zo yo io bo saved co hwidth _ _ hready (by simp [hp]) _ middle
      have hR' : Visited W input tape ArrayAccess.readCode _ _ _ := hR.mono
        (max_le hP.finish (le_max_right _ _))
      exact hP.seq (hR'.seq (last.visited_noAddressPush (by decide) hR'.finish))

/-- The corresponding write bound uses the actual payload length and
includes every instruction in preparation, memory updates, and cleanup. -/
theorem write_visited (widthBank indexBank baseBank payloadBank : ℕ)
    (hw : 10 ≤ widthBank) (hi : 10 ≤ indexBank) (hb : 10 ≤ baseBank) (hc : 10 ≤ payloadBank)
    (input : List Bool) (tape : ℕ→Bool) (width index base payload : List Bool)
    (hwidth : 0 < width.length) (s t : Store) (hscratch : Scratch s.val)
    (hwidthBank : Word s.val widthBank width) (hindexBank : Word s.val indexBank index)
    (hbaseBank : Word s.val baseBank base) (hpayloadBank : Word s.val payloadBank payload)
    (cost : ℕ) (run : Executes input tape (writeCode widthBank indexBank baseBank payloadBank) cost s t) :
    Visited (ArrayAccess.addressWidth s.val width index base payload) input tape
      (writeCode widthBank indexBank baseBank payloadBank) cost s t := by
  obtain ⟨wbank,hwbank⟩ := hwidthBank
  obtain ⟨ibank,hibank⟩ := hindexBank
  obtain ⟨bbank,hbbank⟩ := hbaseBank
  obtain ⟨cbank,hcbank⟩ := hpayloadBank
  rcases hscratch with ⟨⟨ao,h0⟩,⟨wo,h1⟩,⟨zo,h2⟩,⟨yo,h3⟩,
    ⟨io,h5⟩,⟨co,h6⟩,⟨bo,h8⟩,⟨saved,h9⟩⟩
  obtain ⟨p,ep,hp,_⟩ := prepare_executes widthBank indexBank baseBank payloadBank hw hi hb hc
    input tape width index base payload wo io bo co wbank ibank bbank cbank s h1 h5 h8 h6
    hwbank hibank hbbank hcbank
  let W := ArrayAccess.addressWidth s.val width index base payload
  have hP : Visited W input tape (prepare widthBank indexBank baseBank payloadBank) _ s p :=
    ep.visited_noAddressPush rfl (le_max_left _ _)
  have hready : ArrayAccess.Ready p.val width index base ao wo zo yo io bo saved := by
    constructor
    · simpa [hp] using h0
    · simp [hp]
    · simpa [hp] using h2
    · simpa [hp] using h3
    · simp [hp]
    · simp [hp]
    · simpa [hp] using h9
  change Executes input tape (.seq _ (.seq _ _)) cost s t at run
  cases run with
  | seq first rest =>
    rcases ep.deterministic first with ⟨rfl,rfl⟩
    cases rest with
    | seq middle last =>
      have hR := ArrayAccess.write_visited input tape width index base payload
        ao wo zo yo io bo saved co hwidth _ _ hready (by simp [hp]) _ middle
      have hR' : Visited W input tape ArrayAccess.writeCode _ _ _ := hR.mono
        (max_le hP.finish (le_max_right _ _))
      exact hP.seq (hR'.seq (last.visited_noAddressPush (by decide) hR'.finish))

end Maxwell.Cost.BankArray
