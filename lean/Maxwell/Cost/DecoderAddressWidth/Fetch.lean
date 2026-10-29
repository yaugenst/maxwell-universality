import Maxwell.Cost.DecoderFetch
import Maxwell.Cost.ArrayAccess.Width

namespace Maxwell.Cost.DecoderAddressWidth
open Structured

/-- The actual decoded width, index and clock determine every intermediate
address of the fixed fetch program. The caller's larger address is retained. -/
theorem fetch_visited (input : List Bool) (tape : ℕ→Bool)
    (width index clock : List Bool) (wbank ibank cbank : ℤ)
    (hwidth : 0 < width.length) (s t : Store) (hscratch : DecoderFetch.Scratch s.val)
    (h64 : s.val.tapes 64=BitTape.shifted width wbank)
    (h45 : s.val.tapes 45=BitTape.shifted index ibank)
    (h66 : s.val.tapes 66=BitTape.shifted clock cbank)
    (cost : ℕ) (run : Executes input tape DecoderFetch.code cost s t) :
    Visited (max s.val.address.length (width.length+index.length+1+clock.length))
      input tape DecoderFetch.code cost s t := by
  rcases hscratch with ⟨⟨ao,h0⟩,⟨wo,h1⟩,⟨zo,h2⟩,⟨yo,h3⟩,
    ⟨io,h5⟩,⟨co,h6⟩,⟨bo,h8⟩,⟨saved,h9⟩⟩
  obtain ⟨p,ep,hp,_⟩ := DecoderFetch.prepare_executes input tape width index clock wo io co
    wbank ibank cbank s h1 h5 h6 h64 h45 h66
  let W := max s.val.address.length (width.length+index.length+1+clock.length)
  have hP : Visited W input tape DecoderFetch.prepare _ s p :=
    ep.visited_noAddressPush (by decide) (le_max_left _ _)
  have hready : ArrayAccess.Ready p.val width index [] ao wo zo yo io bo saved := by
    constructor
    · simpa [hp] using h0
    · simp [hp]
    · simpa [hp] using h2
    · simpa [hp] using h3
    · simp [hp]
    · simpa [hp,BitTape.shifted,BitTape.blank] using h8
    · simpa [hp] using h9
  change Executes input tape (.seq _ (.seq _ _)) cost s t at run
  cases run with
  | seq first rest =>
    rcases ep.deterministic first with ⟨rfl,rfl⟩
    cases rest with
    | seq middle last =>
      have hR := ArrayAccess.read_visited input tape width index [] clock
        ao wo zo yo io bo saved co hwidth _ _ hready (by simp [hp]) _ middle
      have hR' : Visited W input tape ArrayAccess.readCode _ _ _ := hR.mono (by
        apply max_le hP.finish
        dsimp [W]
        exact le_max_right _ _)
      exact hP.seq (hR'.seq (last.visited_noAddressPush (by decide) hR'.finish))

end Maxwell.Cost.DecoderAddressWidth
