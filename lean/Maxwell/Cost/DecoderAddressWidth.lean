import Maxwell.Cost.DecoderAddressWidth.Setup
import Maxwell.Cost.DecoderAddressWidth.Rows
import Maxwell.Cost.DecoderComplexity
import Maxwell.Cost.RealSimulation.WidthSimulation

namespace Maxwell.Cost.DecoderAddressWidth
open Structured DecoderParser
set_option maxRecDepth 8192

/-- The complete decoder's explicit address register stays linear in its
already established execution-width parameter. -/
def width {n : ℕ} (I : Target.Instance n) : ℕ := 2*Decoder.executionWidth I+1

theorem fetchWidth_le {n : ℕ} (I : Target.Instance n) : fetchWidth I.decoder ≤ width I := by
  have hb : I.decoder.format.width.bits.length ≤ I.decoder.format.width := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact Nat.lt_two_pow_self
  dsimp [fetchWidth,width,Decoder.executionWidth]
  omega

theorem loaderWidth_le {n : ℕ} (I : Target.Instance n) :
    (I.decoder.sampleCount*I.decoder.format.width).bits.length ≤ width I := by
  dsimp [width,Decoder.executionWidth]
  omega

/-- Enrich the actual complete decoder execution with a bound at every
charged instruction boundary. The input and message are the original
canonical codecs, and the endpoint and operation count are unchanged. -/
theorem decoder_visited {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages)
    (tape : ℕ→Bool) (cost : ℕ) (t : Store)
    (run : Executes (Codec.target I++Codec.messages I.decoder w) tape Decoder.code cost
      (Store.ofState BitRAMState.initial) t) :
    Visited (width I) (Codec.target I++Codec.messages I.decoder w) tape Decoder.code cost
      (Store.ofState BitRAMState.initial) t := by
  obtain ⟨sc,s,es,_,hs⟩ := setup_steps I w tape
  have eS := (setup_visited I w tape sc s es).mono (loaderWidth_le I)
  have hi : (beforeRows I++Codec.nat n)++((rows I.decoder).flatMap rowWire++Codec.messages I.decoder w)=
      Codec.target I++Codec.messages I.decoder w := by
    rw [target_rows]
    simp [List.append_assoc]
  change Executes _ tape (.seq _ _) cost _ t at run
  cases run with
  | seq first rest =>
    rcases es.deterministic first with ⟨rfl,rfl⟩
    rw [←hi] at rest
    have eR := rows_visited I.decoder w (rows I.decoder) n.bits (beforeRows I++Codec.nat n)
      (Codec.messages I.decoder w) tape (fun _ => 0) 0 (width I) (fetchWidth_le I)
      (by simp [Algebra.CoreShort]) rfl rfl rfl rfl s _ eS.finish hs.inputHead hs.ready hs.bank
      hs.messages hs.supportCounter hs.counter (by simp) _ rest
    rw [hi] at eR
    exact eS.seq eR

/-- Every reachable decoder prefix, including prefixes requested under a
larger fuel cap, has a bounded explicit binary address. -/
theorem decoder_prefix {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages)
    (tape : ℕ→Bool) (spent : ℕ) (state : BitRAMState)
    (run : PricedSteps (Decoder.program.next (Codec.target I++Codec.messages I.decoder w) tape)
      spent BitRAMState.initial state) : state.address.length ≤ 2*Decoder.executionWidth I+1 := by
  obtain ⟨cost,t,_,he,_⟩ := Decoder.executes I w tape
  exact (decoder_visited I w tape cost t he).prefix_bound spent state run

/-- The exact public premise of the finite bit-to-real interpreter. This is
proved from the real decoder and its actual messages, without an additional
hypothesis about addresses or message accuracy. -/
theorem simulator_prefix {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages)
    (tape : ℕ→Bool) (fuel : ℕ) :
    RealSimulation.PrefixAddressBound Decoder.program
      (Codec.target I++Codec.messages I.decoder w) tape BitRAMState.initial fuel (width I) := by
  intro spent state _ run
  exact decoder_prefix I w tape spent state run

end Maxwell.Cost.DecoderAddressWidth
