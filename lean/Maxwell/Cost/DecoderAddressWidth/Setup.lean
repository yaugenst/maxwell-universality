import Maxwell.Cost.DecoderAddressWidth.LoadMessages
import Maxwell.Cost.DecoderParser.Setup

/-! The decoder setup's only address-building phase is the actual message
loader. Its count is computed from parsed metadata, and all remaining setup
instructions preserve the resulting address-width bound. -/
namespace Maxwell.Cost.DecoderAddressWidth
open Structured DecoderParser
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

private theorem metadata_load_visited {ι : Type*} {n : ℕ}
    (D : Target.WeightedDecoder ι n) (w : D.Messages) (preceding suffix : List Bool)
    (tape : ℕ → Bool) (s t : Store) (W cost : ℕ)
    (hwithin : Address.Within W s.val)
    (hwidth : (Codec.messages D w).length.bits.length ≤ W)
    (hhead : s.val.inputHead = preceding.length)
    (hblank : ∀ j ∈ MetadataProduct.work, s.val.tapes j = BitTape.blank)
    (haddress : s.val.tapes 61 = BitTape.blank)
    (hi : s.val.tapes 41 = BitTape.ofList D.format.integerBits.bits)
    (hf : s.val.tapes 42 = BitTape.ofList D.format.fractionalBits.bits)
    (hs : s.val.tapes 43 = BitTape.ofList D.sampleCount.bits)
    (run : Executes (preceding ++ (Codec.messages D w ++ suffix)) tape
      MetadataProduct.loadCode cost s t) :
    Visited W (preceding ++ (Codec.messages D w ++ suffix)) tape MetadataProduct.loadCode cost s t := by
  obtain ⟨pc,p,ao,wo,zo,yo,so,hpc,ep,hp60,hp0,hp1,hp2,hp3,hp64,fp⟩ :=
    MetadataProduct.steps (preceding ++ (Codec.messages D w ++ suffix)) tape
      D.format.integerBits D.format.fractionalBits D.sampleCount s hblank hi hf hs
  have hphead : p.val.inputHead = preceding.length := fp.inputHead.trans hhead
  have hpaddress : p.val.tapes 61 = BitTape.blank := (fp.tapes 61 (by decide)).trans haddress
  have hpcount : p.val.tapes 60 = BitTape.ofList (Codec.messages D w).length.bits := by
    simpa only [Codec.messages_length,Target.FixedPointFormat.width] using hp60
  change Executes _ _ (.seq MetadataProduct.code LoadMessages.code) cost s t at run
  cases run with
  | seq first second =>
    rcases ep.deterministic first with ⟨rfl,rfl⟩
    have vp := ep.visited_noAddressPush (by decide) hwithin
    have vl := load_word_visited preceding (Codec.messages D w) suffix tape p t
      hphead hpcount hpaddress _ second
    exact vp.seq (vl.mono (max_le vp.finish hwidth))

/-- Every actual instruction boundary of decoder setup is bounded by the
binary width of the number of message bits computed from input metadata. -/
theorem setup_visited {n : ℕ} (I : Target.Instance n) (w : I.decoder.Messages)
    (tape : ℕ → Bool) (cost : ℕ) (t : Store)
    (run : Executes (Codec.target I ++ Codec.messages I.decoder w) tape setupCode cost
      (Store.ofState BitRAMState.initial) t) :
    Visited (I.decoder.sampleCount*I.decoder.format.width).bits.length
      (Codec.target I ++ Codec.messages I.decoder w) tape setupCode cost
      (Store.ofState BitRAMState.initial) t := by
  obtain ⟨rc,r,er,hrc,hrhead,hrarchive,hrmeta,hrready,hrframe⟩ :=
    retainedTarget_steps I (Codec.messages I.decoder w) tape
  have hb (j : ℕ) (hj : j ∈ MetadataProduct.work) : r.val.tapes j = BitTape.blank := by
    apply hrframe.tapes j
    simp only [MetadataProduct.work,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
    omega
  have h61 : r.val.tapes 61 = BitTape.blank := hrframe.tapes 61 (by decide)
  change Executes _ _ (.seq prepareCode (.seq DecoderConstants.code
    (.seq Output.headerCode (readNatural 72)))) cost _ t at run
  cases run with
  | seq preparation remaining =>
    change Executes _ _ (.seq retainedTargetCode (.seq Replay.loadCode secondPassPrefix)) _ _ _ at preparation
    cases preparation with
    | seq retained afterRetained =>
      rcases er.deterministic retained with ⟨rfl,rfl⟩
      have vr := er.visited_noAddressPush (by decide)
        (show Address.Within (I.decoder.sampleCount*I.decoder.format.width).bits.length
          (Store.ofState BitRAMState.initial).val from Nat.zero_le _)
      cases afterRetained with
      | seq load secondPass =>
        change Executes _ _ (.seq MetadataProduct.loadCode Replay.code) _ _ _ at load
        cases load with
        | seq metadataLoad replay =>
          have vm := metadata_load_visited I.decoder w (Codec.target I) [] tape r _ _ _
            vr.finish (by simp only [Codec.messages_length]; exact le_rfl) hrhead hb h61
            hrmeta.integerBits hrmeta.fractionalBits hrmeta.sampleCount
            (by simpa only [List.append_nil] using metadataLoad)
          simp only [List.append_nil] at vm
          have vp := replay.visited_noAddressPush (by decide) vm.finish
          have vs := secondPass.visited_noAddressPush (by decide) vp.finish
          have vt := remaining.visited_noAddressPush (by decide) vs.finish
          exact (vr.seq ((vm.seq vp).seq vs)).seq vt

end Maxwell.Cost.DecoderAddressWidth
