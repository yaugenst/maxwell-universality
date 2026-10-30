import Maxwell.Continuum.CalibrationNeumannSemantics

/-! Every executed Neumann array write fits a width derived from input channel bounds. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.CalibrationMatrix Maxwell.Cost.CalibrationMatrix.Horner
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem Snapshot.fits_of_bits {n : ℕ} {a : Snapshot n} {A : ChannelMatrix n} {D : ℕ}
    {state : Channels n×Channels n} (h : a.Decodes A D state)
    (hp : Horner.FitsWidth (addressValue a.data.width) (matvec A state.2))
    (hw : Horner.FitsWidth (addressValue a.data.width) (channelStep A D state).1)
    (hx : Horner.FitsWidth (addressValue a.data.width) (channelStep A D state).2) : Fits a.data a.words := by
  have dec : (a.data.productData a.words 10 11).Decodes A state.2 := by
    simpa only [h.value] using h.matrix.product a.words 10 11
  have hf : (a.data.productBuffers a.words 10 11 5 4).Fits := Buffers.fits_of_decodes dec hp.1 hp.2
  have hcu : Horner.channels (productWords a.data a.words) 4 5=(matvec A state.2).negate := by
    rw [channels_swap _ 5 4,Horner.product_channels h.matrix _ _ _ _ _ (by decide) hf,h.value]
  have hcw : Horner.channels (productWords a.data a.words) 0 1=state.1 :=
    (product_source a.data a.words).trans h.source
  have hcz : Horner.channels (productWords a.data a.words) 2 3=zeroChannels n :=
    (product_zero a.data a.words).trans h.zero
  have wp i := congrArg (fun c : Channels n => c.positive i) hcw
  have wn i := congrArg (fun c : Channels n => c.negative i) hcw
  have xp i := congrArg (fun c : Channels n => c.positive i) hcz
  have xn i := congrArg (fun c : Channels n => c.negative i) hcz
  have up i := congrArg (fun c : Channels n => c.positive i) hcu
  have un i := congrArg (fun c : Channels n => c.negative i) hcu
  simp only [Horner.channels] at wp wn
  simp only [Horner.channels,zeroChannels] at xp xn
  simp only [Horner.channels,Channels.negate] at up un
  refine ⟨hf,?_,?_,?_,?_⟩
  · intro i
    change (addressValue (((productWords a.data a.words) 0).get i)*a.data.K).bits.length≤_
    rw [h.denominator,wp i]
    simpa only [channelStep,Channels.scale,Nat.mul_comm] using hw.1 i
  · intro i
    change (addressValue (((productWords a.data a.words) 1).get i)*a.data.K).bits.length≤_
    rw [h.denominator,wn i]
    simpa only [channelStep,Channels.scale,Nat.mul_comm] using hw.2 i
  · intro i
    change (addressValue (((productWords a.data a.words) 0).get i)*a.data.K+
      addressValue (((productWords a.data a.words) 2).get i)*a.data.K+
      addressValue (((productWords a.data a.words) 5).get i)*a.data.S).bits.length≤_
    rw [h.denominator,h.numerator,wp i,xp i,un i]
    simpa [channelStep,Channels.scale,Channels.add,Nat.mul_comm]
      using hx.1 i
  · intro i
    change (addressValue (((productWords a.data a.words) 1).get i)*a.data.K+
      addressValue (((productWords a.data a.words) 3).get i)*a.data.K+
      addressValue (((productWords a.data a.words) 4).get i)*a.data.S).bits.length≤_
    rw [h.denominator,h.numerator,wn i,xn i,up i]
    simpa [channelStep,Channels.scale,Channels.add,Nat.mul_comm]
      using hx.2 i

theorem Snapshot.iterate_fits {n : ℕ} {a : Snapshot n} {A : ChannelMatrix n} {D aBound bBound : ℕ}
    {b : Channels n} (h : a.Decodes A D (b,b)) (hA : A.Bounded aBound) (hb : b.Bounded bBound)
    (N : ℕ) (hW : uniformWidth n aBound bBound D N≤addressValue a.data.width) :
    ∀ k<N, Fits (a.iterate k).data (a.iterate k).words := by
  have widths (k : ℕ) (hk : k≤N+1) := channels_uniform_width hA D b hb N _ hW k hk
  have decodes : ∀ k≤N, (a.iterate k).Decodes A D (channels A D b k) := by
    intro k
    induction k with
    | zero => intro _; exact h
    | succ k ih =>
      intro hk
      have hk' : k<N := by omega
      have hc := ih (by omega)
      apply Snapshot.advance_decodes hc
      apply Snapshot.fits_of_bits hc
      · simpa only [Snapshot.iterate_width] using (widths k (by omega)).2.2
      · simpa only [Snapshot.iterate_width,channels] using (widths (k+1) (by omega)).1
      · simpa only [Snapshot.iterate_width,channels] using (widths (k+1) (by omega)).2.1
  intro k hk
  apply Snapshot.fits_of_bits (decodes k hk.le)
  · simpa only [Snapshot.iterate_width] using (widths k (by omega)).2.2
  · simpa only [Snapshot.iterate_width,channels] using (widths (k+1) (by omega)).1
  · simpa only [Snapshot.iterate_width,channels] using (widths (k+1) (by omega)).2.1

#print axioms Snapshot.iterate_fits

end Maxwell.Continuum.Calibration.NeumannMachine
