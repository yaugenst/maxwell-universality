import Maxwell.Cost.CalibrationMatrix.Horner.Semantics

namespace Maxwell.Cost.CalibrationMatrix.Horner

/-- Actual channel word widths, before any cancellation. -/
def FitsWidth {n : ℕ} (width : ℕ) (x : Channels n) : Prop :=
  (∀ i, (x.positive i).bits.length ≤ width) ∧ (∀ i, (x.negative i).bits.length ≤ width)

/-- Pure bounds for the two products and the next state imply every
physical array write in a Horner step fits its reserved binary slot. -/
theorem Snapshot.fits_of_bits {n : ℕ} {a : Snapshot n} {A : ChannelMatrix n}
    {D S : ℕ} {state : Channels n × Channels n} (hd : a.Decodes A D S state)
    (h1 : FitsWidth (addressValue a.data.width) (matvec A state.2))
    (h2 : FitsWidth (addressValue a.data.width) (matvec A (matvec A state.2)))
    (hw : FitsWidth (addressValue a.data.width) (hornerStep A D S state).1)
    (hx : FitsWidth (addressValue a.data.width) (hornerStep A D S state).2) : Fits a.data a.words := by
  have dec1 : (a.data.productData a.words 2 3).Decodes A state.2 := by
    simpa only [hd.value] using hd.matrix.product a.words 2 3
  have hf1 : (a.data.productBuffers a.words 2 3 10 11).Fits :=
    Buffers.fits_of_decodes dec1 h1.1 h1.2
  have hc1 : channels (firstWords a.data a.words) 10 11 = matvec A state.2 := by
    rw [firstWords,product_channels hd.matrix _ _ _ _ _ (by decide) hf1,hd.value]
  have dec2 : (a.data.productData (firstWords a.data a.words) 10 11).Decodes A (matvec A state.2) := by
    simpa only [hc1] using hd.matrix.product (firstWords a.data a.words) 10 11
  have hf2 : (a.data.productBuffers (firstWords a.data a.words) 10 11 4 5).Fits :=
    Buffers.fits_of_decodes dec2 h2.1 h2.2
  have hc2 : channels (secondWords a.data a.words) 4 5 = matvec A (matvec A state.2) := by
    rw [secondWords,product_channels hd.matrix _ _ _ _ _ (by decide) hf2,hc1]
  have hcw : channels (secondWords a.data a.words) 0 1 = state.1 := by
    simpa [channels,secondWords,firstWords,productWords,setOutputs] using hd.source
  have hcx : channels (secondWords a.data a.words) 2 3 = state.2 := by
    simpa [channels,secondWords,firstWords,productWords,setOutputs] using hd.value
  have wp i := congrArg (fun c : Channels n => c.positive i) hcw
  have wn i := congrArg (fun c : Channels n => c.negative i) hcw
  have xp i := congrArg (fun c : Channels n => c.positive i) hcx
  have xn i := congrArg (fun c : Channels n => c.negative i) hcx
  have up i := congrArg (fun c : Channels n => c.positive i) hc2
  have un i := congrArg (fun c : Channels n => c.negative i) hc2
  simp only [channels] at wp wn xp xn up un
  refine ⟨hf1,hf2,?_,?_,?_,?_⟩
  · intro i
    change (addressValue (((secondWords a.data a.words) 0).get i)*a.data.K).bits.length ≤ _
    rw [hd.denominator,wp i]
    simpa [hornerStep,Channels.scale,Nat.mul_comm] using hw.1 i
  · intro i
    change (addressValue (((secondWords a.data a.words) 1).get i)*a.data.K).bits.length ≤ _
    rw [hd.denominator,wn i]
    simpa [hornerStep,Channels.scale,Nat.mul_comm] using hw.2 i
  · intro i
    change (addressValue (((secondWords a.data a.words) 0).get i)*a.data.K+
      addressValue (((secondWords a.data a.words) 2).get i)*a.data.K+
      addressValue (((secondWords a.data a.words) 5).get i)*a.data.S).bits.length ≤ _
    rw [hd.denominator,hd.numerator,wp i,xp i,un i]
    simpa [hornerStep,Channels.scale,Channels.add,Channels.negate,Nat.mul_comm] using hx.1 i
  · intro i
    change (addressValue (((secondWords a.data a.words) 1).get i)*a.data.K+
      addressValue (((secondWords a.data a.words) 3).get i)*a.data.K+
      addressValue (((secondWords a.data a.words) 4).get i)*a.data.S).bits.length ≤ _
    rw [hd.denominator,hd.numerator,wn i,xn i,up i]
    simpa [hornerStep,Channels.scale,Channels.add,Channels.negate,Nat.mul_comm] using hx.2 i

/-- A numerical bound on the exact recurrence suffices for the whole
compiled loop; no assumption about a host-computed row operation is needed. -/
theorem Snapshot.iterate_fits_of_bits {n : ℕ} {a : Snapshot n} {A : ChannelMatrix n}
    {D S : ℕ} {source : Channels n} (hd : a.Decodes A D S (source,source)) (N : ℕ)
    (h1 : ∀ k, k < N → FitsWidth (addressValue a.data.width) (matvec A (horner A D S source k).2))
    (h2 : ∀ k, k < N → FitsWidth (addressValue a.data.width) (matvec A (matvec A (horner A D S source k).2)))
    (hw : ∀ k, k < N → FitsWidth (addressValue a.data.width) (horner A D S source (k+1)).1)
    (hx : ∀ k, k < N → FitsWidth (addressValue a.data.width) (horner A D S source (k+1)).2) :
    ∀ k, k < N → Fits (a.iterate k).data (a.iterate k).words := by
  have decodes : ∀ k, k ≤ N → (a.iterate k).Decodes A D S (horner A D S source k) := by
    intro k
    induction k with
    | zero => intro _;exact hd
    | succ k ih =>
      intro hk
      have hk' : k < N := by omega
      exact Snapshot.advance_decodes (ih (by omega)) (Snapshot.fits_of_bits (ih (by omega))
        (by simpa using h1 k hk') (by simpa using h2 k hk')
        (by simpa only [Snapshot.iterate_width,horner] using hw k hk')
        (by simpa only [Snapshot.iterate_width,horner] using hx k hk'))
  intro k hk
  exact Snapshot.fits_of_bits (decodes k (by omega))
    (by simpa using h1 k hk) (by simpa using h2 k hk)
    (by simpa only [Snapshot.iterate_width,horner] using hw k hk)
    (by simpa only [Snapshot.iterate_width,horner] using hx k hk)

end Maxwell.Cost.CalibrationMatrix.Horner
