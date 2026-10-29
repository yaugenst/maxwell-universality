import Maxwell.Cost.CalibrationMatrix.Horner.Step

namespace Maxwell.Cost.CalibrationMatrix.Horner

variable {n : ℕ}

/-- The signed-channel pair read from two actual arrays of words. -/
def channels (words : Fin 12 → Vector (List Bool) n) (positive negative : Fin 12) : Channels n :=
  ⟨fun i => addressValue ((words positive).get i),
    fun i => addressValue ((words negative).get i)⟩

structure Data.DecodesMatrix (d : Data n) (A : ChannelMatrix n) : Prop where
  positive : ∀ i j, addressValue (d.matrixPositive.get (matrixSlot i j)) = A.positive i j
  negative : ∀ i j, addressValue (d.matrixNegative.get (matrixSlot i j)) = A.negative i j

theorem Data.DecodesMatrix.product {d : Data n} {A : ChannelMatrix n}
    (h : d.DecodesMatrix A) (words : Fin 12 → Vector (List Bool) n) (ip iq : Fin 12) :
    (d.productData words ip iq).Decodes A (channels words ip iq) :=
  ⟨h.positive, h.negative, fun _ => rfl, fun _ => rfl⟩

theorem product_channels {d : Data n} {A : ChannelMatrix n}
    (h : d.DecodesMatrix A) (words : Fin 12 → Vector (List Bool) n)
    (ip iq op oq : Fin 12) (hpq : op ≠ oq)
    (hfit : (d.productBuffers words ip iq op oq).Fits) :
    channels (productWords d words ip iq op oq) op oq = matvec A (channels words ip iq) := by
  have hout := (d.productBuffers words ip iq op oq).advance_decodes (h.product words ip iq) hfit
  apply congrArg₂ Channels.mk <;> funext i
  · simpa [channels, productWords, setOutputs, hpq, Buffers.advance,
      Data.productBuffers, matvec] using hout.vectorPositive i
  · simpa [channels, productWords, setOutputs, Buffers.advance,
      Data.productBuffers, matvec] using hout.vectorNegative i

private theorem second_w (d : Data n) (words : Fin 12 → Vector (List Bool) n) :
    channels (secondWords d words) 0 1 = channels words 0 1 := by
  simp [channels, secondWords, firstWords, productWords, setOutputs]

private theorem second_x (d : Data n) (words : Fin 12 → Vector (List Bool) n) :
    channels (secondWords d words) 2 3 = channels words 2 3 := by
  simp [channels, secondWords, firstWords, productWords, setOutputs]

theorem second_product_channels {d : Data n} {A : ChannelMatrix n}
    (h : d.DecodesMatrix A) (words : Fin 12 → Vector (List Bool) n) (hfit : Fits d words) :
    channels (secondWords d words) 4 5 = matvec A (matvec A (channels words 2 3)) := by
  rw [secondWords, product_channels h _ _ _ _ _ (by decide) hfit.second,
    firstWords, product_channels h _ _ _ _ _ (by decide) hfit.first]

theorem round_channels {d : Data n} {A : ChannelMatrix n}
    (h : d.DecodesMatrix A) (words : Fin 12 → Vector (List Bool) n) (hfit : Fits d words) :
    (channels (roundWords d words) 6 7, channels (roundWords d words) 8 9) =
      Affine.output d.K d.S (channels words 0 1) (channels words 2 3)
        (matvec A (matvec A (channels words 2 3))) := by
  have hout := Affine.filled_channels d.affineData (affineWords (secondWords d words))
    hfit.wPositive hfit.wNegative hfit.xPositive hfit.xNegative
  change (channels (roundWords d words) 6 7, channels (roundWords d words) 8 9) =
    Affine.output d.K d.S (channels (secondWords d words) 0 1)
      (channels (secondWords d words) 2 3) (channels (secondWords d words) 4 5) at hout
  rw [second_w, second_x, second_product_channels h words hfit] at hout
  exact hout

/-- Matrix entries, the exact denominator cube, the step numerator, and both
live channel pairs are tied to the same stored snapshot. -/
structure Snapshot.Decodes (a : Snapshot n) (A : ChannelMatrix n) (D S : ℕ)
    (state : Channels n × Channels n) : Prop where
  matrix : a.data.DecodesMatrix A
  denominator : a.data.K = D^3
  numerator : a.data.S = S
  source : channels a.words 0 1 = state.1
  value : channels a.words 2 3 = state.2

theorem Snapshot.advance_channels (a : Snapshot n) :
    (channels a.advance.words 0 1, channels a.advance.words 2 3) =
      (channels (roundWords a.data a.words) 6 7, channels (roundWords a.data a.words) 8 9) := by
  simp [Snapshot.advance, recycleWords, channels, Equiv.swap_apply_def]

/-- The two actual products, affine writes, and four buffer swaps realize
one exact Horner recurrence whenever their finite-width writes fit. -/
theorem Snapshot.advance_decodes {a : Snapshot n} {A : ChannelMatrix n} {D S : ℕ}
    {state : Channels n × Channels n} (h : a.Decodes A D S state) (hfit : Fits a.data a.words) :
    a.advance.Decodes A D S (hornerStep A D S state) := by
  have hc := a.advance_channels.trans (round_channels h.matrix a.words hfit)
  rw [h.denominator, h.numerator, h.source, h.value] at hc
  have hstep : Affine.output (D^3) S state.1 state.2
      (matvec A (matvec A state.2)) = hornerStep A D S state := rfl
  rw [hstep] at hc
  exact ⟨⟨h.matrix.positive, h.matrix.negative⟩, h.denominator, h.numerator,
    congrArg Prod.fst hc, congrArg Prod.snd hc⟩

/-- Every snapshot produced by the concrete buffer iteration decodes the
same channel recurrence used by the polynomial and bit-size arguments. -/
theorem Snapshot.iterate_decodes {a : Snapshot n} {A : ChannelMatrix n} {D S : ℕ}
    {source : Channels n} (h : a.Decodes A D S (source, source)) (N : ℕ)
    (hfit : ∀ k, k < N → Fits (a.iterate k).data (a.iterate k).words) :
    (a.iterate N).Decodes A D S (horner A D S source N) := by
  induction N with
  | zero => exact h
  | succ N ih =>
    exact Snapshot.advance_decodes (ih (fun k hk => hfit k (by omega))) (hfit N (by omega))

theorem Snapshot.iterate_channels {a : Snapshot n} {A : ChannelMatrix n} {D S : ℕ}
    {source : Channels n} (h : a.Decodes A D S (source, source)) (N : ℕ)
    (hfit : ∀ k, k < N → Fits (a.iterate k).data (a.iterate k).words) :
    (channels (a.iterate N).words 0 1, channels (a.iterate N).words 2 3) =
      horner A D S source N := by
  have hd := Snapshot.iterate_decodes h N hfit
  exact Prod.ext hd.source hd.value

end Maxwell.Cost.CalibrationMatrix.Horner
