import Maxwell.Continuum.CalibrationNeumannStep
import Maxwell.Continuum.CalibrationNeumannChannels

/-! Exact shared-denominator semantics of the executed Neumann array step. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.CalibrationMatrix Maxwell.Cost.CalibrationMatrix.Horner
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def zeroChannels (n : ℕ) : Channels n := ⟨fun _=>0,fun _=>0⟩

theorem channels_swap {n : ℕ} (words : Fin 12→Vector (List Bool) n) (p q : Fin 12) :
    Horner.channels words q p=(Horner.channels words p q).negate := rfl

structure Snapshot.Decodes {n : ℕ} (a : Snapshot n) (A : ChannelMatrix n) (D : ℕ)
    (state : Channels n×Channels n) : Prop where
  matrix : a.data.DecodesMatrix A
  denominator : a.data.K=D
  numerator : a.data.S=1
  source : Horner.channels a.words 0 1=state.1
  value : Horner.channels a.words 10 11=state.2
  zero : Horner.channels a.words 2 3=zeroChannels n

theorem product_channels {n : ℕ} {a : Snapshot n} {A : ChannelMatrix n} {D : ℕ}
    {state : Channels n×Channels n} (h : a.Decodes A D state) (hf : Fits a.data a.words) :
    Horner.channels (productWords a.data a.words) 4 5=(matvec A state.2).negate := by
  rw [channels_swap _ 5 4,Horner.product_channels h.matrix _ _ _ _ _ (by decide) hf.product,h.value]

theorem product_source {n : ℕ} (d : Horner.Data n) (words : Fin 12→Vector (List Bool) n) :
    Horner.channels (productWords d words) 0 1=Horner.channels words 0 1 := by
  simp [Horner.channels,productWords,Horner.productWords,setOutputs]

theorem product_zero {n : ℕ} (d : Horner.Data n) (words : Fin 12→Vector (List Bool) n) :
    Horner.channels (productWords d words) 2 3=Horner.channels words 2 3 := by
  simp [Horner.channels,productWords,Horner.productWords,setOutputs]

theorem affine_output_step {n : ℕ} (A : ChannelMatrix n) (D : ℕ) (state : Channels n×Channels n) :
    Affine.output D 1 state.1 (zeroChannels n) (matvec A state.2).negate=channelStep A D state := by
  apply Prod.ext
  · rfl
  · apply congrArg₂ Channels.mk <;> funext i <;>
      simp [Channels.scale,Channels.add,Channels.negate,zeroChannels]

theorem round_channels {n : ℕ} {a : Snapshot n} {A : ChannelMatrix n} {D : ℕ}
    {state : Channels n×Channels n} (h : a.Decodes A D state) (hf : Fits a.data a.words) :
    (Horner.channels (roundWords a.data a.words) 6 7,Horner.channels (roundWords a.data a.words) 8 9)=
      channelStep A D state := by
  have hout := Affine.filled_channels a.data.affineData (affineWords (productWords a.data a.words))
    hf.wPositive hf.wNegative hf.xPositive hf.xNegative
  change (Horner.channels (roundWords a.data a.words) 6 7,Horner.channels (roundWords a.data a.words) 8 9)=
    Affine.output a.data.K a.data.S (Horner.channels (productWords a.data a.words) 0 1)
      (Horner.channels (productWords a.data a.words) 2 3)
      (Horner.channels (productWords a.data a.words) 4 5) at hout
  rw [h.denominator,h.numerator,product_source,product_zero,h.source,h.zero,product_channels h hf] at hout
  exact hout.trans (affine_output_step A D state)

theorem Snapshot.advance_channels {n : ℕ} (a : Snapshot n) :
    (Horner.channels a.advance.words 0 1,Horner.channels a.advance.words 10 11)=
      (Horner.channels (roundWords a.data a.words) 6 7,Horner.channels (roundWords a.data a.words) 8 9) := by
  simp [Snapshot.advance,recycleWords,Horner.channels,Equiv.swap_apply_def]

theorem Snapshot.advance_zero {n : ℕ} (a : Snapshot n) :
    Horner.channels a.advance.words 2 3=Horner.channels a.words 2 3 := by
  simp [Snapshot.advance,recycleWords,Horner.channels,Equiv.swap_apply_def,roundWords,
    affineFinalWords,Affine.filledWords,affineWords,affinePort,productWords,Horner.productWords,setOutputs]

theorem Snapshot.advance_decodes {n : ℕ} {a : Snapshot n} {A : ChannelMatrix n} {D : ℕ}
    {state : Channels n×Channels n} (h : a.Decodes A D state) (hf : Fits a.data a.words) :
    a.advance.Decodes A D (channelStep A D state) := by
  have hc := a.advance_channels.trans (round_channels h hf)
  exact ⟨⟨h.matrix.positive,h.matrix.negative⟩,h.denominator,h.numerator,
    congrArg Prod.fst hc,congrArg Prod.snd hc,a.advance_zero.trans h.zero⟩

theorem Snapshot.iterate_decodes {n : ℕ} {a : Snapshot n} {A : ChannelMatrix n} {D : ℕ}
    {b : Channels n} (h : a.Decodes A D (b,b)) (N : ℕ)
    (hf : ∀ k<N, Fits (a.iterate k).data (a.iterate k).words) :
    (a.iterate N).Decodes A D (channels A D b N) := by
  induction N with
  | zero => exact h
  | succ N ih => exact Snapshot.advance_decodes (ih (fun k hk => hf k (by omega))) (hf N (by omega))

#print axioms Snapshot.iterate_decodes

end Maxwell.Continuum.Calibration.NeumannMachine
