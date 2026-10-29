import Maxwell.Certificate.DyadicPackedRowsButterfly
import Maxwell.Certificate.DyadicPackedRowsFFTForcedSound
import Maxwell.Certificate.DyadicKernelButterflySound

namespace Maxwell.Certificate.DyadicKernel.PackedRowsButterfly
open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee
open PackedRowsFFT

theorem axisX_contains {p w : Nat} {root : Int → Rectangle} {norm : Rectangle} {sign : Int}
    {input output : Field} {M : Matrix (Fin 20) (Fin 20) ℂ} {v : Cell → ℂ}
    (h : axisX w root norm sign input = some output)
    (hline : ∀ (line : Butterfly.Values) (a : Fin 20 → ℂ),
      DyadicButterfly.Contains p (Butterfly.toValues 20 line) a →
      DyadicButterfly.Contains p
        (Butterfly.toValues 20 (Butterfly.transform20 root norm sign line)) (M *ᵥ a))
    (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output)) (FourierBinding.axisX M *ᵥ v) := by
  have hb : PackedRowsFFT.build w (fun x y z =>
      Butterfly.get (Butterfly.transform20 root norm sign
        (Array.ofFn fun j : Fin 20 => get w input j y z)) x.val) = some output := by
    simpa only [axisX,Forced.build_eq] using h
  rintro ⟨x,y,z⟩
  have hlin : DyadicButterfly.Contains p
      (Butterfly.toValues 20 (Array.ofFn fun j : Fin 20 => get w input j y z))
      (fun j => v (j,y,z)) := by
    intro j
    simpa [Butterfly.toValues,Butterfly.get,FFT.toField,get_decode] using hv (j,y,z)
  have hl := hline _ _ hlin x
  change (FFT.get (decode w output) x y z).toDyadic.Contains p _
  rw [get_decode,get_build hb,axisX_mulVec]
  exact hl

theorem axisY_contains {p w : Nat} {root : Int → Rectangle} {norm : Rectangle} {sign : Int}
    {input output : Field} {M : Matrix (Fin 10) (Fin 10) ℂ} {v : Cell → ℂ}
    (h : axisY w root norm sign input = some output)
    (hline : ∀ (line : Butterfly.Values) (a : Fin 10 → ℂ),
      DyadicButterfly.Contains p (Butterfly.toValues 10 line) a →
      DyadicButterfly.Contains p
        (Butterfly.toValues 10 (Butterfly.transform10 root norm sign line)) (M *ᵥ a))
    (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output)) (FourierBinding.axisY M *ᵥ v) := by
  have hb : PackedRowsFFT.build w (fun x y z =>
      Butterfly.get (Butterfly.transform10 root norm sign
        (Array.ofFn fun j : Fin 10 => get w input x j z)) y.val) = some output := by
    simpa only [axisY,Forced.build_eq] using h
  rintro ⟨x,y,z⟩
  have hlin : DyadicButterfly.Contains p
      (Butterfly.toValues 10 (Array.ofFn fun j : Fin 10 => get w input x j z))
      (fun j => v (x,j,z)) := by
    intro j
    simpa [Butterfly.toValues,Butterfly.get,FFT.toField,get_decode] using hv (x,j,z)
  have hl := hline _ _ hlin y
  change (FFT.get (decode w output) x y z).toDyadic.Contains p _
  rw [get_decode,get_build hb,axisY_mulVec]
  exact hl

theorem axisZ_contains {p w : Nat} {root : Int → Rectangle} {norm : Rectangle} {sign : Int}
    {input output : Field} {M : Matrix (Fin 10) (Fin 10) ℂ} {v : Cell → ℂ}
    (h : axisZ w root norm sign input = some output)
    (hline : ∀ (line : Butterfly.Values) (a : Fin 10 → ℂ),
      DyadicButterfly.Contains p (Butterfly.toValues 10 line) a →
      DyadicButterfly.Contains p
        (Butterfly.toValues 10 (Butterfly.transform10 root norm sign line)) (M *ᵥ a))
    (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output)) (FourierBinding.axisZ M *ᵥ v) := by
  have hb : PackedRowsFFT.build w (fun x y z =>
      Butterfly.get (Butterfly.transform10 root norm sign
        (Array.ofFn fun j : Fin 10 => get w input x y j)) z.val) = some output := by
    simpa only [axisZ,Forced.build_eq] using h
  rintro ⟨x,y,z⟩
  have hlin : DyadicButterfly.Contains p
      (Butterfly.toValues 10 (Array.ofFn fun j : Fin 10 => get w input x y j))
      (fun j => v (x,y,j)) := by
    intro j
    simpa [Butterfly.toValues,Butterfly.get,FFT.toField,get_decode] using hv (x,y,j)
  have hl := hline _ _ hlin z
  change (FFT.get (decode w output) x y z).toDyadic.Contains p _
  rw [get_decode,get_build hb,axisZ_mulVec]
  exact hl

theorem axisX_forward_contains {p w : Nat} {root : Int → Rectangle} {norm : Rectangle}
    {input output : Field} {v : Cell → ℂ}
    (h : axisX w root norm (-1) input = some output)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (hn : norm.toDyadic = FFTWitness.norm20)
    (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output))
      (FourierBinding.axisX (cyclicFourier 20) *ᵥ v) :=
  axisX_contains h (fun line a ha => Butterfly.transform20_forward_contains p root hr norm hn line a ha) hv

theorem axisX_inverse_contains {p w : Nat} {root : Int → Rectangle} {norm : Rectangle}
    {input output : Field} {v : Cell → ℂ}
    (h : axisX w root norm 1 input = some output)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (hn : norm.toDyadic = FFTWitness.norm20)
    (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output))
      (FourierBinding.axisX ((cyclicFourier 20).conjTranspose) *ᵥ v) :=
  axisX_contains h (fun line a ha => Butterfly.transform20_inverse_contains p root hr norm hn line a ha) hv

theorem axisY_forward_contains {p w : Nat} {root : Int → Rectangle} {norm : Rectangle}
    {input output : Field} {v : Cell → ℂ}
    (h : axisY w root norm (-1) input = some output)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (hn : norm.toDyadic = FFTWitness.norm10)
    (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output))
      (FourierBinding.axisY (cyclicFourier 10) *ᵥ v) :=
  axisY_contains h (fun line a ha => Butterfly.transform10_forward_contains p root hr norm hn line a ha) hv

theorem axisY_inverse_contains {p w : Nat} {root : Int → Rectangle} {norm : Rectangle}
    {input output : Field} {v : Cell → ℂ}
    (h : axisY w root norm 1 input = some output)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (hn : norm.toDyadic = FFTWitness.norm10)
    (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output))
      (FourierBinding.axisY ((cyclicFourier 10).conjTranspose) *ᵥ v) :=
  axisY_contains h (fun line a ha => Butterfly.transform10_inverse_contains p root hr norm hn line a ha) hv

theorem axisZ_forward_contains {p w : Nat} {root : Int → Rectangle} {norm : Rectangle}
    {input output : Field} {v : Cell → ℂ}
    (h : axisZ w root norm (-1) input = some output)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (hn : norm.toDyadic = FFTWitness.norm10)
    (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output))
      (FourierBinding.axisZ (cyclicFourier 10) *ᵥ v) :=
  axisZ_contains h (fun line a ha => Butterfly.transform10_forward_contains p root hr norm hn line a ha) hv

theorem axisZ_inverse_contains {p w : Nat} {root : Int → Rectangle} {norm : Rectangle}
    {input output : Field} {v : Cell → ℂ}
    (h : axisZ w root norm 1 input = some output)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (hn : norm.toDyadic = FFTWitness.norm10)
    (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output))
      (FourierBinding.axisZ ((cyclicFourier 10).conjTranspose) *ᵥ v) :=
  axisZ_contains h (fun line a ha => Butterfly.transform10_inverse_contains p root hr norm hn line a ha) hv

end Maxwell.Certificate.DyadicKernel.PackedRowsButterfly
