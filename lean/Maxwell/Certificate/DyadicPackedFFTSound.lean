import Maxwell.Certificate.DyadicPackedFFT
import Maxwell.Certificate.PackedFFTCodecSound
import Maxwell.Certificate.DyadicKernelFFTSound

namespace Maxwell.Certificate.DyadicKernel.PackedFFT

def index (x : Fin 20) (y z : Fin 10) : Fin 2000 :=
  ⟨100*x.val+10*y.val+z.val, by have := x.isLt; have := y.isLt; have := z.isLt; omega⟩

@[simp] theorem coordinateX_index (x : Fin 20) (y z : Fin 10) :
    coordinateX (index x y z) = x := by
  apply Fin.ext
  simp only [coordinateX, index, Fin.ofNat, Fin.val_mk]
  have := x.isLt
  have := y.isLt
  have := z.isLt
  omega

@[simp] theorem coordinateY_index (x : Fin 20) (y z : Fin 10) :
    coordinateY (index x y z) = y := by
  apply Fin.ext
  simp only [coordinateY, index, Fin.ofNat, Fin.val_mk]
  have := x.isLt
  have := y.isLt
  have := z.isLt
  omega

@[simp] theorem coordinateZ_index (x : Fin 20) (y z : Fin 10) :
    coordinateZ (index x y z) = z := by
  apply Fin.ext
  simp only [coordinateZ, index, Fin.ofNat, Fin.val_mk]
  have := x.isLt
  have := y.isLt
  have := z.isLt
  omega

attribute [local irreducible] packChecked

theorem get_build {w n : Nat} {f : Fin 20 → Fin 10 → Fin 10 → Rectangle}
    (h : build w f = some n) (x : Fin 20) (y z : Fin 10) :
    get w n x y z = f x y z := by
  have hh := packChecked_get (a := List.ofFn fun i : Fin 2000 =>
    f (coordinateX i) (coordinateY i) (coordinateZ i)) h (index x y z).val
      (by rw [List.length_ofFn]; exact (index x y z).isLt)
  simp only [List.getElem_ofFn] at hh
  change Packed.getPacked w n (index x y z).val =
    f (coordinateX (index x y z)) (coordinateY (index x y z))
      (coordinateZ (index x y z)) at hh
  rw [coordinateX_index, coordinateY_index, coordinateZ_index] at hh
  exact hh

@[simp] theorem get_decode (w n : Nat) (x : Fin 20) (y z : Fin 10) :
    FFT.get (decode w n) x y z = get w n x y z := FFT.get_build _ x y z

theorem decode_build {w n : Nat} {f : Fin 20 → Fin 10 → Fin 10 → Rectangle}
    (h : build w f = some n) : decode w n = FFT.build f := by
  have he : get w n = f := funext fun x => funext fun y => funext fun z => get_build h x y z
  exact congrArg FFT.build he

theorem axisX_eq {w q input output : Nat} {K : FFT.Kernel 20}
    (h : axisX w q K input = some output) :
    decode w output = FFT.axisX q K (decode w input) := by
  rw [decode_build h]
  simp only [FFT.axisX, get_decode]

theorem axisY_eq {w q input output : Nat} {K : FFT.Kernel 10}
    (h : axisY w q K input = some output) :
    decode w output = FFT.axisY q K (decode w input) := by
  rw [decode_build h]
  simp only [FFT.axisY, get_decode]

theorem axisZ_eq {w q input output : Nat} {K : FFT.Kernel 10}
    (h : axisZ w q K input = some output) :
    decode w output = FFT.axisZ q K (decode w input) := by
  rw [decode_build h]
  simp only [FFT.axisZ, get_decode]

theorem diagonal_eq {w q input output : Nat} {t : FFT.Field}
    (h : diagonal w q t input = some output) :
    decode w output = FFT.diagonal q t (decode w input) := by
  rw [decode_build h]
  simp only [FFT.diagonal, get_decode]

attribute [local irreducible] decode FFT.axisX FFT.axisY FFT.axisZ FFT.diagonal

theorem forward_eq {w q input output : Nat} {K20 : FFT.Kernel 20} {K10 : FFT.Kernel 10}
    {twiddle : FFT.Field} (h : forward w q K20 K10 twiddle input = some output) :
    decode w output = FFT.forward q K20 K10 twiddle (decode w input) := by
  obtain ⟨first,hfirst,second,hsecond,third,hthird,hresult⟩ :=
    (by simpa only [forward, bind, Option.bind_eq_some_iff] using h :
      ∃ first, axisX w q K20 input = some first ∧
      ∃ second, diagonal w q twiddle first = some second ∧
      ∃ third, axisY w q K10 second = some third ∧ axisZ w q K10 third = some output)
  rw [axisZ_eq hresult, axisY_eq hthird, diagonal_eq hsecond, axisX_eq hfirst]
  rfl

theorem inverse_eq {w q input output : Nat} {K20 : FFT.Kernel 20} {K10 : FFT.Kernel 10}
    {twiddle : FFT.Field} (h : inverse w q K20 K10 twiddle input = some output) :
    decode w output = FFT.inverse q K20 K10 twiddle (decode w input) := by
  obtain ⟨first,hfirst,second,hsecond,third,hthird,hresult⟩ :=
    (by simpa only [inverse, bind, Option.bind_eq_some_iff] using h :
      ∃ first, axisZ w q (FFT.adjoint K10) input = some first ∧
      ∃ second, axisY w q (FFT.adjoint K10) first = some second ∧
      ∃ third, diagonal w q (FFT.conjugateField twiddle) second = some third ∧
        axisX w q (FFT.adjoint K20) third = some output)
  rw [axisX_eq hresult, diagonal_eq hthird, axisY_eq hsecond, axisZ_eq hfirst]
  rfl

open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee

theorem forward_contains {p w q input output : Nat} {K20 : FFT.Kernel 20}
    {K10 : FFT.Kernel 10} {twiddle : FFT.Field}
    (h : forward w q K20 K10 twiddle input = some output)
    (h20 : DyadicFFT.KernelContains q (FFT.toKernel K20) (cyclicFourier 20))
    (h10 : DyadicFFT.KernelContains q (FFT.toKernel K10) (cyclicFourier 10))
    (ht : DyadicFFT.Contains q (FFT.toField twiddle) fccTwiddle)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output))
      ((transform 0).conjTranspose *ᵥ v) := by
  rw [forward_eq h]
  exact FFT.forward_contains K20 K10 twiddle (decode w input) h20 h10 ht v hv

theorem inverse_contains {p w q input output : Nat} {K20 : FFT.Kernel 20}
    {K10 : FFT.Kernel 10} {twiddle : FFT.Field}
    (h : inverse w q K20 K10 twiddle input = some output)
    (h20 : DyadicFFT.KernelContains q (FFT.toKernel K20) (cyclicFourier 20))
    (h10 : DyadicFFT.KernelContains q (FFT.toKernel K10) (cyclicFourier 10))
    (ht : DyadicFFT.Contains q (FFT.toField twiddle) fccTwiddle)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w output)) (transform 0 *ᵥ v) := by
  rw [inverse_eq h]
  exact FFT.inverse_contains K20 K10 twiddle (decode w input) h20 h10 ht v hv

theorem subset_sound {p w a b : Nat} (h : subset w a b = true) {v : Cell → ℂ}
    (ha : DyadicFFT.Contains p (FFT.toField (decode w a)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w b)) v := by
  rintro ⟨x,y,z⟩
  have hx := List.all_eq_true.mp h _ (List.mem_ofFn.mpr ⟨x,rfl⟩)
  have hy := List.all_eq_true.mp hx _ (List.mem_ofFn.mpr ⟨y,rfl⟩)
  have hz := List.all_eq_true.mp hy _ (List.mem_ofFn.mpr ⟨z,rfl⟩)
  have hi := ha (x,y,z)
  simp only [FFT.toField, get_decode] at hi ⊢
  exact DyadicRectangle.subsetCheck_sound ((subsetCheck_eq _ _).symm.trans hz) hi

theorem inverse_native_contains {p w q input native : Nat} {K20 : FFT.Kernel 20}
    {K10 : FFT.Kernel 10} {twiddle : FFT.Field}
    (h : (inverse w q K20 K10 twiddle input).any (fun output => subset w output native) = true)
    (h20 : DyadicFFT.KernelContains q (FFT.toKernel K20) (cyclicFourier 20))
    (h10 : DyadicFFT.KernelContains q (FFT.toKernel K10) (cyclicFourier 10))
    (ht : DyadicFFT.Contains q (FFT.toField twiddle) fccTwiddle)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains p (FFT.toField (decode w input)) v) :
    DyadicFFT.Contains p (FFT.toField (decode w native)) (transform 0 *ᵥ v) := by
  obtain ⟨output,he,hs⟩ := (Option.any_eq_true _ _).mp h
  exact subset_sound hs (inverse_contains he h20 h10 ht v hv)

end Maxwell.Certificate.DyadicKernel.PackedFFT
