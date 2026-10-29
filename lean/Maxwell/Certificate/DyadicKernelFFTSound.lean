import Maxwell.Certificate.DyadicKernelFFT
import Maxwell.Certificate.DyadicKernelRoundedSound
import Maxwell.Certificate.DyadicFFTRows

namespace Maxwell.Certificate.DyadicKernel.FFT
open Maxwell.Spectral.PrimitiveYee Matrix FourierBinding

def toField (a : Field) : DyadicFFT.Field :=
  fun r => (get a r.1 r.2.1 r.2.2).toDyadic

def toKernel {n : ℕ} (K : Kernel n) : DyadicFFT.Kernel n :=
  fun i j => (K i j).toDyadic

@[simp] theorem get_build (a : Fin 20 → Fin 10 → Fin 10 → Rectangle)
    (x : Fin 20) (y z : Fin 10) : get (build a) x y z = a x y z := by
  simp [get, build]

theorem dotRound_checked {n : ℕ} (p q : ℕ) (a b : Fin n → Rectangle) :
    DyadicRectangle.dotCheck p q (fun i => (a i).toDyadic) (fun i => (b i).toDyadic)
      (dotRound q (List.ofFn fun i => (a i,b i))).toDyadic = true := by
  have h := round_checked q (dot (List.ofFn fun i => (a i,b i)))
  change dotCheck q (List.ofFn fun i => (a i,b i))
    (dotRound q (List.ofFn fun i => (a i,b i))) = true at h
  rw [dotCheck_eq p q, List.map_ofFn, DyadicRectangle.listDotCheck_ofFn_eq] at h
  exact h

theorem axisX_checked (p q : ℕ) (K : Kernel 20) (input : Field) :
    DyadicFFT.axisXCheck p q (toKernel K) (toField input) (toField (axisX q K input)) = true := by
  apply DyadicFFT.axisXCheck_of_rows
  rintro ⟨x,y,z⟩
  simpa only [toField, toKernel, axisX, get_build] using
    dotRound_checked p q (fun j => get input j y z) (K x)

theorem axisY_checked (p q : ℕ) (K : Kernel 10) (input : Field) :
    DyadicFFT.axisYCheck p q (toKernel K) (toField input) (toField (axisY q K input)) = true := by
  apply DyadicFFT.axisYCheck_of_rows
  rintro ⟨x,y,z⟩
  simpa only [toField, toKernel, axisY, get_build] using
    dotRound_checked p q (fun j => get input x j z) (K y)

theorem axisZ_checked (p q : ℕ) (K : Kernel 10) (input : Field) :
    DyadicFFT.axisZCheck p q (toKernel K) (toField input) (toField (axisZ q K input)) = true := by
  apply DyadicFFT.axisZCheck_of_rows
  rintro ⟨x,y,z⟩
  simpa only [toField, toKernel, axisZ, get_build] using
    dotRound_checked p q (fun j => get input x y j) (K z)

theorem diagonal_checked (p q : ℕ) (t input : Field) :
    DyadicFFT.diagonalCheck p q (toField t) (toField input)
      (toField (diagonal q t input)) = true := by
  apply DyadicFFT.diagonalCheck_of_rows
  rintro ⟨x,y,z⟩
  have h := round_checked q (mulExact (get input x y z) (get t x y z))
  rw [rescaleCheck_eq p q, toDyadic_mulExact] at h
  simpa only [toField, diagonal, get_build, mulRound] using h

@[simp] theorem toKernel_adjoint {n : ℕ} (K : Kernel n) :
    toKernel (adjoint K) = DyadicFFT.adjoint (toKernel K) := by
  ext i j
  exact toDyadic_conjugate (K j i)

@[simp] theorem toField_conjugate (a : Field) :
    toField (conjugateField a) = DyadicFFT.conjugate (toField a) := by
  ext r
  simp only [toField, conjugateField, get_build, DyadicFFT.conjugate,
    toDyadic_conjugate]

attribute [local irreducible] toField toKernel axisX axisY axisZ diagonal

theorem forward_contains {p q : ℕ} (K20 : Kernel 20) (K10 : Kernel 10)
    (twiddle input : Field)
    (h20 : DyadicFFT.KernelContains q (toKernel K20) (cyclicFourier 20))
    (h10 : DyadicFFT.KernelContains q (toKernel K10) (cyclicFourier 10))
    (ht : DyadicFFT.Contains q (toField twiddle) fccTwiddle)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains p (toField input) v) :
    DyadicFFT.Contains p (toField (forward q K20 K10 twiddle input))
      ((transform 0).conjTranspose *ᵥ v) := by
  let first := axisX q K20 input
  let second := diagonal q twiddle first
  let third := axisY q K10 second
  let result := axisZ q K10 third
  let w : DyadicFFT.Proposal := ⟨toField first,toField second,toField third,toField result⟩
  change DyadicFFT.Contains p w.result ((transform 0).conjTranspose *ᵥ v)
  apply DyadicFFT.forwardCheck_sound (toKernel K20) (toKernel K10) (toField twiddle)
    (toField input) w h20 h10 ht v hv
  exact DyadicFFT.forwardCheck_of_stages _ _ _ _ _ _ _
    (axisX_checked p q K20 input) (diagonal_checked p q twiddle first)
    (axisY_checked p q K10 second) (axisZ_checked p q K10 third)

theorem inverse_contains {p q : ℕ} (K20 : Kernel 20) (K10 : Kernel 10)
    (twiddle input : Field)
    (h20 : DyadicFFT.KernelContains q (toKernel K20) (cyclicFourier 20))
    (h10 : DyadicFFT.KernelContains q (toKernel K10) (cyclicFourier 10))
    (ht : DyadicFFT.Contains q (toField twiddle) fccTwiddle)
    (v : Cell → ℂ) (hv : DyadicFFT.Contains p (toField input) v) :
    DyadicFFT.Contains p (toField (inverse q K20 K10 twiddle input))
      (transform 0 *ᵥ v) := by
  let first := axisZ q (adjoint K10) input
  let second := axisY q (adjoint K10) first
  let third := diagonal q (conjugateField twiddle) second
  let result := axisX q (adjoint K20) third
  let w : DyadicFFT.Proposal := ⟨toField first,toField second,toField third,toField result⟩
  change DyadicFFT.Contains p w.result (transform 0 *ᵥ v)
  apply DyadicFFT.inverseCheck_sound (toKernel K20) (toKernel K10) (toField twiddle)
    (toField input) w h20 h10 ht v hv
  apply DyadicFFT.inverseCheck_of_stages
  · simpa only [toKernel_adjoint] using axisZ_checked p q (adjoint K10) input
  · simpa only [toKernel_adjoint] using axisY_checked p q (adjoint K10) first
  · simpa only [toField_conjugate] using diagonal_checked p q (conjugateField twiddle) second
  · simpa only [toKernel_adjoint] using axisX_checked p q (adjoint K20) third

theorem subsetRow_sound {p : ℕ} {a b : Field} {x : Fin 20}
    (h : subsetRow a b x = true) (y z : Fin 10) {v : ℂ}
    (ha : (get a x y z).toDyadic.Contains p v) :
    (get b x y z).toDyadic.Contains p v := by
  have hy := List.all_eq_true.mp h _ (List.mem_ofFn.mpr ⟨y,rfl⟩)
  have hz := List.all_eq_true.mp hy _ (List.mem_ofFn.mpr ⟨z,rfl⟩)
  apply DyadicRectangle.subsetCheck_sound _ ha
  exact (subsetCheck_eq _ _).symm.trans hz

end Maxwell.Certificate.DyadicKernel.FFT
