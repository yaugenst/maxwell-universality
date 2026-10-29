import Maxwell.Certificate.DyadicKernelFFTStrict
import Maxwell.Certificate.DyadicKernelFFTSound

namespace Maxwell.Certificate.DyadicKernel.FFT

@[simp] theorem forceNat_eq {α : Type} (n : ℕ) (k : ℕ → α) : forceNat n k = k n := by
  cases n <;> rfl

@[simp] theorem forceInt_eq {α : Type} (n : ℤ) (k : ℤ → α) : forceInt n k = k n := by
  cases n <;> simp [forceInt]

@[simp] theorem forceRectangle_eq {α : Type} (a : Rectangle) (k : Rectangle → α) :
    forceRectangle a k = k a := by
  cases a
  simp [forceRectangle]

theorem collect_eq {α β γ : Type} (f : α → (β → γ) → γ) (g : α → β)
    (hf : ∀ a k, f a k = k (g a)) (xs : List α) (k : List β → γ) :
    collect f xs k = k (xs.map g) := by
  induction xs generalizing k with
  | nil => rfl
  | cons a xs ih => rw [collect, hf, ih, List.map_cons]

@[simp] theorem buildStrict_eq (a : Fin 20 → Fin 10 → Fin 10 → Rectangle) :
    buildStrict a = build a := by
  unfold buildStrict
  have hz (x : Fin 20) (y : Fin 10) (k : List Rectangle → Field) :
      collect (fun z kz => forceRectangle (a x y z) kz)
        (List.ofFn fun z : Fin 10 => z) k = k (List.ofFn (a x y)) := by
    rw [collect_eq _ (a x y) (fun z kz => forceRectangle_eq _ _) , List.map_ofFn]
    rfl
  have hy (x : Fin 20) (k : List (Array Rectangle) → Field) :
      collect (fun y ky => collect (fun z kz => forceRectangle (a x y z) kz)
        (List.ofFn fun z : Fin 10 => z) (fun zs => ky ⟨zs⟩))
        (List.ofFn fun y : Fin 10 => y) k =
          k (List.ofFn fun y => (⟨List.ofFn (a x y)⟩ : Array Rectangle)) := by
    rw [collect_eq _ (fun y => (⟨List.ofFn (a x y)⟩ : Array Rectangle))
      (fun y ky => hz x y _), List.map_ofFn]
    rfl
  rw [collect_eq _ (fun x => (⟨List.ofFn fun y =>
    (⟨List.ofFn (a x y)⟩ : Array Rectangle)⟩ : Array (Array Rectangle)))
    (fun x kx => hy x _), List.map_ofFn]
  have hm {n : ℕ} {α : Type} (f : Fin n → α) :
      (⟨List.ofFn f⟩ : Array α) = Array.ofFn f := by
    apply Array.ext'
    exact (Array.toList_ofFn (f := f)).symm
  simp only [Function.comp_def, hm, build]

@[simp] theorem axisXStrict_eq (q : ℕ) (K : Kernel 20) (a : Field) :
    axisXStrict q K a = axisX q K a := by simp [axisXStrict, axisX]

@[simp] theorem axisYStrict_eq (q : ℕ) (K : Kernel 10) (a : Field) :
    axisYStrict q K a = axisY q K a := by simp [axisYStrict, axisY]

@[simp] theorem axisZStrict_eq (q : ℕ) (K : Kernel 10) (a : Field) :
    axisZStrict q K a = axisZ q K a := by simp [axisZStrict, axisZ]

@[simp] theorem diagonalStrict_eq (q : ℕ) (t a : Field) :
    diagonalStrict q t a = diagonal q t a := by simp [diagonalStrict, diagonal]

theorem forwardStrict_eq (q : ℕ) (K20 : Kernel 20) (K10 : Kernel 10)
    (twiddle input : Field) : forwardStrict q K20 K10 twiddle input =
      forward q K20 K10 twiddle input := by
  simp only [forwardStrict, forward, axisXStrict_eq, diagonalStrict_eq, axisYStrict_eq, axisZStrict_eq]

theorem inverseStrict_eq (q : ℕ) (K20 : Kernel 20) (K10 : Kernel 10)
    (twiddle input : Field) : inverseStrict q K20 K10 twiddle input =
      inverse q K20 K10 twiddle input := by
  simp only [inverseStrict, inverse, axisXStrict_eq, diagonalStrict_eq, axisYStrict_eq, axisZStrict_eq]

end Maxwell.Certificate.DyadicKernel.FFT
