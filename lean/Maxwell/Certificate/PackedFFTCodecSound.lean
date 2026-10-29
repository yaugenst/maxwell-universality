import Maxwell.Certificate.DyadicPackedFFT
import Maxwell.Certificate.DyadicPackedSound

namespace Maxwell.Certificate.DyadicKernel.PackedFFT

theorem packChecked_eq_some {w n : Nat} {a : List Rectangle}
    (h : packChecked w a = some n) :
    n = Packed.packRects w a ∧ ∀ r ∈ a, Packed.fits w r = true := by
  induction a generalizing n with
  | nil =>
      have hn : n = 0 := by simpa [packChecked] using h.symm
      subst n
      exact ⟨rfl, by simp⟩
  | cons r tail ih =>
      simp only [packChecked] at h
      split at h
      next hr =>
        cases ht : packChecked w tail with
        | none => simp [ht] at h
        | some t =>
          have hn : Packed.packRect w r+2^(3*w)*t = n := by simpa [ht] using h
          obtain ⟨he,hfits⟩ := ih ht
          constructor
          · simpa only [Packed.packRects, he] using hn.symm
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hr
            · exact hfits x hx
      next => contradiction

theorem packChecked_get {w n : Nat} {a : List Rectangle}
    (h : packChecked w a = some n) (i : Nat) (hi : i < a.length) :
    Packed.getPacked w n i = a[i] := by
  obtain ⟨rfl,hfits⟩ := packChecked_eq_some h
  exact Packed.getPacked_packRects a hfits i hi

end Maxwell.Certificate.DyadicKernel.PackedFFT
