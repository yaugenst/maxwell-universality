import Maxwell.Certificate.DyadicPackedRowsFFT
import Maxwell.Certificate.PackedFFTCodecSound

namespace Maxwell.Certificate.DyadicKernel.PackedRowsFFT

theorem collectList_spec {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : collectList f xs = some ys) :
    ys.length = xs.length ∧ ∀ i : Nat, (xs[i]?).bind f = ys[i]? := by
  induction xs generalizing ys with
  | nil =>
      have he : ys=[] := by simpa [collectList] using h.symm
      subst ys
      exact ⟨rfl,by simp⟩
  | cons x xs ih =>
      cases hx : f x with
      | none => simp [collectList,hx] at h
      | some y =>
          cases ht : collectList f xs with
          | none => simp [collectList,hx,ht] at h
          | some zs =>
              have he : y::zs=ys := by simpa [collectList,hx,ht] using h
              subst ys
              obtain ⟨hl,hget⟩ := ih ht
              constructor
              · simpa using hl
              · intro i
                cases i with
                | zero => simpa using hx
                | succ i => simpa using hget i

theorem collect_spec {n : Nat} {α : Type} {f : Fin n → Option α} {a : Array α}
    (h : collect f = some a) : a.size=n ∧ ∀ i : Fin n, f i = a[i.val]? := by
  cases ht : collectList f (List.ofFn fun i : Fin n => i) with
  | none => simp [collect,ht] at h
  | some xs =>
      have he : xs.toArray=a := by simpa [collect,ht] using h
      subst a
      obtain ⟨hl,hget⟩ := collectList_spec ht
      constructor
      · simpa using hl
      · intro i
        simpa using hget i.val

theorem collect_getD {n : Nat} {α : Type} (fallback : α)
    {f : Fin n → Option α} {a : Array α} (h : collect f = some a) (i : Fin n) :
    f i = some ((a[i.val]?).getD fallback) := by
  obtain ⟨hsize,hget⟩ := collect_spec h
  have hi : i.val < a.size := by omega
  rw [hget i]
  simp [Array.getElem?_eq_getElem hi]

theorem get_build {w : Nat} {f : Fin 20 → Fin 10 → Fin 10 → Rectangle} {a : Field}
    (h : build w f = some a) (x : Fin 20) (y z : Fin 10) : get w a x y z = f x y z := by
  have hx := collect_getD #[] h x
  have hy := collect_getD 0 hx y
  have hz := PackedFFT.packChecked_get hy z.val (by simp)
  simpa only [get,List.getElem_ofFn] using hz

end Maxwell.Certificate.DyadicKernel.PackedRowsFFT
