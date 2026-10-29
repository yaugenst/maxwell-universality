import Maxwell.Certificate.DyadicKernelVector
import Maxwell.Certificate.DyadicKernelRoundedDivision
import Maxwell.Certificate.DyadicKernelFFTSound

namespace Maxwell.Certificate.DyadicKernel
open Matrix

@[simp] theorem Triple.get_ofFn (a : Fin 3 → Rectangle) (i : Fin 3) :
    (Triple.ofFn a).get i = a i := by fin_cases i <;> rfl

@[simp] theorem Triple.toDyadic_get (a : Triple) (i : Fin 3) :
    (a.get i).toDyadic = a.toVector i := by fin_cases i <;> rfl

theorem dotRound_fin_contains {p q n : ℕ} {a b : Fin n → Rectangle}
    {z w : Fin n → ℂ}
    (ha : ∀ i, (a i).toDyadic.Contains p (z i))
    (hb : ∀ i, (b i).toDyadic.Contains q (w i)) :
    (dotRound q (List.ofFn fun i => (a i,b i))).toDyadic.Contains p (∑ i, z i*w i) :=
  DyadicRectangle.dotCheck_sound (FFT.dotRound_checked p q a b) ha hb

theorem dotTriple_contains {p : ℕ} {a b : Triple} {z w : Fin 3 → ℂ}
    (ha : ∀ i, (a.toVector i).Contains p (z i))
    (hb : ∀ i, (b.toVector i).Contains p (w i)) :
    (dotTriple p a b).toDyadic.Contains p (∑ i, z i*w i) := by
  change (dotRound p (List.ofFn fun i : Fin 3 => (a.get i,b.get i))).toDyadic.Contains p _
  exact dotRound_fin_contains (by simpa only [Triple.toDyadic_get] using ha)
    (by simpa only [Triple.toDyadic_get] using hb)

theorem laplacianRound_contains {p : ℕ} {d : Triple} {δ : Fin 3 → ℂ}
    (hd : ∀ i, (d.toVector i).Contains p (δ i)) :
    (laplacianRound p d).toDyadic.Contains p ((∑ i, Complex.normSq (δ i) : ℝ):ℂ) := by
  have hh : (laplacianRound p d).toDyadic.Contains p (∑ i, star (δ i)*δ i) := by
    change (dotRound p (List.ofFn fun i : Fin 3 => (conjugate (d.get i),d.get i))).toDyadic.Contains p _
    apply dotRound_fin_contains
    · intro i
      rw [toDyadic_conjugate, Triple.toDyadic_get]
      exact DyadicRectangle.conjugate_contains (hd i)
    · simpa only [Triple.toDyadic_get] using hd
  convert hh using 1
  simp only [Complex.ofReal_sum, Complex.star_def]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm, Complex.mul_conj]

theorem projectRound_contains {p : ℕ} {d raw result : Triple} {lap : Rectangle}
    {δ u : Fin 3 → ℂ} {l : ℝ}
    (h : projectRound p d raw lap = some result)
    (hd : ∀ i, (d.toVector i).Contains p (δ i))
    (hu : ∀ i, (raw.toVector i).Contains p (u i))
    (hl : lap.toDyadic.Contains p (l:ℂ)) (i : Fin 3) :
    (result.toVector i).Contains p (u i - star (δ i)*((∑ j, δ j*u j)/(l:ℂ))) := by
  unfold projectRound at h
  cases he : divRound p (dotTriple p d raw) lap with
  | none => simp [he] at h
  | some quotient =>
      simp [he] at h
      subst result
      rw [← Triple.toDyadic_get, Triple.get_ofFn, toDyadic_add, toDyadic_neg, Triple.toDyadic_get, sub_eq_add_neg]
      apply DyadicRectangle.add_contains (hu i)
      apply DyadicRectangle.neg_contains
      apply mulRound_contains
      · rw [toDyadic_conjugate, Triple.toDyadic_get]
        exact DyadicRectangle.conjugate_contains (hd i)
      · exact divRound_contains he (dotTriple_contains hd hu) hl

theorem curlRow_contains {p : ℕ} {d : Triple}
    {c : Maxwell.Spectral.PeriodicYee.Momentum} {f : FourierBinding.Frequency}
    (hd : ∀ i, (d.toVector i).Contains p (FourierBinding.symbol c f i)) (i j : Fin 3) :
    ((curlRow d i).get j).toDyadic.Contains p (FourierBinding.curlSymbolMatrix c f i j) := by
  have he : ((curlRow d i).get j).toDyadic = DyadicRectangle.curlMatrix d.toVector i j := by
    fin_cases i <;> fin_cases j <;> rfl
  rw [he]
  exact DyadicRectangle.curlMatrix_contains hd i j

theorem curlRound_contains {p : ℕ} {adjoint : Bool} {d u : Triple}
    {c : Maxwell.Spectral.PeriodicYee.Momentum} {f : FourierBinding.Frequency}
    {v : Fin 3 → ℂ}
    (hd : ∀ i, (d.toVector i).Contains p (FourierBinding.symbol c f i))
    (hu : ∀ i, (u.toVector i).Contains p (v i)) (i : Fin 3) :
    ((curlRound p adjoint d u).toVector i).Contains p
      (((if adjoint then (FourierBinding.curlSymbolMatrix c f).conjTranspose
         else FourierBinding.curlSymbolMatrix c f) *ᵥ v) i) := by
  rw [← Triple.toDyadic_get]
  simp only [curlRound, Triple.get_ofFn]
  apply dotRound_fin_contains
  · intro j
    cases adjoint
    · exact curlRow_contains hd i j
    · exact DyadicRectangle.conjugate_contains (curlRow_contains hd j i)
  · simpa only [Triple.toDyadic_get] using hu

theorem divideTriple_contains {p : ℕ} {u denominators result : Triple}
    {v : Fin 3 → ℂ} {m : Fin 3 → ℝ}
    (h : divideTriple p u denominators = some result)
    (hu : ∀ i, (u.toVector i).Contains p (v i))
    (hm : ∀ i, (denominators.toVector i).Contains p (m i:ℂ)) (i : Fin 3) :
    (result.toVector i).Contains p (v i/(m i:ℂ)) := by
  cases hx : divRound p u.x denominators.x with
  | none => simp [divideTriple,hx] at h
  | some x =>
    cases hy : divRound p u.y denominators.y with
    | none => simp [divideTriple,hx,hy] at h
    | some y =>
      cases hz : divRound p u.z denominators.z with
      | none => simp [divideTriple,hx,hy,hz] at h
      | some z =>
        simp [divideTriple,hx,hy,hz] at h
        subst result
        fin_cases i
        · exact divRound_contains hx (hu 0) (hm 0)
        · exact divRound_contains hy (hu 1) (hm 1)
        · exact divRound_contains hz (hu 2) (hm 2)

theorem magneticRound_contains {d weighted field : Triple}
    {c : Maxwell.Spectral.PeriodicYee.Momentum} {f : FourierBinding.Frequency}
    {v u : Fin 3 → ℂ}
    (hd : ∀ i, (d.toVector i).Contains 52 (FourierBinding.symbol c f i))
    (hv : ∀ i, (weighted.toVector i).Contains 52 (v i))
    (hu : ∀ i, (field.toVector i).Contains 52 (u i)) (i : Fin 3) :
    ((magneticRound d weighted field).toVector i).Contains 52
      ((FourierBinding.curlSymbolMatrix c f *ᵥ v) i - u i/64) := by
  let a : Fin 4 → Rectangle := Fin.cons ⟨-(2^46),0,0⟩ (fun j => (curlRow d i).get j)
  let b : Fin 4 → Rectangle := Fin.cons (field.get i) weighted.get
  have ha : ∀ j, (a j).toDyadic.Contains 52
      ((Fin.cons (-1/64:ℂ) (FourierBinding.curlSymbolMatrix c f i) : Fin 4 → ℂ) j) := by
    intro j
    refine Fin.cases ?_ (fun k => curlRow_contains hd i k) j
    exact DyadicRectangle.negativeFrequencySquared_contains
  have hb : ∀ j, (b j).toDyadic.Contains 52 ((Fin.cons (u i) v : Fin 4 → ℂ) j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [b, Fin.cons_zero, Triple.toDyadic_get] using hu i
    · simpa only [b, Fin.cons_succ, Triple.toDyadic_get] using hv k
  have hh := dotRound_fin_contains ha hb
  rw [← Triple.toDyadic_get]
  simp only [magneticRound,Triple.get_ofFn]
  change (dotRound 52 (List.ofFn fun j => (a j,b j))).toDyadic.Contains 52 _
  convert hh using 1
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Matrix.mulVec, dotProduct]
  ring

end Maxwell.Certificate.DyadicKernel
