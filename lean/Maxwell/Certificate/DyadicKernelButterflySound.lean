import Maxwell.Certificate.DyadicKernelButterfly
import Maxwell.Certificate.DyadicKernelFFTStrictSound
import Maxwell.Certificate.DyadicButterfly

namespace Maxwell.Certificate.DyadicKernel.Butterfly
open Matrix
set_option maxRecDepth 10000

def toValues (n : ℕ) (a : Values) : DyadicButterfly.Values n :=
  fun i => (get a i.val).toDyadic

theorem build_eq {n : ℕ} (f : Fin n → Rectangle) : build f = Array.ofFn f := by
  unfold build
  rw [FFT.collect_eq _ f (fun i k => FFT.forceRectangle_eq _ _), List.map_ofFn]
  apply Array.ext'
  exact (Array.toList_ofFn (f := f)).symm

@[simp] theorem get_build {n : ℕ} (f : Fin n → Rectangle) (i : Fin n) :
    get (build f) i.val = f i := by simp [build_eq, get]

theorem even_binding (n : ℕ) (a : Values) :
    toValues n (even n a) = DyadicButterfly.evenSamples (toValues (n*2) a) := by
  ext i
  simp [toValues, get, even, DyadicButterfly.evenSamples, finProdFinEquiv]

theorem odd_binding (n : ℕ) (a : Values) :
    toValues n (odd n a) = DyadicButterfly.oddSamples (toValues (n*2) a) := by
  ext i
  simp [toValues, get, odd, DyadicButterfly.oddSamples, finProdFinEquiv, Nat.add_comm]

attribute [local irreducible] build five pair combine

theorem five_checked (p : ℕ) (root : ℤ → Rectangle)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m) (stride : ℤ) (input : Values) :
    DyadicButterfly.fiveCheck p stride (toValues 5 input)
      (toValues 5 (five root stride input)) = true := by
  apply decide_eq_true
  intro k
  change DyadicRectangle.dotCheck p 52 (fun j : Fin 5 => (get input j.val).toDyadic)
    (fun j => FFTWitness.root (stride*k.val*j.val)) (get (five root stride input) k.val).toDyadic = true
  rw [five, get_build]
  simpa only [hr] using
    FFT.dotRound_checked p 52 (fun j : Fin 5 => get input j.val)
      (fun j => root (stride*k.val*j.val))

theorem pair_checked (p : ℕ) (root : ℤ → Rectangle)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m) (phase : ℤ) (upper : Bool)
    (ev od : Rectangle) :
    DyadicButterfly.pairCheck p phase upper ev.toDyadic od.toDyadic
      (pair root phase upper ev od).toDyadic = true := by
  have h := FFT.dotRound_checked p 52
    (![ev,if upper then neg od else od]) (![unit52,root phase])
  have he : (fun i : Fin 2 => (![ev,if upper then neg od else od] i).toDyadic) =
      ![ev.toDyadic,if upper then od.toDyadic.neg else od.toDyadic] := by
    ext i
    fin_cases i
    · rfl
    · change (if upper then neg od else od).toDyadic =
        if upper then od.toDyadic.neg else od.toDyadic
      cases upper
      · rfl
      · exact toDyadic_neg od
  have hk : (fun i : Fin 2 => (![unit52,root phase] i).toDyadic) =
      ![DyadicButterfly.unit52,FFTWitness.root phase] := by
    ext i
    fin_cases i
    · rfl
    · exact hr phase
  have hl : (List.ofFn fun i : Fin 2 =>
      (![ev,if upper then neg od else od] i, ![unit52,root phase] i)) =
        [(ev,unit52),(if upper then neg od else od,root phase)] := rfl
  rw [hl, he, hk] at h
  simpa only [DyadicButterfly.pairCheck, pair] using h

theorem combine_checked (n p : ℕ) (root : ℤ → Rectangle)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m) (stride : ℤ) (ev od : Values) :
    DyadicButterfly.butterflyCheck n p stride (toValues n ev) (toValues n od)
      (toValues (n*2) (combine n root stride ev od)) = true := by
  apply decide_eq_true
  intro a
  by_cases ha : a.val < n
  · simp only [dite_eq_left ha]
    change DyadicButterfly.pairCheck p (stride*a.val) false
      (get ev a.val).toDyadic (get od a.val).toDyadic
      (get (combine n root stride ev od) a.val).toDyadic = true
    rw [combine, get_build]
    simpa only [ite_eq_left ha,
      show decide (n ≤ a.val) = false from decide_eq_false (Nat.not_le.mpr ha)] using
      pair_checked p root hr (stride*a.val) false (get ev a.val) (get od a.val)
  · simp only [dite_eq_right ha]
    change DyadicButterfly.pairCheck p (stride*((a.val-n : ℕ) : ℤ)) true
      (get ev (a.val-n)).toDyadic (get od (a.val-n)).toDyadic
      (get (combine n root stride ev od) a.val).toDyadic = true
    rw [combine, get_build]
    simpa only [ite_eq_right ha,
      show decide (n ≤ a.val) = true from decide_eq_true (Nat.le_of_not_gt ha)] using
      pair_checked p root hr (stride*((a.val-n : ℕ) : ℤ)) true (get ev (a.val-n)) (get od (a.val-n))

def tenProposal (w : Ten) : DyadicButterfly.TenProposal :=
  ⟨toValues 5 w.even5,toValues 5 w.odd5,toValues 10 w.result⟩

def twentyProposal (w : Twenty) : DyadicButterfly.TwentyProposal :=
  ⟨tenProposal w.even10,tenProposal w.odd10,toValues 20 w.result⟩

theorem ten_checked (p : ℕ) (root : ℤ → Rectangle)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m) (sign : ℤ) (input : Values) :
    DyadicButterfly.tenCheck p sign (toValues 10 input)
      (tenProposal (ten root sign input)) = true := by
  simp only [DyadicButterfly.tenCheck, Bool.and_eq_true_iff, tenProposal, ten]
  exact ⟨⟨by simpa only [even_binding] using five_checked p root hr (4*sign) (even 5 input),
    by simpa only [odd_binding] using five_checked p root hr (4*sign) (odd 5 input)⟩,
      combine_checked 5 p root hr (2*sign) _ _⟩

theorem twenty_checked (p : ℕ) (root : ℤ → Rectangle)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m) (sign : ℤ) (input : Values) :
    DyadicButterfly.twentyCheck p sign (toValues 20 input)
      (twentyProposal (twenty root sign input)) = true := by
  simp only [DyadicButterfly.twentyCheck, Bool.and_eq_true_iff, twentyProposal, twenty]
  exact ⟨⟨by simpa only [even_binding] using ten_checked p root hr sign (even 10 input),
    by simpa only [odd_binding] using ten_checked p root hr sign (odd 10 input)⟩,
      combine_checked 10 p root hr sign _ _⟩

theorem normalize_checked (n p : ℕ) (norm : Rectangle) (input : Values) :
    DyadicButterfly.normalizeCheck p norm.toDyadic (toValues n input)
      (toValues n (normalize n norm input)) = true := by
  apply decide_eq_true
  intro i
  have h := round_checked 52 (mulExact (get input i.val) norm)
  rw [rescaleCheck_eq p 52, toDyadic_mulExact] at h
  simpa only [toValues, normalize, get_build, mulRound] using h


theorem transform10_forward_contains (p : ℕ) (root : ℤ → Rectangle)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (norm : Rectangle) (hn : norm.toDyadic = FFTWitness.norm10)
    (input : Values) (v : Fin 10 → ℂ)
    (hv : DyadicButterfly.Contains p (toValues 10 input) v) :
    DyadicButterfly.Contains p (toValues 10 (transform10 root norm (-1) input))
      (FourierBinding.cyclicFourier 10 *ᵥ v) := by
  apply DyadicButterfly.tenForward_sound (w := tenProposal (ten root (-1) input)) hv
  apply Bool.and_eq_true_iff.mpr
  refine ⟨ten_checked p root hr (-1) input, ?_⟩
  simpa only [hn, transform10, tenProposal] using
    normalize_checked 10 p norm (ten root (-1) input).result


theorem transform10_inverse_contains (p : ℕ) (root : ℤ → Rectangle)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (norm : Rectangle) (hn : norm.toDyadic = FFTWitness.norm10)
    (input : Values) (v : Fin 10 → ℂ)
    (hv : DyadicButterfly.Contains p (toValues 10 input) v) :
    DyadicButterfly.Contains p (toValues 10 (transform10 root norm 1 input))
      ((FourierBinding.cyclicFourier 10).conjTranspose *ᵥ v) := by
  apply DyadicButterfly.tenInverse_sound (w := tenProposal (ten root 1 input)) hv
  apply Bool.and_eq_true_iff.mpr
  refine ⟨ten_checked p root hr 1 input, ?_⟩
  simpa only [hn, transform10, tenProposal] using
    normalize_checked 10 p norm (ten root 1 input).result


theorem transform20_forward_contains (p : ℕ) (root : ℤ → Rectangle)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (norm : Rectangle) (hn : norm.toDyadic = FFTWitness.norm20)
    (input : Values) (v : Fin 20 → ℂ)
    (hv : DyadicButterfly.Contains p (toValues 20 input) v) :
    DyadicButterfly.Contains p (toValues 20 (transform20 root norm (-1) input))
      (FourierBinding.cyclicFourier 20 *ᵥ v) := by
  apply DyadicButterfly.twentyForward_sound (w := twentyProposal (twenty root (-1) input)) hv
  apply Bool.and_eq_true_iff.mpr
  refine ⟨twenty_checked p root hr (-1) input, ?_⟩
  simpa only [hn, transform20, twentyProposal] using
    normalize_checked 20 p norm (twenty root (-1) input).result


theorem transform20_inverse_contains (p : ℕ) (root : ℤ → Rectangle)
    (hr : ∀ m, (root m).toDyadic = FFTWitness.root m)
    (norm : Rectangle) (hn : norm.toDyadic = FFTWitness.norm20)
    (input : Values) (v : Fin 20 → ℂ)
    (hv : DyadicButterfly.Contains p (toValues 20 input) v) :
    DyadicButterfly.Contains p (toValues 20 (transform20 root norm 1 input))
      ((FourierBinding.cyclicFourier 20).conjTranspose *ᵥ v) := by
  apply DyadicButterfly.twentyInverse_sound (w := twentyProposal (twenty root 1 input)) hv
  apply Bool.and_eq_true_iff.mpr
  refine ⟨twenty_checked p root hr 1 input, ?_⟩
  simpa only [hn, transform20, twentyProposal] using
    normalize_checked 20 p norm (twenty root 1 input).result

end Maxwell.Certificate.DyadicKernel.Butterfly
