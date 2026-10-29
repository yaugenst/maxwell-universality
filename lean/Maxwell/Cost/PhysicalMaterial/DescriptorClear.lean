import Maxwell.Cost.PhysicalMaterial.DescriptorRead

namespace Maxwell.Cost.PhysicalMaterial.Descriptors
open Structured RationalAccumulator
set_option maxHeartbeats 1000000

private theorem clear_field (port : Fin 5) (input : List Bool) (tape : ℕ → Bool)
    (v : Fin 5 → ℕ) (s : Store) (hs : Ready s.val) (hv : Bank s.val v) :
    ∃ t, Executes input tape (.call (TapeOps.clear (targetTape port)))
      (6 * (v port).bits.length + 4) s t ∧ Ready t.val ∧
      Bank t.val (Function.update v port 0) ∧ Frame targets s.val t.val := by
  obtain ⟨origin, ho⟩ := hv port
  obtain ⟨t, et, ht, hf⟩ := WordCall.clear (targetTape port) input tape (v port).bits origin s ho
  have keep (i : ℕ) (hi : i ≠ targetTape port) : t.val.tapes i = s.val.tapes i := by simp [ht, hi]
  refine ⟨t, et, ?_, ?_, ⟨hf.2.2.1, hf.2.1, hf.2.2.2.1, hf.2.2.2.2.1, ?_⟩⟩
  · intro i hi
    exact blank_of_eq (keep i (by have := targetTape_bounds port; omega)) (hs i hi)
  · intro i
    by_cases he : i = port
    · subst i
      rw [Function.update_self]
      apply (zero_word_iff_blank _ _).mpr
      exact ⟨origin + (v port).bits.length, by simp [ht]⟩
    · rw [Function.update_of_ne he]
      exact word_of_eq (keep (targetTape i) (fun hh => he (targetTape_injective hh))) (hv i)
  · intro i _ hi
    exact keep i (by intro hh; subst i; exact hi (target_mem port))

def clearCode : Code := .seq (.call (TapeOps.clear 294)) (.seq (.call (TapeOps.clear 295))
  (.seq (.call (TapeOps.clear 296)) (.seq (.call (TapeOps.clear 276)) (.call (TapeOps.clear 277)))))

/-- Reclaim all five candidate fields after the current record has been tested. -/
theorem clear (input : List Bool) (tape : ℕ → Bool) (v : Fin 5 → ℕ) (B : ℕ)
    (hB : ∀ i, (v i).bits.length ≤ B) (s : Store) (hs : Ready s.val) (hv : Bank s.val v) :
    ∃ cost t, cost ≤ 30*B+20 ∧ Executes input tape clearCode cost s t ∧
      Ready t.val ∧ Bank t.val (fun _ => 0) ∧ Frame targets s.val t.val := by
  let v1 := Function.update v 0 0
  let v2 := Function.update v1 1 0
  let v3 := Function.update v2 2 0
  let v4 := Function.update v3 3 0
  obtain ⟨a, ea, ha, hav, fa⟩ := clear_field 0 input tape v s hs hv
  obtain ⟨b, eb, hb, hbv, fb⟩ := clear_field 1 input tape v1 a ha hav
  obtain ⟨c, ec, hc, hcv, fc⟩ := clear_field 2 input tape v2 b hb hbv
  obtain ⟨e, ee, he, hev, fe⟩ := clear_field 3 input tape v3 c hc hcv
  obtain ⟨t, et, ht, htv, ft⟩ := clear_field 4 input tape v4 e he hev
  have h1 : v1 1 = v 1 := by simp [v1]
  have h2 : v2 2 = v 2 := by simp [v2, v1]
  have h3 : v3 3 = v 3 := by simp [v3, v2, v1]
  have h4 : v4 4 = v 4 := by simp [v4, v3, v2, v1]
  have hzero : Function.update v4 4 0 = fun _ => 0 := by
    funext i
    fin_cases i <;> simp [v4, v3, v2, v1]
  refine ⟨_, t, ?_, ea.seq (eb.seq (ec.seq (ee.seq et))), ht,
    by simpa only [hzero] using htv, (((fa.trans fb).trans fc).trans fe).trans ft⟩
  rw [h1, h2, h3, h4]
  have b0 := hB 0
  have b1 := hB 1
  have b2 := hB 2
  have b3 := hB 3
  have b4 := hB 4
  omega

end Maxwell.Cost.PhysicalMaterial.Descriptors
