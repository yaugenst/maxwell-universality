import Maxwell.Cost.RealArrayNormalize.Correctness
import Maxwell.Cost.RealVectorCode
import Maxwell.Cost.RealWordFrame

namespace Maxwell.Cost.RealNormalizeSerialize
open RealNatCode (Layout StoredWord)
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- Normalize the actual coefficient/source array, retain its scale in
real register20, and write its count-prefixed rounded canonical bytes. -/
def program (byCount : Bool) : Machine := ⟨
  ((RealArrayNormalize.program byCount).code.map (RAMInstruction.relocate 0 42)) ++
  [.indexCopy 24 25, .copy 20 7] ++
  (RealVectorCode.program.code.map (RAMInstruction.relocate 44 258)) ++ [.halt]⟩

theorem contains_normalize (byCount : Bool) :
    (program byCount).Contains (RealArrayNormalize.program byCount) 0 42 := by
  intro i; cases byCount <;> fin_cases i <;> rfl

theorem contains_vector (byCount : Bool) :
    (program byCount).Contains RealVectorCode.program 44 258 := by
  intro i; cases byCount <;> fin_cases i <;> rfl

noncomputable def prepared (s : RAMState) : RAMState :=
  (s.setIndex 24 (s.indices 25)).setWord 20 (s.words 7)

theorem prepare_steps (byCount : Bool) (input : RAMInput) (tape : ℕ → Bool)
    (s : RAMState) (hpc : s.pc = 42) :
    execute ((program byCount).next input tape) 2 s = some (prepared s) := by
  cases byCount <;> simp [execute, program, RealArrayNormalize.program, Machine.next, hpc,
    prepared, RAMState.setWord, RAMState.setIndex]

theorem vector_words_bound : RealVectorCode.program.writesWordsBelow 17 = true := by decide

/-- A single actual finite execution binds the original real array to the
rounded rational codec. No external tape is replaced between stages. -/
theorem terminates (byCount : Bool) (input : RAMInput) (tape : ℕ → Bool) (L : Layout)
    (base n p : ℕ) (v : ℕ → ℝ) (s : RAMState) (hbase : 32 ≤ base)
    (hpc : s.pc = 0) (hs : s.indices 25 = base) (hn : s.indices 26 = n)
    (hp : s.indices 27 = p) (hc : s.indices 20 = L.cache)
    (hb : s.indices 21 = L.buffer) (hstride : s.indices 22 = L.stride)
    (hv : ∀ j < n, s.words (base + j) = v j) :
    ∃ cost : ℕ, ∃ t : RAMState,
      cost ≤ (59 * p + 189) * n + 23 * n.size + 41 ∧
      Terminates ((program byCount).next input tape) cost s t ∧ t.pc = 258 ∧
      StoredWord t L (Codec.list Codec.rat
        (RealVectorCode.values (RealNormalize.normalized byCount n v) p n)) ∧
      t.words 20 = RealNormalize.scale byCount n v := by
  obtain ⟨a, ha, hapc, _, hascale, havalues, haframe⟩ :=
    RealArrayNormalize.terminates byCount input tape base n v s hbase hpc hs hn hv
  have hcall₁ := (contains_normalize byCount).call input tape ha.toSteps (by
    simp [RealArrayNormalize.program, hapc])
  have hstart : s.relocate 0 = s := by simp [RAMState.relocate]
  rw [hstart] at hcall₁
  let b := prepared {a with pc := 42}
  have hm (i : ℕ) (hi : 4 ≤ i) (hne : i ≠ 24) : a.indices i = s.indices i :=
    haframe.indices i hi hne
  have hbvalues : ∀ j < n, b.words (base + j) = RealNormalize.normalized byCount n v j := by
    intro j hj
    simpa [b, prepared, RAMState.setWord, RAMState.setIndex, show base + j ≠ 20 by omega] using havalues j hj
  have hbmeta (i : ℕ) (hi : 4 ≤ i) (hne : i ≠ 24) : b.indices i = s.indices i := by
    simpa [b, prepared, RAMState.setWord, RAMState.setIndex, hne] using hm i hi hne
  obtain ⟨cost, t, hbound, ht, htpc, hstored⟩ := RealVectorCode.terminates input tape L base n p
    (RealNormalize.normalized byCount n v) {b with pc := 0} hbase rfl
    (by simp [b, prepared, RAMState.setWord, RAMState.setIndex, hm 25 (by omega) (by omega), hs])
    ((hbmeta 26 (by omega) (by omega)).trans hn) ((hbmeta 27 (by omega) (by omega)).trans hp)
    ((hbmeta 20 (by omega) (by omega)).trans hc) ((hbmeta 21 (by omega) (by omega)).trans hb)
    ((hbmeta 22 (by omega) (by omega)).trans hstride) hbvalues
  have hcall₂ := (contains_vector byCount).call_at input tape b t (by simp [b, prepared, RAMState.setWord, RAMState.setIndex])
    ht.toSteps (by simp [RealVectorCode.program, RealNatCode.program, RealArrayCode.program,
      RealRoundRat.program, RealMidpointRegister.program, RealMidpointRegister.kernel,
      RealMidpoint.program, RealRound.program, RealMidpointRegister.adapt, RealRatCode.program, htpc])
  have hprepare := execute_sound _ (prepare_steps byCount input tape {a with pc := 42} rfl)
  refine ⟨(22 * n + 15 + 1) + 2 + (cost + 1), {t with pc := 258}, ?_, ?_, rfl, hstored, ?_⟩
  · nlinarith
  · exact ((hcall₁.trans hprepare).trans hcall₂).terminates
      (Terminates.halt _ (by
        cases byCount <;> simp [program, RealArrayNormalize.program, RealVectorCode.program,
          RealNatCode.program, RealArrayCode.program, RealRoundRat.program, RealMidpointRegister.program,
          RealMidpointRegister.kernel, RealMidpoint.program, RealRound.program,
          RealMidpointRegister.adapt, RealRatCode.program, Machine.next]))
  · have he := ht.high_word vector_words_bound 20 (by omega)
    simpa [b, prepared, RAMState.setWord, RAMState.setIndex, hascale] using he

end Maxwell.Cost.RealNormalizeSerialize
