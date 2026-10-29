import Maxwell.Cost.PhysicalMaterial.DescriptorClear
import Maxwell.Cost.BinaryPrecision

namespace Maxwell.Cost.PhysicalMaterial
open Structured RationalAccumulator
set_option maxHeartbeats 1000000

def copyReplaceCode (source target : ℕ) : Code :=
  .seq (.call (TapeOps.clear target)) (.call (WordTransfer.clone source target))

/-- Replace one runtime word by a preserved copy of another runtime word. -/
theorem copy_replace (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (old new : ℕ) (s : Store)
    (hs : Word s.val source new) (ht : Word s.val target old) :
    ∃ t, Executes input tape (copyReplaceCode source target)
      (6*old.bits.length+15*new.bits.length+21) s t ∧ Word t.val target new ∧
      BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨so, hso⟩ := hs
  obtain ⟨origin, ho⟩ := ht
  obtain ⟨a, ea, hat, fa⟩ := WordCall.clear target input tape old.bits origin s ho
  have has : a.val.tapes source = BitTape.shifted new.bits so := by simpa [hat, hne] using hso
  have hab : a.val.tapes target = {BitTape.blank with head := origin + old.bits.length} := by simp [hat]
  obtain ⟨t, et, htt, ft⟩ := WordCall.clone source target hne input tape new.bits so
    (origin + old.bits.length) a has hab
  refine ⟨t, ?_, ⟨origin + old.bits.length, by simp [htt]⟩,
    ⟨ft.1.trans fa.1, ft.2.1.trans fa.2.1, ft.2.2.1.trans fa.2.2.1,
      ft.2.2.2.1.trans fa.2.2.2.1, ft.2.2.2.2.1.trans fa.2.2.2.2.1, ?_⟩⟩
  · convert ea.seq et using 1 <;> first | rfl | omega
  · intro i hi
    have hit : i ≠ target := by simpa using hi
    simp [htt, hat, hit]

def replacePairCode : Code := .seq (copyReplaceCode 276 272) (copyReplaceCode 277 273)
def selectPairCode : Code := .branch 2 replacePairCode .skip

def Pair (s : BitRAMState) (p : ℕ × ℕ) : Prop := Word s 272 p.1 ∧ Word s 273 p.2

theorem replace_pair (input : List Bool) (tape : ℕ → Bool) (old new : ℕ × ℕ)
    (s : Store) (hold : Pair s.val old) (hn : Word s.val 276 new.1) (hd : Word s.val 277 new.2) :
    ∃ t, Executes input tape replacePairCode
      (6*(old.1.bits.length+old.2.bits.length)+15*(new.1.bits.length+new.2.bits.length)+42) s t ∧
      Pair t.val new ∧ BinaryPrecision.Frame {272, 273} s.val t.val := by
  obtain ⟨a, ea, ha, fa⟩ := copy_replace 276 272 (by decide) input tape old.1 new.1 s hn hold.1
  obtain ⟨t, et, ht, ft⟩ := copy_replace 277 273 (by decide) input tape old.2 new.2 a
    (word_of_eq (fa.tapes 277 (by decide)) hd) (word_of_eq (fa.tapes 273 (by decide)) hold.2)
  refine ⟨t, ?_, ⟨word_of_eq (ft.tapes 272 (by decide)) ha, ht⟩,
    (fa.mono (by decide)).trans (ft.mono (by decide))⟩
  convert ea.seq et using 1 <;> first | rfl | omega

/-- The selected pair is copied only on the machine's actual test bit. -/
theorem select_pair (input : List Bool) (tape : ℕ → Bool) (old new : ℕ × ℕ) (hit : Bool)
    (B : ℕ) (hB : old.1.bits.length ≤ B ∧ old.2.bits.length ≤ B ∧
      new.1.bits.length ≤ B ∧ new.2.bits.length ≤ B)
    (s : Store) (hold : Pair s.val old) (hn : Word s.val 276 new.1) (hd : Word s.val 277 new.2)
    (hhit : s.val.registers 2 = hit) :
    ∃ cost t, cost ≤ 42*B+43 ∧ Executes input tape selectPairCode cost s t ∧
      Pair t.val (if hit then new else old) ∧ BinaryPrecision.Frame {272, 273} s.val t.val := by
  cases hit
  · exact ⟨2, s, by omega, .no hhit (.skip s), hold, .refl _ _⟩
  · obtain ⟨t, et, ht, ft⟩ := replace_pair input tape old new s hold hn hd
    refine ⟨_, t, ?_, .yes hhit et, ht, ft⟩
    omega

end Maxwell.Cost.PhysicalMaterial
