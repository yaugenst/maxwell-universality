import Maxwell.Cost.CalibrationSource.IndexArray.Entry
import Maxwell.Cost.CalibrationMatrix.GenerationPrefix

namespace Maxwell.Cost.CalibrationSource.IndexArray
open Structured BankArray
open RationalAccumulator (Blank)
open Defect.FiniteStencil Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def words {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (d N width : ℕ) :
    Vector (List Bool) m :=
  Vector.ofFn fun i => FixedWidth.bits width (address R0 L v (edges i) d N).bits

@[simp] theorem words_get {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (d N width : ℕ) (i : Fin m) :
    (words R0 L v edges d N width).get i = FixedWidth.bits width (address R0 L v (edges i) d N).bits := by
  simp [words,Vector.get,Fin.cast]

/-- The source support is fixed for the platform, so its finite enumeration
is unrolled into literal arithmetic programs, each with an actual array write. -/
def prefixCode {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) : (n : ℕ) → n ≤ m → Code
  | 0, _ => .skip
  | n+1, hn => .seq (prefixCode R0 L v edges n (by omega))
      (entryCode R0 L v (edges ⟨n,by omega⟩) n)

def code {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) : Code :=
  prefixCode R0 L v edges m le_rfl

def costCap (m B : ℕ) : ℕ := 1+m*entryCost B

private theorem prefix_executes {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge)
    (d N B : ℕ) (c : Data) (n : ℕ) (hn : n ≤ m)
    (hsize : Sized R0 L d N c B) (hm : m.bits.length ≤ B)
    (hc : ∀ i, ∀ a ∈ indexInstructions R0 L v (edges i), a.literalWidth ≤ B)
    (hfit : ∀ i, (address R0 L v (edges i) d N).bits.length ≤ addressValue c.width)
    (initial : Vector (List Bool) m) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Stored R0 L d N c s.val) (hw : Workspace s.val)
    (ha : BitArray.Represents s.val.memory (addressValue c.base) (addressValue c.width) initial) :
    ∃ cost t, cost ≤ costCap n B ∧ Executes input tape (prefixCode R0 L v edges n hn) cost s t ∧
      Stored R0 L d N c t.val ∧ Workspace t.val ∧
      BitArray.Represents t.val.memory (addressValue c.base) (addressValue c.width)
        (CalibrationMatrix.GenerationPrefix.written initial (words R0 L v edges d N (addressValue c.width)) n) ∧
      Frame s.val t.val ∧ Outside c m s.val t.val := by
  induction n with
  | zero =>
    exact ⟨1,s,by simp [costCap],.skip s,hs,hw,by simpa only [CalibrationMatrix.GenerationPrefix.zero] using ha,
      Frame.refl _,Outside.refl _ _ _⟩
  | succ n ih =>
    obtain ⟨a,p,hca,ea,hps,hpw,hpa,hpf,hpo⟩ := ih (by omega)
    let i : Fin m := ⟨n,by omega⟩
    have hiwidth : i.val.bits.length ≤ B := by
      have h := Nat.size_le_size (Nat.le_of_lt i.isLt)
      rw [← Nat.size_eq_bits_len,← Nat.size_eq_bits_len] at h
      exact h.trans hm
    obtain ⟨b,t,hcb,eb,hts,htw,htm,hta,htf⟩ := entry_executes R0 L v (edges i) d N B c i
      hiwidth hsize (hc i) (hfit i) _ input tape p hps hpw hpa
    have htout := Outside.of_write i _ (FixedWidth.bits_length _ _) htm
    refine ⟨a+b,t,by dsimp only [costCap] at *; nlinarith only [hca,hcb],ea.seq eb,hts,htw,?_,
      hpf.trans htf,hpo.trans htout⟩
    rw [← words_get R0 L v edges d N (addressValue c.width) i,
      CalibrationMatrix.GenerationPrefix.step _ _ i] at hta
    exact hta

/-- Initialize the complete sparse-index array from the fixed support.
Every initial memory bit may be arbitrary; the returned array is produced
by actual arithmetic and indexed writes. -/
theorem executes {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge)
    (d N B : ℕ) (c : Data) (hsize : Sized R0 L d N c B) (hm : m.bits.length ≤ B)
    (hc : ∀ i, ∀ a ∈ indexInstructions R0 L v (edges i), a.literalWidth ≤ B)
    (hfit : ∀ i, (address R0 L v (edges i) d N).bits.length ≤ addressValue c.width)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Stored R0 L d N c s.val) (hw : Workspace s.val) :
    ∃ cost t, cost ≤ costCap m B ∧ Executes input tape (code R0 L v edges) cost s t ∧
      Stored R0 L d N c t.val ∧ Workspace t.val ∧
      BitArray.Represents t.val.memory (addressValue c.base) (addressValue c.width)
        (words R0 L v edges d N (addressValue c.width)) ∧
      Frame s.val t.val ∧ Outside c m s.val t.val := by
  obtain ⟨cost,t,hcost,he,hts,htw,hta,htf,hto⟩ := prefix_executes R0 L v edges d N B c m le_rfl
    hsize hm hc hfit (BitArray.snapshot s.val.memory (addressValue c.base) (addressValue c.width) m)
    input tape s hs hw (BitArray.snapshot_represents _ _ _ _)
  exact ⟨cost,t,hcost,he,hts,htw,by simpa only [CalibrationMatrix.GenerationPrefix.complete] using hta,htf,hto⟩

end Maxwell.Cost.CalibrationSource.IndexArray
