import Maxwell.Cost.PhysicalMaterial.DenseEmit
import Maxwell.Cost.PhysicalMaterial.FlattenIndex

namespace Maxwell.Cost.PhysicalMaterial.CellEmit
open Structured RationalAccumulator Maxwell.Spectral.Lattice
set_option maxHeartbeats 1400000

def work : Finset ℕ := DenseEmit.work ∪ {322}
structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  tapes : ∀ j ∉ work, t.tapes j = s.tapes j

def code (material : Cell20 → ℚ) : Code :=
  .seq (FlattenIndex.code 240 241 242) (.seq (DenseEmit.code material) (.call (TapeOps.clear 322)))
def costBound (material : Cell20 → ℚ) (x y z B : ℕ) : ℕ :=
  20000*(B+2)^2+DenseEmit.costBound material x y z B+6*B+4

/-- One runtime cell computes its own flattened address, reads its two dense
strength fields, emits the canonical rational, and clears the index. -/
theorem executes {cells : ℕ} (l : Dense.Layout cells) (nums dens : Vector (List Bool) cells)
    (i : Fin cells) (B : ℕ) (hl : l.Sized B) (hi : i.val.bits.length ≤ B)
    (material : Cell20 → ℚ) (hm : ∀ c, 0 ≤ material c)
    (input : List Bool) (tape : ℕ → Bool) (x y z ny nz sn sd : ℕ) (hsd : 0 < sd)
    (hindex : (x*ny+y)*nz+z = i.val)
    (hxB : x.bits.length ≤ B) (hyB : y.bits.length ≤ B) (hzB : z.bits.length ≤ B)
    (hnyB : ny.bits.length ≤ B) (hnzB : nz.bits.length ≤ B)
    (hden : 0 < addressValue (dens.get i))
    (hB : Arithmetic.Bounded (Emit.data material x y z sn sd
      (addressValue (nums.get i)) (addressValue (dens.get i))) B)
    (s : Store) (hs : DenseEmit.Ready x y z sn sd s) (hd : Dense.Stored l nums dens s.val)
    (hny : Word s.val 251 ny) (hnz : Word s.val 252 nz) (h322 : Blank s.val 322) :
    ∃ cost t, cost ≤ costBound material x y z B ∧ Executes input tape (code material) cost s t ∧
      t.val.output = (Codec.rat (Emit.value material x y z sn sd
        (addressValue (nums.get i)) (addressValue (dens.get i)))).reverse ++ s.val.output ∧
      (∀ j ∈ work, Blank t.val j) ∧ Dense.Stored l nums dens t.val ∧ Frame s.val t.val := by
  have sr : Descriptors.Ready s.val := fun j hj => hs.blank j (Finset.mem_union_right _ (by simpa using hj))
  obtain ⟨fc,a,hfc,ef,hindexWord,har,fa,_⟩ := FlattenIndex.executes 240 241 242
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    input tape x y z ny nz B s hs.xWord hs.yWord hs.zWord hny hnz ⟨hxB,hyB,hzB,hnyB,hnzB⟩ sr h322
  have haReady : DenseEmit.Ready x y z sn sd a := by
    refine ⟨word_of_eq (fa.tapes 240 (by decide)) hs.xWord,
      word_of_eq (fa.tapes 241 (by decide)) hs.yWord,
      word_of_eq (fa.tapes 242 (by decide)) hs.zWord,
      word_of_eq (fa.tapes 243 (by decide)) hs.period,
      word_of_eq (fa.tapes 249 (by decide)) hs.clock,
      word_of_eq (fa.tapes 260 (by decide)) hs.sigmaNumerator,
      word_of_eq (fa.tapes 261 (by decide)) hs.sigmaDenominator,?_⟩
    intro j hj
    by_cases hj10 : j < 10
    · exact har j hj10
    · exact blank_of_eq (fa.tapes j (by
        simp only [FlattenIndex.work,Finset.mem_insert,Finset.mem_singleton]
        have hj322 : j ≠ 322 := fun he => by subst j; exact (by decide : 322 ∉ DenseEmit.work) hj
        omega)) (hs.blank j hj)
  have had : Dense.Stored l nums dens a.val :=
    ⟨BankArray.word_of_eq (fa.tapes 300 (by decide)) hd.width,
      BankArray.word_of_eq (fa.tapes 301 (by decide)) hd.clock,
      BankArray.word_of_eq (fa.tapes 320 (by decide)) hd.numBase,
      BankArray.word_of_eq (fa.tapes 321 (by decide)) hd.denBase,
      by simpa only [fa.memory] using hd.nums,by simpa only [fa.memory] using hd.dens⟩
  have hai : Word a.val 322 i.val := by simpa only [hindex] using hindexWord
  obtain ⟨ec,b,hec,ee,hbout,hbblank,hbd,hbi,fb⟩ := DenseEmit.executes l nums dens i B hl hi material hm
    input tape x y z sn sd hsd hden hB a haReady had hai
  obtain ⟨origin,hword⟩ := hbi
  obtain ⟨t,et,htt,ft⟩ := WordCall.clear 322 input tape i.val.bits origin b hword
  have keep (j : ℕ) (hj : j ≠ 322) : t.val.tapes j = b.val.tapes j := by simp [htt,hj]
  have frame : Frame s.val t.val := by
    refine ⟨ft.2.2.1.trans (fb.memory.trans fa.memory),ft.2.1.trans (fb.inputHead.trans fa.inputHead),
      ft.2.2.2.1.trans (fb.randomCursor.trans fa.randomCursor),?_⟩
    intro j hj
    have hjd : j ∉ DenseEmit.work := fun h => hj (Finset.mem_union_left _ h)
    have hj322 : j ≠ 322 := fun h => by subst j; exact hj (by simp [work])
    exact (keep j hj322).trans ((fb.tapes j hjd).trans (fa.tapes j (by
      have hj10 : 10 ≤ j := by
        have hh : j ∉ Finset.range 10 := fun hh => hjd (Finset.mem_union_right _ hh)
        simpa using hh
      simp only [FlattenIndex.work,Finset.mem_insert,Finset.mem_singleton]
      omega)))
  refine ⟨fc+(ec+(6*i.val.bits.length+4)),t,by dsimp only [costBound]; omega,ef.seq (ee.seq et),?_,?_,?_,frame⟩
  · rw [ft.2.2.2.2.1,hbout,fa.output]
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact blank_of_eq (keep j (fun he => by subst j; exact (by decide : 322 ∉ DenseEmit.work) hj)) (hbblank j hj)
    · have he : j=322 := Finset.mem_singleton.mp hj
      subst j
      exact ⟨origin+i.val.bits.length,by simp [htt]⟩
  · exact ⟨BankArray.word_of_eq (keep 300 (by decide)) hbd.width,
      BankArray.word_of_eq (keep 301 (by decide)) hbd.clock,
      BankArray.word_of_eq (keep 320 (by decide)) hbd.numBase,
      BankArray.word_of_eq (keep 321 (by decide)) hbd.denBase,
      by simpa only [ft.2.2.1] using hbd.nums,by simpa only [ft.2.2.1] using hbd.dens⟩

end Maxwell.Cost.PhysicalMaterial.CellEmit
