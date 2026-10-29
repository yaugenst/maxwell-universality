import Maxwell.Cost.PhysicalMaterial.CellEmit
import Maxwell.Cost.PhysicalEmit.Grid

namespace Maxwell.Cost.PhysicalMaterial.GridEmit
open Structured RationalAccumulator Maxwell.Spectral.Lattice
set_option maxHeartbeats 1800000

structure Ready {cells : ℕ} (l : Dense.Layout cells) (nums dens : Vector (List Bool) cells)
    (sn sd : ℕ) (s : Store) : Prop where
  period : Word s.val 243 20
  clock : Word s.val 249 16
  sigmaNumerator : Word s.val 260 sn
  sigmaDenominator : Word s.val 261 sd
  blank : ∀ j ∈ CellEmit.work, Blank s.val j
  stored : Dense.Stored l nums dens s.val

def work : Finset ℕ := CellEmit.work ∪ PhysicalEmit.loopTapes
structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  tapes : ∀ j ∉ work, t.tapes j = s.tapes j

theorem Frame.refl (s : BitRAMState) : Frame s s := ⟨rfl,rfl,rfl,fun _ _ => rfl⟩
theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.memory.trans h.memory,k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,
    fun j hj => (k.tapes j hj).trans (h.tapes j hj)⟩

def bodyBudget (material : Cell20 → ℚ) (B : ℕ) : ℕ :=
  60000*(B+2)^2+2100*(B+8)^2+770+
    10*CalibrationMatrix.MaterialTable.outputBits 15 (materialTable material)+
    Arithmetic.costBound B+100000*(7*B+26)^3+72*B+173

theorem bodyBudget_bound (material : Cell20 → ℚ) (x y z B : ℕ)
    (hx : x.bits.length ≤ B) (hy : y.bits.length ≤ B) (hz : z.bits.length ≤ B) :
    CellEmit.costBound material x y z B ≤ bodyBudget material B := by
  have hx' := Nat.pow_le_pow_left (Nat.add_le_add_right hx 8) 2
  have hy' := Nat.pow_le_pow_left (Nat.add_le_add_right hy 8) 2
  have hz' := Nat.pow_le_pow_left (Nat.add_le_add_right hz 8) 2
  dsimp [CellEmit.costBound,DenseEmit.costBound,Emit.costBound,lookupBudget,keyBudget,bodyBudget]
  nlinarith

def records {cells : ℕ} (nums dens : Vector (List Bool) cells)
    (material : Cell20 → ℚ) (ny nz sn sd x y z : ℕ) : List Bool :=
  if h : (x*ny+y)*nz+z < cells then Codec.rat (Emit.value material x y z sn sd
    (addressValue (nums.get ⟨_,h⟩)) (addressValue (dens.get ⟨_,h⟩))) else []

def code (material : Cell20 → ℚ) : Code := PhysicalEmit.gridCode (CellEmit.code material)

theorem flatIndex_lt (nx ny nz x y z : ℕ) (hx : x<nx) (hy : y<ny) (hz : z<nz) :
    (x*ny+y)*nz+z < nx*ny*nz := by
  have hxy : x*ny+y < nx*ny := by nlinarith
  nlinarith

private theorem ready_loop {cells : ℕ} (l : Dense.Layout cells)
    (nums dens : Vector (List Bool) cells) (sn sd : ℕ) (s t : Store)
    (hf : PhysicalEmit.LoopFrame PhysicalEmit.loopTapes s.val t.val) (hs : Ready l nums dens sn sd s) :
    Ready l nums dens sn sd t := by
  refine ⟨word_of_eq (hf.tapes 243 (by decide)) hs.period,
    word_of_eq (hf.tapes 249 (by decide)) hs.clock,
    word_of_eq (hf.tapes 260 (by decide)) hs.sigmaNumerator,
    word_of_eq (hf.tapes 261 (by decide)) hs.sigmaDenominator,?_,?_⟩
  · intro j hj
    exact blank_of_eq (hf.tapes j (fun hm =>
      Finset.disjoint_left.mp (by decide : Disjoint CellEmit.work PhysicalEmit.loopTapes) hj hm)) (hs.blank j hj)
  · exact ⟨BankArray.word_of_eq (hf.tapes 300 (by decide)) hs.stored.width,
      BankArray.word_of_eq (hf.tapes 301 (by decide)) hs.stored.clock,
      BankArray.word_of_eq (hf.tapes 320 (by decide)) hs.stored.numBase,
      BankArray.word_of_eq (hf.tapes 321 (by decide)) hs.stored.denBase,
      by simpa only [hf.memory] using hs.stored.nums,by simpa only [hf.memory] using hs.stored.dens⟩

/-- The actual nested cell iterator emits every material rational in the
codec's x/y/z order. Its per-cell body performs only two dense array reads. -/
theorem executes (nx ny nz B sn sd : ℕ) (l : Dense.Layout (nx*ny*nz))
    (nums dens : Vector (List Bool) (nx*ny*nz)) (hl : l.Sized B)
    (hvolume : nx*ny*nz < 2^B) (hsize : ∀ a : Fin 3, (![nx,ny,nz] a).bits.length ≤ B)
    (material : Cell20 → ℚ) (hm : ∀ c, 0 ≤ material c) (hsd : 0 < sd)
    (hden : ∀ i, 0 < addressValue (dens.get i))
    (hB : ∀ x y z (hx : x<nx) (hy : y<ny) (hz : z<nz),
      Arithmetic.Bounded (Emit.data material x y z sn sd
        (addressValue (nums.get ⟨(x*ny+y)*nz+z,flatIndex_lt nx ny nz x y z hx hy hz⟩))
        (addressValue (dens.get ⟨(x*ny+y)*nz+z,flatIndex_lt nx ny nz x y z hx hy hz⟩))) B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready l nums dens sn sd s)
    (hr : PhysicalEmit.LowerReady 0 ![nx,ny,nz] B s.val) :
    ∃ cost t, cost ≤ (nx+1)*(ny+1)*(nz+1)*(bodyBudget material B+156*B+174) ∧
      Executes input tape (code material) cost s t ∧ Ready l nums dens sn sd t ∧
      PhysicalEmit.LowerReady 0 ![nx,ny,nz] B t.val ∧ Frame s.val t.val ∧
      t.val.output = (PhysicalEmit.gridWords ![nx,ny,nz] (records nums dens material ny nz sn sd)).reverse ++ s.val.output := by
  let R : Store → Prop := fun t => Ready l nums dens sn sd t ∧ Frame s.val t.val
  have stable : ∀ u t, PhysicalEmit.LoopFrame PhysicalEmit.loopTapes u.val t.val → R u → R t := by
    intro u t hf hu
    exact ⟨ready_loop l nums dens sn sd u t hf hu.1,hu.2.trans
      ⟨hf.memory,hf.inputHead,hf.randomCursor,fun j hj => hf.tapes j (fun hh => hj (Finset.mem_union_right _ hh))⟩⟩
  have body : ∀ x y z, x<nx → y<ny → z<nz → ∀ u, R u →
      PhysicalEmit.LowerReady 3 ![nx,ny,nz] B u.val → Word u.val 240 x → Word u.val 241 y → Word u.val 242 z →
      ∃ cost t, cost ≤ bodyBudget material B ∧ Executes input tape (CellEmit.code material) cost u t ∧
        R t ∧ PhysicalEmit.Held 3 u.val t.val ∧
        t.val.output = (records nums dens material ny nz sn sd x y z).reverse ++ u.val.output := by
    intro x y z hx hy hz u hu hur hux huy huz
    let i : Fin (nx*ny*nz) := ⟨(x*ny+y)*nz+z,flatIndex_lt nx ny nz x y z hx hy hz⟩
    have hiB : i.val.bits.length ≤ B := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (i.isLt.trans hvolume)
    have hnxB : nx.bits.length ≤ B := hsize 0
    have hnyB : ny.bits.length ≤ B := hsize 1
    have hnzB : nz.bits.length ≤ B := hsize 2
    have hxB : x.bits.length ≤ B := by
      rw [Nat.size_eq_bits_len]
      exact (Nat.size_le_size hx.le).trans (by simpa only [← Nat.size_eq_bits_len] using hnxB)
    have hyB : y.bits.length ≤ B := by
      rw [Nat.size_eq_bits_len]
      exact (Nat.size_le_size hy.le).trans (by simpa only [← Nat.size_eq_bits_len] using hnyB)
    have hzB : z.bits.length ≤ B := by
      rw [Nat.size_eq_bits_len]
      exact (Nat.size_le_size hz.le).trans (by simpa only [← Nat.size_eq_bits_len] using hnzB)
    have er : DenseEmit.Ready x y z sn sd u :=
      ⟨hux,huy,huz,hu.1.period,hu.1.clock,hu.1.sigmaNumerator,hu.1.sigmaDenominator,
        fun j hj => hu.1.blank j (Finset.mem_union_left _ hj)⟩
    obtain ⟨c,t,hc,he,ho,hblank,hd,hf⟩ := CellEmit.executes l nums dens i B hl hiB material hm
      input tape x y z ny nz sn sd hsd rfl hxB hyB hzB hnyB hnzB (hden i) (hB x y z hx hy hz)
      u er hu.1.stored (hur.dimensions 1) (hur.dimensions 2) (hu.1.blank 322 (by decide))
    have htr : Ready l nums dens sn sd t :=
      ⟨word_of_eq (hf.tapes 243 (by decide)) hu.1.period,
        word_of_eq (hf.tapes 249 (by decide)) hu.1.clock,
        word_of_eq (hf.tapes 260 (by decide)) hu.1.sigmaNumerator,
        word_of_eq (hf.tapes 261 (by decide)) hu.1.sigmaDenominator,hblank,hd⟩
    refine ⟨c,t,hc.trans (bodyBudget_bound material x y z B hxB hyB hzB),he,
      ⟨htr,hu.2.trans ⟨hf.memory,hf.inputHead,hf.randomCursor,
        fun j hj => hf.tapes j (fun hh => hj (Finset.mem_union_left _ hh))⟩⟩,?_,?_⟩
    · refine ⟨?_,?_,?_⟩
      · intro a
        apply hf.tapes
        fin_cases a <;> decide
      · intro a _
        apply hf.tapes
        fin_cases a <;> decide
      · intro a _
        apply hf.tapes
        fin_cases a <;> decide
    · simpa only [records,dite_eq_left (flatIndex_lt nx ny nz x y z hx hy hz)] using ho
  obtain ⟨c,t,hc,he,hR,hr,_,ho⟩ := PhysicalEmit.grid ![nx,ny,nz] B (bodyBudget material B) hsize
    (CellEmit.code material) input tape R (records nums dens material ny nz sn sd) stable body s ⟨hs,.refl _⟩ hr
  exact ⟨c,t,hc,he,hR.1,hr,hR.2,ho⟩

end Maxwell.Cost.PhysicalMaterial.GridEmit
