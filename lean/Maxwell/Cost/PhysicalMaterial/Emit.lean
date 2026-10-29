import Maxwell.Cost.PhysicalMaterial.Lookup
import Maxwell.Cost.PhysicalMaterial.Arithmetic
import Maxwell.Cost.RationalCanonical.Correctness

/-! Reusable per-cell material emission from actual coordinate, sigma, and
selected-strength words. Lookup, arithmetic, reduction, serialization, and
cleanup are all finite charged machine programs. -/
namespace Maxwell.Cost.PhysicalMaterial.Emit
open Structured RationalAccumulator Maxwell.Spectral.Lattice
set_option maxHeartbeats 1000000

def scratch : Finset ℕ := ArithmeticBank.work ∪
  {4,220,221,222,223,228,229,230,231,244,247,248,270,271}
def work : Finset ℕ := scratch ∪ {272,273}

structure Frame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  tapes : ∀ i ∉ work, t.tapes i = s.tapes i

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.address.trans h.address, k.memory.trans h.memory, k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor, fun i hi => (k.tapes i hi).trans (h.tapes i hi)⟩

private theorem Frame.ofBinary {changed : Finset ℕ} {s t : BitRAMState}
    (h : BinaryPrecision.Frame changed s t) (hc : changed ⊆ work) : Frame s t :=
  ⟨h.address,h.memory,h.inputHead,h.randomCursor,fun i hi => h.tapes i (fun hh => hi (hc hh))⟩

private theorem Frame.ofCanonical {s t : BitRAMState} (h : RationalCanonical.EmitFrame s t) :
    Frame s t := by
  refine ⟨h.address,h.memory,h.inputHead,h.randomCursor,?_⟩
  intro i hi
  exact h.tapes i (fun hh => hi ((by decide :
    ({0,1,2,3,4,220,221,222,223,228,229,230,231}:Finset ℕ) ⊆ work) hh))

structure Ready (x y z sigmaNum sigmaDen strengthNum strengthDen : ℕ) (s : Store) : Prop where
  xWord : Word s.val 240 x
  yWord : Word s.val 241 y
  zWord : Word s.val 242 z
  period : Word s.val 243 20
  clock : Word s.val 249 16
  sigmaNumerator : Word s.val 260 sigmaNum
  sigmaDenominator : Word s.val 261 sigmaDen
  strengthNumerator : Word s.val 272 strengthNum
  strengthDenominator : Word s.val 273 strengthDen
  blank : ∀ i ∈ scratch, Blank s.val i

def cell (x y z : ℕ) : Cell20 := ![(x:ZMod 20),(y:ZMod 20),(z:ZMod 20)]

def data (material : Cell20 → ℚ) (x y z sn sd vn vd : ℕ) : Arithmetic.Data :=
  ⟨(material (cell x y z)).num.toNat,(material (cell x y z)).den,sn,sd,vn,vd⟩

def value (material : Cell20 → ℚ) (x y z sn sd vn vd : ℕ) : ℚ :=
  material (cell x y z)+64*((sn:ℚ)/sd)+64*((vn:ℚ)/vd)

private theorem data_value (material : Cell20 → ℚ) (hm : ∀ c, 0 ≤ material c)
    (x y z sn sd vn vd : ℕ) : Arithmetic.value (data material x y z sn sd vn vd) =
      value material x y z sn sd vn vd := by
  have hn : 0 ≤ (material (cell x y z)).num := Rat.num_nonneg.mpr (hm _)
  simp only [Arithmetic.value,data,value]
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hn, Rat.num_div_den]

private def clearList : List ℕ → Code
  | [] => .skip
  | i::rest => .seq (.call (TapeOps.clear i)) (clearList rest)

private theorem clear_list (indices : List ℕ) (hnodup : indices.Nodup)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (s : Store)
    (hwords : ∀ i ∈ indices, Word s.val i (v i)) :
    ∃ t, Executes input tape (clearList indices)
      (6*(indices.map (fun i => (v i).bits.length)).sum+4*indices.length+1) s t ∧
      (∀ i ∈ indices, Blank t.val i) ∧ BinaryPrecision.Frame indices.toFinset s.val t.val := by
  induction indices generalizing s with
  | nil => exact ⟨s,.skip s,by simp,BinaryPrecision.Frame.refl _ _⟩
  | cons i rest ih =>
    obtain ⟨origin,ho⟩ := hwords i (by simp)
    obtain ⟨a,ea,hta,fa⟩ := WordCall.clear i input tape (v i).bits origin s ho
    have keep (j : ℕ) (hj : j ≠ i) : a.val.tapes j = s.val.tapes j := by simp [hta,hj]
    have hrest : ∀ j ∈ rest, Word a.val j (v j) := by
      intro j hj
      exact word_of_eq (keep j (by intro he; subst j; exact (List.nodup_cons.mp hnodup).1 hj))
        (hwords j (by simp [hj]))
    obtain ⟨t,et,hblank,ft⟩ := ih hnodup.of_cons a hrest
    have fclear : BinaryPrecision.Frame {i} s.val a.val :=
      ⟨fa.1,fa.2.1,fa.2.2.1,fa.2.2.2.1,fa.2.2.2.2.1,
        fun j hj => keep j (by simpa using hj)⟩
    refine ⟨t,?_,?_,(fclear.mono (by simp)).trans (ft.mono (by simp))⟩
    · convert ea.seq et using 1 <;> first | rfl | simp only [List.map_cons,List.sum_cons,List.length_cons]; omega
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact blank_of_eq (ft.tapes j (by simpa using (List.nodup_cons.mp hnodup).1))
          ⟨origin+(v j).bits.length,by simp [hta]⟩
      · exact hblank j hj

private def cleanupIndices : List ℕ := [270,271,272,273,228,229]

def cleanupCode : Code := clearList cleanupIndices

def code (material : Cell20 → ℚ) : Code :=
  .seq (lookupCode material) (.seq Arithmetic.code (.seq RationalCanonical.code cleanupCode))

def costBound (material : Cell20 → ℚ) (x y z B : ℕ) : ℕ :=
  lookupBudget material x y z + Arithmetic.costBound B +
    100000*(7*B+26)^3+66*B+169

/-- One cell is looked up from its stored coordinates and serialized exactly;
all per-cell work, including the selected strength, is erased for reuse. -/
theorem executes (material : Cell20 → ℚ) (hm : ∀ c, 0 ≤ material c)
    (input : List Bool) (tape : ℕ → Bool) (x y z sn sd vn vd B : ℕ)
    (hsd : 0 < sd) (hvd : 0 < vd)
    (hB : Arithmetic.Bounded (data material x y z sn sd vn vd) B)
    (s : Store) (hs : Ready x y z sn sd vn vd s) :
    ∃ cost t, cost ≤ costBound material x y z B ∧ Executes input tape (code material) cost s t ∧
      t.val.output = (Codec.rat (value material x y z sn sd vn vd)).reverse ++ s.val.output ∧
      (∀ i ∈ work, Blank t.val i) ∧ Frame s.val t.val := by
  let d := data material x y z sn sd vn vd
  have valid : Arithmetic.Valid d := ⟨(material (cell x y z)).pos,hsd,hvd⟩
  obtain ⟨c1,a,hc1,e1,ha270,ha271,ha0,ha244,ha247,ha248,f1⟩ :=
    lookup_executes material input tape x y z s hs.xWord hs.yWord hs.zWord hs.period hs.clock
      (fun i hi => hs.blank i (by simp [scratch,ArithmeticBank.work]; omega))
      (hs.blank 244 (by decide)) (hs.blank 247 (by decide)) (hs.blank 248 (by decide))
      (hs.blank 270 (by decide)) (hs.blank 271 (by decide))
  have ar : Arithmetic.Ready d a := by
    refine ⟨ha270,ha271,word_of_eq (f1.tapes 260 (by decide)) hs.sigmaNumerator,
      word_of_eq (f1.tapes 261 (by decide)) hs.sigmaDenominator,
      word_of_eq (f1.tapes 272 (by decide)) hs.strengthNumerator,
      word_of_eq (f1.tapes 273 (by decide)) hs.strengthDenominator,?_⟩
    intro i hi
    by_cases hi5 : i < 5
    · exact ha0 i hi5
    · apply blank_of_eq (f1.tapes i ?_) (hs.blank i ?_)
      · simp only [lookupWork,keyWork,Arithmetic.work,ArithmeticBank.work,
          Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢
        omega
      · exact (by decide : Arithmetic.work ∪ {4} ⊆ scratch) hi
  obtain ⟨c2,b,e2,hc2,hb228,hb229,hsgn,hbblank,f2⟩ := Arithmetic.executes input tape d B valid hB a ar
  have extraBlank (i : ℕ) (hi : i ∈ ({220,221,222,223,230,231}:Finset ℕ)) : Blank b.val i := by
    apply blank_of_eq ((f2.tapes i ?_).trans (f1.tapes i ?_))
      (hs.blank i ((by decide : ({220,221,222,223,230,231}:Finset ℕ) ⊆ scratch) hi))
    all_goals simp only [Arithmetic.work,ArithmeticBank.work,lookupWork,keyWork,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi ⊢; omega
  have nr : RationalCanonical.NormalizeReady b.val (Arithmetic.numerator d) (Arithmetic.denominator d) :=
    ⟨hb228,hb229,⟨(zero_word_iff_blank _ _).mpr (extraBlank 220 (by simp)),
      (zero_word_iff_blank _ _).mpr (extraBlank 221 (by simp)),extraBlank 222 (by simp),
      extraBlank 223 (by simp),fun i hi => hbblank i (by simp [ArithmeticBank.work]; omega)⟩,
      extraBlank 230 (by simp),extraBlank 231 (by simp)⟩
  obtain ⟨c3,c,hc3,e3,hout,nc,f3⟩ := RationalCanonical.executes input tape false
    (Arithmetic.numerator d) (Arithmetic.denominator d) (Arithmetic.denominator_pos d valid) b nr hsgn
  have hvalue : RationalCanonical.value false (Arithmetic.numerator d) (Arithmetic.denominator d) =
      value material x y z sn sd vn vd := by
    simpa only [RationalCanonical.value,Bool.false_eq_true,ite_false] using
      (Arithmetic.fraction_value d valid).trans (data_value material hm x y z sn sd vn vd)
  have keepInput (i : ℕ) (hi : i ∈ ({270,271,272,273}:Finset ℕ)) : c.val.tapes i = a.val.tapes i := by
    exact (f3.tapes i (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢; omega)).trans
      (f2.tapes i (by simp only [Arithmetic.work,ArithmeticBank.work,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi ⊢; omega))
  let vals : ℕ → ℕ := fun i => if i=270 then d.baseNum else if i=271 then d.baseDen else
    if i=272 then vn else if i=273 then vd else if i=228 then Arithmetic.numerator d else Arithmetic.denominator d
  have words : ∀ i ∈ cleanupIndices, Word c.val i (vals i) := by
    intro i hi
    simp only [cleanupIndices,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact word_of_eq (keepInput 270 (by simp)) ha270
    · exact word_of_eq (keepInput 271 (by simp)) ha271
    · exact word_of_eq (keepInput 272 (by simp)) ar.strengthNum
    · exact word_of_eq (keepInput 273 (by simp)) ar.strengthDen
    · exact nc.numerator
    · exact nc.denominator
  obtain ⟨t,e4,htblank,f4⟩ := clear_list cleanupIndices (by decide) input tape vals c words
  have outsideCleanup (i : ℕ) (hi : i ∉ cleanupIndices.toFinset) : t.val.tapes i = c.val.tapes i :=
    f4.tapes i hi
  have cleaned (i : ℕ) (hi : i ∈ work) : Blank t.val i := by
    by_cases hc : i ∈ cleanupIndices
    · exact htblank i hc
    · apply blank_of_eq (outsideCleanup i (by simpa using hc))
      by_cases hi5 : i < 5
      · exact nc.work.scratch i hi5
      by_cases hcanon : i ∈ ({220,221,222,223,230,231}:Finset ℕ)
      · simp only [Finset.mem_insert,Finset.mem_singleton] at hcanon
        rcases hcanon with rfl | rfl | rfl | rfl | rfl | rfl
        · exact (zero_word_iff_blank _ _).mp nc.work.first
        · exact (zero_word_iff_blank _ _).mp nc.work.second
        · exact nc.work.quotient
        · exact nc.work.remainder
        · exact nc.outputNumerator
        · exact nc.outputDenominator
      have keepc : c.val.tapes i = b.val.tapes i := f3.tapes i (by
        simp only [cleanupIndices,List.mem_cons,List.not_mem_nil,or_false] at hc
        simp only [Finset.mem_insert,Finset.mem_singleton] at hcanon ⊢
        omega)
      apply blank_of_eq keepc
      by_cases hbank : i ∈ ArithmeticBank.work ∪ {4}
      · exact hbblank i hbank
      have keymem : i = 244 ∨ i = 247 ∨ i = 248 := by
        simp only [work,scratch,ArithmeticBank.work,cleanupIndices,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton,List.mem_cons,List.not_mem_nil,or_false] at hi hc hbank hcanon
        omega
      apply blank_of_eq (f2.tapes i (by
        simp only [Arithmetic.work,ArithmeticBank.work,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton]
        omega))
      rcases keymem with rfl | rfl | rfl
      · exact ha244
      · exact ha247
      · exact ha248
  refine ⟨_,t,?_,e1.seq (e2.seq (e3.seq e4)),?_,cleaned,
    (((Frame.ofBinary f1 (by decide)).trans (Frame.ofBinary f2 (by decide))).trans
      (Frame.ofCanonical f3)).trans (Frame.ofBinary f4 (by decide))⟩
  · have hn := Arithmetic.numerator_bits d B hB
    have hd := Arithmetic.denominator_bits d B hB
    have hcanonical := RationalCanonical.costBound_polynomial (Arithmetic.numerator d) (Arithmetic.denominator d)
    have hwidth : (Arithmetic.numerator d).size+(Arithmetic.denominator d).size+2 ≤ 7*B+26 := by
      rw [← Nat.size_eq_bits_len,← Nat.size_eq_bits_len]
      omega
    have hcc : c3 ≤ 100000*(7*B+26)^3 := hc3.trans
      (hcanonical.trans (Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left hwidth 3)))
    have hbN := hB.1
    have hbD := hB.2.1
    change d.baseNum.bits.length ≤ B at hbN
    change d.baseDen.bits.length ≤ B at hbD
    have hvN : vn.bits.length ≤ B := hB.2.2.2.2.1
    have hvD : vd.bits.length ≤ B := hB.2.2.2.2.2
    simp only [cleanupIndices,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    norm_num [vals]
    dsimp [costBound]
    omega
  · rw [f4.output,hout,hvalue,f2.output,f1.output]

end Maxwell.Cost.PhysicalMaterial.Emit
