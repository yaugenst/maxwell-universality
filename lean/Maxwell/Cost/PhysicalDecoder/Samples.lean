import Maxwell.Cost.PhysicalMaterial.Scatter.Coordinates
import Maxwell.Cost.EmitNatural
import Maxwell.Cost.EmitLiteral
import Maxwell.Cost.RationalCanonical.Transfer
import Maxwell.Composition.FiniteDefectLayout
import Maxwell.Codec

/-! Actual sample-coordinate emission. The prototype edge is fixed program
data; the selected routed anchor is read from tapes 340--342. Transverse
coordinates include the PEC index correction before serialization. -/
namespace Maxwell.Cost.PhysicalDecoder.Samples
open Structured RationalAccumulator
open Maxwell.Spectral.Lattice
open Maxwell.Composition.TranslatedStencil
open PhysicalMaterial.Scatter

def work : Finset ℕ := {0,1,2,3,292,343}

structure Frame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  tapes : ∀ i, i ∉ work → t.tapes i = s.tapes i

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,fun i hi => (k.tapes i hi).trans (h.tapes i hi)⟩

theorem Frame.of_binary {s t : BitRAMState}
    (h : BinaryPrecision.Frame (offsetWork 343) s t) : Frame s t := by
  refine ⟨h.address,h.memory,h.inputHead,h.randomCursor,?_⟩
  intro i hi
  exact h.tapes i (by simpa [work,offsetWork,PhysicalMaterial.Membership.offsetWork,
    Finset.mem_insert,Finset.mem_singleton,not_or,and_assoc,and_left_comm,and_comm] using hi)

theorem Frame.word {s t : BitRAMState} (h : Frame s t) {i n : ℕ} (hi : i ∉ work)
    (hw : Word s i n) : Word t i n := word_of_eq (h.tapes i hi) hw

def adjusted (e : Edge) (j : Fin 3) : ℤ := e.2 j - if j = e.1 then 0 else 1
def coordinate (a : Fin 3 → ℕ) (e : Edge) (j : Fin 3) : ℕ :=
  ((a j : ℤ) + adjusted e j).toNat
def record (a : Fin 3 → ℕ) (e : Edge) : List Bool :=
  Codec.nat e.1.val ++ Codec.nat (coordinate a e 0) ++
    Codec.nat (coordinate a e 1) ++ Codec.nat (coordinate a e 2)

theorem record_finiteEdge (box : Target.Box) (a : Fin 3 → ℕ) (e : Edge)
    (hi : ∀ j, 0 < (edge (fun j => (a j : ℤ)) e).2 j ∧
      (edge (fun j => (a j : ℤ)) e).2 j < (Maxwell.Green.boxSide box j : ℤ)) :
    record a e = Codec.edge (finiteEdge box (edge (fun j => (a j : ℤ)) e) hi) := by
  rcases e with ⟨dir, x⟩
  fin_cases dir <;>
    simp [record,coordinate,adjusted,finiteEdge,edge,Codec.edge,sub_eq_add_neg,add_assoc]

def indexCode (source : ℕ) (delta : ℤ) : Code :=
  .seq (offsetCode source 343 delta)
    (.seq (EmitNatural.code 343) (.call (TapeOps.clear 343)))

def coordinateCode (j : Fin 3) (delta : ℤ) : Code := indexCode (340+j.val) delta

def coordinateFactor (delta : ℤ) : ℕ := offsetFactor delta + 26*delta.natAbs.bits.length+80

theorem coordinate_length (n : ℕ) (delta : ℤ) :
    ((n : ℤ)+delta).toNat.bits.length ≤ n.bits.length+delta.natAbs.bits.length+1 := by
  have hle : ((n : ℤ)+delta).toNat ≤ n+delta.natAbs := by
    cases delta <;> simp
    omega
  have h := Nat.size_le_size hle
  have hs := IndexedAddress.sum_length_le n.bits delta.natAbs.bits
  simp only [addressValue_bits] at hs
  have h' : ((n : ℤ)+delta).toNat.bits.length ≤ (n+delta.natAbs).bits.length := by
    simpa only [Nat.size_eq_bits_len] using h
  exact h'.trans hs

set_option maxRecDepth 8192 in
theorem index_executes (source : ℕ) (hsource : 10 ≤ source) (hne : source ≠ 343)
    (delta : ℤ) (n B : ℕ)
    (hn : n.bits.length ≤ B) (hroom : 0 ≤ (n : ℤ)+delta)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : Word s.val source n) (hz : Blank s.val 343)
    (h292 : Blank s.val 292) (hr : Ready s.val) :
    ∃ cost t, cost ≤ coordinateFactor delta*(B+1) ∧
      Executes input tape (indexCode source delta) cost s t ∧
      t.val.output = (Codec.nat ((n : ℤ)+delta).toNat).reverse ++ s.val.output ∧
      Blank t.val 343 ∧ Blank t.val 292 ∧ Ready t.val ∧ Frame s.val t.val := by
  obtain ⟨c,a,hc,ea,aw,a292,ar,af⟩ := offset_executes source 343 hsource
    (by decide) hne (by decide) delta n B hn hroom input tape s hw hz h292 hr
  obtain ⟨origin,aho⟩ := aw
  obtain ⟨b,eb,bo,bf⟩ := EmitNatural.executes 343 ((n : ℤ)+delta).toNat origin input tape a aho
  obtain ⟨t,et,tz,tf⟩ := RationalCanonical.clear_word 343 ((n : ℤ)+delta).toNat input tape b
    (word_of_eq (congrFun bf.2.2.2.2 343) ⟨origin,aho⟩)
  have fa : Frame s.val a.val := Frame.of_binary af
  have fb : Frame a.val b.val := ⟨bf.1,bf.2.2.1,bf.2.1,bf.2.2.2.1,
    fun i _ => congrFun bf.2.2.2.2 i⟩
  have ft : Frame b.val t.val := by
    refine ⟨tf.1,tf.2.2.1,tf.2.1,tf.2.2.2.1,?_⟩
    intro i hi
    have hn : i ≠ 343 := by simp only [work,Finset.mem_insert,Finset.mem_singleton,not_or] at hi; tauto
    exact tf.2.2.2.2.2.1 i hn hn
  refine ⟨c+((20*((n:ℤ)+delta).toNat.bits.length+24)+
    (6*((n:ℤ)+delta).toNat.bits.length+4)),t,?_,ea.seq (eb.seq et),?_,
    (zero_word_iff_blank _ _).mp tz,?_,?_,fa.trans (fb.trans ft)⟩
  · have hl := coordinate_length n delta
    unfold coordinateFactor
    nlinarith
  · rw [tf.2.2.2.2.1,bo,af.output]
  · exact blank_of_eq (tf.2.2.2.2.2.1 292 (by decide) (by decide))
      (blank_of_eq (congrFun bf.2.2.2.2 292) a292)
  · intro i hi
    exact blank_of_eq (tf.2.2.2.2.2.1 i (by omega) (by omega))
      (blank_of_eq (congrFun bf.2.2.2.2 i) (ar i hi))

theorem coordinate_executes (j : Fin 3) (delta : ℤ) (n B : ℕ)
    (hn : n.bits.length ≤ B) (hroom : 0 ≤ (n : ℤ)+delta)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : Word s.val (340+j.val) n) (hz : Blank s.val 343)
    (h292 : Blank s.val 292) (hr : Ready s.val) :
    ∃ cost t, cost ≤ coordinateFactor delta*(B+1) ∧
      Executes input tape (coordinateCode j delta) cost s t ∧
      t.val.output = (Codec.nat ((n : ℤ)+delta).toNat).reverse ++ s.val.output ∧
      Blank t.val 343 ∧ Blank t.val 292 ∧ Ready t.val ∧ Frame s.val t.val :=
  index_executes (340+j.val) (by omega) (by have := j.isLt; omega)
    delta n B hn hroom input tape s hw hz h292 hr

def sampleCode (e : Edge) : Code :=
  .seq (EmitLiteral.code 29 (Codec.nat e.1.val))
    (.seq (coordinateCode 0 (adjusted e 0))
      (.seq (coordinateCode 1 (adjusted e 1)) (coordinateCode 2 (adjusted e 2))))

def sampleFactor (e : Edge) : ℕ := 4*(Codec.nat e.1.val).length+1+
  coordinateFactor (adjusted e 0)+coordinateFactor (adjusted e 1)+coordinateFactor (adjusted e 2)

theorem sample_room (a : Fin 3 → ℕ) (e : Edge)
    (hi : ∀ j, 0 < (a j : ℤ)+e.2 j) : ∀ j, 0 ≤ (a j : ℤ)+adjusted e j := by
  intro j
  have hj := hi j
  unfold adjusted
  split_ifs <;> omega

set_option maxRecDepth 8192 in
theorem sample_executes (a : Fin 3 → ℕ) (e : Edge) (B : ℕ)
    (hb : ∀ j, (a j).bits.length ≤ B) (hi : ∀ j, 0 < (a j : ℤ)+e.2 j)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : ∀ j, Word s.val (340+j.val) (a j)) (hz : Blank s.val 343)
    (h292 : Blank s.val 292) (hr : Ready s.val) :
    ∃ cost t, cost ≤ sampleFactor e*(B+1) ∧ Executes input tape (sampleCode e) cost s t ∧
      t.val.output = (record a e).reverse ++ s.val.output ∧
      Blank t.val 343 ∧ Blank t.val 292 ∧ Ready t.val ∧ Frame s.val t.val := by
  let start := EmitLiteral.finish 29 (Codec.nat e.1.val) s
  have es := EmitLiteral.executes 29 (Codec.nat e.1.val) input tape s
  have fs := EmitLiteral.finish_frame 29 (Codec.nat e.1.val) s
  have os := EmitLiteral.finish_output 29 (Codec.nat e.1.val) s
  have hs : Frame s.val start.val := ⟨fs.1,fs.2.2.1,fs.2.1,fs.2.2.2.1,
    fun j _ => congrFun fs.2.2.2.2.1 j⟩
  obtain ⟨c0,u0,hc0,e0,o0,z0,w0,r0,f0⟩ := coordinate_executes 0 (adjusted e 0) (a 0) B
    (hb 0) (sample_room a e hi 0) input tape start
    (word_of_eq (congrFun fs.2.2.2.2.1 _) (hw 0))
    (blank_of_eq (congrFun fs.2.2.2.2.1 _) hz)
    (blank_of_eq (congrFun fs.2.2.2.2.1 _) h292)
    (fun j hj => blank_of_eq (congrFun fs.2.2.2.2.1 j) (hr j hj))
  obtain ⟨c1,u1,hc1,e1,o1,z1,w1,r1,f1⟩ := coordinate_executes 1 (adjusted e 1) (a 1) B
    (hb 1) (sample_room a e hi 1) input tape u0
    ((hs.trans f0).word (by decide) (hw 1)) z0 w0 r0
  obtain ⟨c2,t,hc2,e2,o2,z2,w2,r2,f2⟩ := coordinate_executes 2 (adjusted e 2) (a 2) B
    (hb 2) (sample_room a e hi 2) input tape u1
    (((hs.trans f0).trans f1).word (by decide) (hw 2)) z1 w1 r1
  refine ⟨(4*(Codec.nat e.1.val).length+1)+(c0+(c1+c2)),t,?_,
    es.seq (e0.seq (e1.seq e2)),?_,z2,w2,r2,hs.trans (f0.trans (f1.trans f2))⟩
  · unfold sampleFactor
    nlinarith
  · rw [o2,o1,o0,os]
    simp only [record,coordinate,List.reverse_append,List.append_assoc]

/-- A fixed platform prototype is compiled once; every copy reads its own
runtime anchor. No instance-dependent coordinate list is stored in the code. -/
def samplesCode : List Edge → Code
  | [] => .skip
  | e :: es => .seq (sampleCode e) (samplesCode es)

def samplesFactor (es : List Edge) : ℕ := (es.map sampleFactor).sum+1

theorem samples_executes (a : Fin 3 → ℕ) (es : List Edge) (B : ℕ)
    (hb : ∀ j, (a j).bits.length ≤ B)
    (hi : ∀ e ∈ es, ∀ j, 0 < (a j : ℤ)+e.2 j)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : ∀ j, Word s.val (340+j.val) (a j)) (hz : Blank s.val 343)
    (h292 : Blank s.val 292) (hr : Ready s.val) :
    ∃ cost t, cost ≤ samplesFactor es*(B+1) ∧ Executes input tape (samplesCode es) cost s t ∧
      t.val.output = (es.flatMap (record a)).reverse ++ s.val.output ∧
      Blank t.val 343 ∧ Blank t.val 292 ∧ Ready t.val ∧ Frame s.val t.val := by
  induction es generalizing s with
  | nil =>
      exact ⟨1,s,by simp [samplesFactor],Executes.skip s,by simp,hz,h292,hr,
        ⟨rfl,rfl,rfl,rfl,fun _ _ => rfl⟩⟩
  | cons e es ih =>
      obtain ⟨c,u,hc,eu,ou,zu,wu,ru,fu⟩ := sample_executes a e B hb
        (hi e (by simp)) input tape s hw hz h292 hr
      obtain ⟨d,t,hd,et,ot,zt,wt,rt,ft⟩ := ih
        (fun e he => hi e (by simp [he])) u
        (fun j => fu.word (by have := j.isLt; simp only [work,Finset.mem_insert,
          Finset.mem_singleton,not_or]; omega) (hw j)) zu wu ru
      refine ⟨c+d,t,?_,eu.seq et,?_,zt,wt,rt,fu.trans ft⟩
      · simp only [samplesFactor,List.map_cons,List.sum_cons] at hd ⊢
        nlinarith
      · rw [ot,ou]
        simp only [List.flatMap_cons,List.reverse_append,List.append_assoc]

end Maxwell.Cost.PhysicalDecoder.Samples
