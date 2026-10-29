import Maxwell.Cost.PhysicalDecoder.Product
import Maxwell.Cost.RationalCanonical.Correctness
import Maxwell.Cost.PhysicalMaterial.ArithmeticBank

namespace Maxwell.Cost.PhysicalDecoder.Arithmetic
open Structured RationalAccumulator

/-- Mode numerator/denominator, selected strength numerator/denominator,
original source scale numerator/denominator, and matrix scale numerator/denominator. -/
abbrev Data := Fin 8 → ℕ

def values (x : Data) : ℕ → ℕ
  | 350 => x 0 | 351 => x 1 | 352 => x 2 | 353 => x 3
  | 354 => x 4 | 355 => x 5 | 356 => x 6 | 357 => x 7 | _ => 0

def numerator (x : Data) : ℕ := (x 2*(x 4*x 7))*x 0
def denominator (x : Data) : ℕ := (x 3*(x 5*x 6))*x 1
def Valid (x : Data) : Prop := 0 < x 1 ∧ 0 < x 3 ∧ 0 < x 5 ∧ 0 < x 6
def Bounded (x : Data) (B : ℕ) : Prop := ∀ i,(x i).bits.length ≤ B
def fraction (x : Data) (negative : Bool) : ℚ :=
  ((x 4 : ℚ)/x 5)/((x 6 : ℚ)/x 7)*((x 2 : ℚ)/x 3)*
    RationalCanonical.value negative (x 0) (x 1)

theorem denominator_pos (x : Data) (h : Valid x) : 0 < denominator x :=
  Nat.mul_pos (Nat.mul_pos h.2.1 (Nat.mul_pos h.2.2.1 h.2.2.2)) h.1

theorem fraction_value (x : Data) (negative : Bool) :
    RationalCanonical.value negative (numerator x) (denominator x) = fraction x negative := by
  cases negative <;> simp [RationalCanonical.value,numerator,denominator,fraction,div_eq_mul_inv,
    mul_comm,mul_left_comm,mul_assoc]

theorem numerator_bits (x : Data) (B : ℕ) (h : Bounded x B) :
    (numerator x).bits.length ≤ 4*B := by
  have h1 := bits_mul_le (x 4) (x 7)
  have h2 := bits_mul_le (x 2) (x 4*x 7)
  have h3 := bits_mul_le (x 2*(x 4*x 7)) (x 0)
  have := h 0; have := h 2; have := h 4; have := h 7
  unfold numerator
  omega

theorem denominator_bits (x : Data) (B : ℕ) (h : Bounded x B) :
    (denominator x).bits.length ≤ 4*B := by
  have h1 := bits_mul_le (x 5) (x 6)
  have h2 := bits_mul_le (x 3) (x 5*x 6)
  have h3 := bits_mul_le (x 3*(x 5*x 6)) (x 1)
  have := h 1; have := h 3; have := h 5; have := h 6
  unfold denominator
  omega

def work : Finset ℕ := PhysicalMaterial.ArithmeticBank.work ∪ {4,228,229}
abbrev Frame := BinaryPrecision.Frame work

structure Ready (x : Data) (s : Store) : Prop where
  words : ∀ i,Word s.val (350+i.val) (x i)
  blank : ∀ i ∈ work,Blank s.val i

private theorem frame_bank {s t : BitRAMState} (h : RationalAccumulator.Frame s t) : Frame s t :=
  (PhysicalMaterial.ArithmeticBank.frame_bank h).mono (by intro i hi; exact Finset.mem_union_left _ hi)

private theorem frame_move {source target : ℕ} {s t : BitRAMState}
    (h : WordTransfer.Frame source target s t) (hs : source ∈ work) (ht : target ∈ work) : Frame s t := by
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,?_⟩
  intro i hi
  exact h.2.2.2.2.2.1 i (by intro he; subst i; exact hi hs) (by intro he; subst i; exact hi ht)

def code : Code := .seq (Product.code 350 30 [352,354,357])
  (.seq (Product.code 351 32 [353,355,356])
    (.seq (.call (WordTransfer.move 30 228)) (.call (WordTransfer.move 32 229))))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem executes (x : Data) (B : ℕ) (hB : Bounded x B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready x s) :
    ∃ cost t, cost ≤ 20000*(4*B+3)^2 ∧ Executes input tape code cost s t ∧
      Word t.val 228 (numerator x) ∧ Word t.val 229 (denominator x) ∧
      (∀ i ∈ PhysicalMaterial.ArithmeticBank.work ∪ {4},Blank t.val i) ∧
      t.val.registers 23=s.val.registers 23 ∧ Frame s.val t.val := by
  have hbank : Bank s.val (fun _ => 0) := by
    intro i hi hi'
    apply (zero_word_iff_blank _ _).mpr
    apply hs.blank
    interval_cases i <;> decide
  have hr : Scratch s.val 0 := ⟨hs.blank 0 (by decide),
    (zero_word_iff_blank _ _).mpr (hs.blank 1 (by decide)),hs.blank 2 (by decide),hs.blank 3 (by decide)⟩
  have hwords (i : ℕ) (hi : i ∈ [350,351,352,353,354,355,356,357]) : Word s.val i (values x i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hs.words 0
    · exact hs.words 1
    · exact hs.words 2
    · exact hs.words 3
    · exact hs.words 4
    · exact hs.words 5
    · exact hs.words 6
    · exact hs.words 7
  have hnwidth : Product.bitSum [350,352,354,357] (values x) ≤ 4*B := by
    simp only [Product.bitSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,values]
    have := hB 0; have := hB 2; have := hB 4; have := hB 7
    omega
  have hdwidth : Product.bitSum [351,353,355,356] (values x) ≤ 4*B := by
    simp only [Product.bitSum,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,values]
    have := hB 1; have := hB 3; have := hB 5; have := hB 6
    omega
  obtain ⟨c1,a,hc1,e1,b1,r1,f1⟩ := Product.executes 350 30 [352,354,357] (by decide)
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega)
    (by decide) (by decide) (values x) (fun _ => 0) (4*B) hnwidth input tape s
    (fun i hi => hwords i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto)) hbank rfl hr
  have b1' : Bank a.val (Function.update (fun _ => 0) 30 (numerator x)) := by
    simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,values,mul_one,numerator] using b1
  obtain ⟨c2,b,hc2,e2,b2,r2,f2⟩ := Product.executes 351 32 [353,355,356] (by decide)
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega)
    (by decide) (by decide) (values x) _ (4*B) hdwidth input tape a
    (fun i hi => word_of_eq (f1.2.2.2.2.2.1 i
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega)
      (Or.inr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega))) (hwords i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto)))
    b1' (by simp) r1
  let v := Function.update (Function.update (fun _ => 0) 30 (numerator x)) 32 (denominator x)
  have b2' : Bank b.val v := by
    simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,values,mul_one,denominator,v] using b2
  have fb : Frame s.val b.val := frame_bank (f1.trans f2)
  obtain ⟨c,e3,c30,c228,f3⟩ := RationalCanonical.move_word 30 228 (numerator x) (by decide)
    input tape b (by simpa [v] using b2' 30 (by decide) (by decide))
    ((zero_word_iff_blank _ _).mpr (blank_of_eq ((f1.trans f2).2.2.2.2.2.1 228 (by decide) (Or.inr (by decide))) (hs.blank 228 (by decide))))
  obtain ⟨t,e4,t32,t229,f4⟩ := RationalCanonical.move_word 32 229 (denominator x) (by decide)
    input tape c (word_of_eq (f3.2.2.2.2.2.1 32 (by decide) (by decide))
      (by simpa [v] using b2' 32 (by decide) (by decide)))
    ((zero_word_iff_blank _ _).mpr (blank_of_eq (f3.2.2.2.2.2.1 229 (by decide) (by decide))
      (blank_of_eq ((f1.trans f2).2.2.2.2.2.1 229 (by decide) (Or.inr (by decide))) (hs.blank 229 (by decide)))))
  refine ⟨c1+(c2+((12*(numerator x).bits.length+11)+(12*(denominator x).bits.length+11))),t,?_,
    e1.seq (e2.seq (e3.seq e4)),word_of_eq (f4.2.2.2.2.2.1 228 (by decide) (by decide)) c228,
    t229,?_,?_,fb.trans ((frame_move f3 (by decide) (by decide)).trans
      (frame_move f4 (by decide) (by decide)))⟩
  · have hn := numerator_bits x B hB
    have hd := denominator_bits x B hB
    norm_num only [List.length_cons,List.length_nil] at hc1 hc2
    nlinarith
  · intro i hi
    have keep (hi30 : i ≠ 30) (hi32 : i ≠ 32) : t.val.tapes i=b.val.tapes i := by
      have hi228 : i ≠ 228 := by intro he; subst i; norm_num [PhysicalMaterial.ArithmeticBank.work] at hi
      have hi229 : i ≠ 229 := by intro he; subst i; norm_num [PhysicalMaterial.ArithmeticBank.work] at hi
      exact (f4.2.2.2.2.2.1 i hi32 hi229).trans (f3.2.2.2.2.2.1 i hi30 hi228)
    by_cases hi30 : i=30
    · subst i
      exact blank_of_eq (f4.2.2.2.2.2.1 30 (by decide) (by decide)) ((zero_word_iff_blank _ _).mp c30)
    by_cases hi32 : i=32
    · subst i
      exact (zero_word_iff_blank _ _).mp t32
    apply blank_of_eq (keep hi30 hi32)
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ (30 ≤ i ∧ i ≤ 36) := by
      simp only [PhysicalMaterial.ArithmeticBank.work,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton] at hi
      omega
    rcases hi' with rfl|rfl|rfl|rfl|rfl|hi'
    · exact r2.1
    · exact (zero_word_iff_blank _ _).mp r2.2.1
    · exact r2.2.2.1
    · exact r2.2.2.2
    · exact blank_of_eq ((f1.trans f2).2.2.2.2.2.1 4 (by decide) (Or.inl (by decide))) (hs.blank 4 (by decide))
    · apply (zero_word_iff_blank _ _).mp
      simpa [v,hi30,hi32] using b2' i hi'.1 hi'.2
  · exact (f4.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans
      ((f3.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans
      ((f1.trans f2).2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide) (by decide)))

end Maxwell.Cost.PhysicalDecoder.Arithmetic
