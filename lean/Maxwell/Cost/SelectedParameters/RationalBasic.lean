import Maxwell.Cost.Structured.NatAssign.Bounds

/-! Exact unsigned rational arithmetic compiled to finite stored-word
assignments. Every source value is read from a physical tape. -/
namespace Maxwell.Cost.SelectedParameters.Rational
open Structured RationalAccumulator
set_option maxHeartbeats 1500000

inductive Basic where
  | add | multiply | divide
  deriving DecidableEq, Repr

def pair : Basic → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | .add,a,b,c,d => (b*c+d*a,d*b)
  | .multiply,a,b,c,d => (c*a,d*b)
  | .divide,a,b,c,d => (d*a,c*b)

def value (p : ℕ × ℕ) : ℚ := (p.1:ℚ)/p.2

def evaluate : Basic → ℚ → ℚ → ℚ
  | .add,a,b => a+b
  | .multiply,a,b => a*b
  | .divide,a,b => a/b

def Valid (op : Basic) (b c d : ℕ) : Prop :=
  0 < b ∧ 0 < d ∧ (op = .divide → 0 < c)

theorem pair_denominator (op : Basic) (a b c d : ℕ) (h : Valid op b c d) :
    0 < (pair op a b c d).2 := by
  cases op
  · exact Nat.mul_pos h.2.1 h.1
  · exact Nat.mul_pos h.2.1 h.1
  · exact Nat.mul_pos (h.2.2 rfl) h.1

theorem pair_value (op : Basic) (a b c d : ℕ) (h : Valid op b c d) :
    value (pair op a b c d) = evaluate op ((a:ℚ)/b) ((c:ℚ)/d) := by
  have hb : (b:ℚ) ≠ 0 := by exact_mod_cast h.1.ne'
  have hd : (d:ℚ) ≠ 0 := by exact_mod_cast h.2.1.ne'
  cases op with
  | add => simp only [pair,value,evaluate,Nat.cast_add,Nat.cast_mul]; field_simp; ring
  | multiply => simp only [pair,value,evaluate,Nat.cast_mul]; field_simp
  | divide =>
    have hc : (c:ℚ) ≠ 0 := by exact_mod_cast (h.2.2 rfl).ne'
    simp only [pair,value,evaluate,Nat.cast_mul]
    field_simp

theorem pair_width (op : Basic) (a b c d B : ℕ)
    (ha : a.bits.length ≤ B) (hb : b.bits.length ≤ B)
    (hc : c.bits.length ≤ B) (hd : d.bits.length ≤ B) :
    (pair op a b c d).1.bits.length ≤ 2*B+1 ∧ (pair op a b c d).2.bits.length ≤ 2*B+1 := by
  have hprod (x y : ℕ) (hx : x.bits.length ≤ B) (hy : y.bits.length ≤ B) :
      (x*y).bits.length ≤ 2*B := (bits_mul_le x y).trans (by omega)
  have hab := hprod d b hd hb
  have hac := hprod c a hc ha
  have had := hprod d a hd ha
  have hbc := hprod b c hb hc
  have hcb := hprod c b hc hb
  cases op <;> simp only [pair]
  · have hh := bits_add_le (b*c) (d*a)
    omega
  · omega
  · omega

def common : Finset ℕ := {30,31,32,33,34,35,36}
def ids (extra : Finset ℕ) : Finset ℕ := extra ∪ common

def prepare (a b c d : ℕ) : List NatAssign.Instruction :=
  [.copy a 30,.copy b 31,.copy c 32,.copy d 33]

def operations : Basic → List NatAssign.Instruction
  | .add => [.copy 30 34,.multiply 33 34,.copy 32 36,.multiply 31 36,.add 36 34,.multiply 33 31]
  | .multiply => [.copy 30 34,.multiply 32 34,.multiply 33 31]
  | .divide => [.copy 30 34,.multiply 33 34,.multiply 32 31]

def clear : List NatAssign.Instruction :=
  [.literal 30 0,.literal 31 0,.literal 32 0,.literal 33 0,.literal 34 0,.literal 35 0,.literal 36 0]

def copyOut (num den : ℕ) : List NatAssign.Instruction := [.copy 34 num,.copy 31 den]

def instructions (op : Basic) (a b c d num den : ℕ) : List NatAssign.Instruction :=
  prepare a b c d ++ operations op ++ copyOut num den ++ clear

def basicCode (op : Basic) (a b c d num den : ℕ) : Code :=
  NatAssign.code (instructions op a b c d num den)

def clean (v : ℕ → ℕ) : ℕ → ℕ := NatAssign.values clear v

def after (v : ℕ → ℕ) (num den : ℕ) (p : ℕ × ℕ) : ℕ → ℕ :=
  clean (Function.update (Function.update v num p.1) den p.2)

def workspace (num den : ℕ) : Finset ℕ := {0,1,2,3,num,den} ∪ common

@[simp] theorem clean_apply (v : ℕ → ℕ) (i : ℕ) : clean v i = if i ∈ common then 0 else v i := by
  simp only [clean,clear,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update_apply,common,Finset.mem_insert,Finset.mem_singleton]
  split_ifs <;> simp_all

@[simp] theorem after_num (v : ℕ → ℕ) (num den : ℕ) (p : ℕ × ℕ)
    (hn : 540 ≤ num) (hne : num ≠ den) : after v num den p num = p.1 := by
  have hnot : num ∉ common := by simp only [common,Finset.mem_insert,Finset.mem_singleton]; omega
  simp [after,hnot,hne]

@[simp] theorem after_den (v : ℕ → ℕ) (num den : ℕ) (p : ℕ × ℕ)
    (hd : 540 ≤ den) : after v num den p den = p.2 := by
  have hnot : den ∉ common := by simp only [common,Finset.mem_insert,Finset.mem_singleton]; omega
  simp [after,hnot]

theorem after_common (v : ℕ → ℕ) (num den : ℕ) (p : ℕ × ℕ) (i : ℕ) (hi : i ∈ common) :
    after v num den p i = 0 := by simp [after,hi]

theorem after_other (v : ℕ → ℕ) (num den : ℕ) (p : ℕ × ℕ) (i : ℕ)
    (hi : i ∉ common) (hn : i ≠ num) (hd : i ≠ den) : after v num den p i = v i := by
  simp [after,hi,hn,hd]

theorem after_width (extra : Finset ℕ) (v : ℕ → ℕ) (num den : ℕ) (p : ℕ × ℕ) (B C : ℕ)
    (hv : ∀ i ∈ ids extra, (v i).bits.length ≤ B) (hBC : B ≤ C)
    (hp : p.1.bits.length ≤ C ∧ p.2.bits.length ≤ C) :
    ∀ i ∈ ids extra, (after v num den p i).bits.length ≤ C := by
  intro i hi
  simp only [after,clean_apply,Function.update_apply]
  split_ifs <;> first | simp | exact hp.1 | exact hp.2 | exact (hv i hi).trans hBC

private theorem values_eq (op : Basic) (a b c d num den : ℕ)
    (_ha : 540 ≤ a) (hb : 540 ≤ b) (hc : 540 ≤ c) (hd : 540 ≤ d)
    (hn : 540 ≤ num) (_he : 540 ≤ den) (_hne : num ≠ den) (v : ℕ → ℕ) :
    NatAssign.values (instructions op a b c d num den) v =
      after v num den (pair op (v a) (v b) (v c) (v d)) := by
  ext i
  have b30 : b ≠ 30 := by omega
  have c30 : c ≠ 30 := by omega
  have c31 : c ≠ 31 := by omega
  have d30 : d ≠ 30 := by omega
  have d31 : d ≠ 31 := by omega
  have d32 : d ≠ 32 := by omega
  have n31 : 31 ≠ num := by omega
  by_cases hi : i ∈ common
  · simp only [common,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases op <;>
      simp [instructions,prepare,operations,copyOut,clear,after,clean,pair,NatAssign.values,
        NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]
  · have i30 : i ≠ 30 := by intro h; subst i; exact hi (by simp [common])
    have i31 : i ≠ 31 := by intro h; subst i; exact hi (by simp [common])
    have i32 : i ≠ 32 := by intro h; subst i; exact hi (by simp [common])
    have i33 : i ≠ 33 := by intro h; subst i; exact hi (by simp [common])
    have i34 : i ≠ 34 := by intro h; subst i; exact hi (by simp [common])
    have i35 : i ≠ 35 := by intro h; subst i; exact hi (by simp [common])
    have i36 : i ≠ 36 := by intro h; subst i; exact hi (by simp [common])
    cases op <;>
      simp [instructions,prepare,operations,copyOut,clear,after,clean,pair,NatAssign.values,
        NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
        Function.update_apply,b30,c30,c31,d30,d31,d32,n31,i30,i31,i32,i33,i34,i35,i36]

def basicCostBound (B : ℕ) : ℕ := 3000*8^19*(B+2)^2

/-- All inputs are copied before either output is assigned, so an output may
reuse an input port. The two output ports must remain distinct. -/
theorem basic_executes (extra : Finset ℕ) (hextra : ∀ i ∈ extra, 540 ≤ i)
    (op : Basic) (a b c d num den : ℕ)
    (ha : a ∈ extra) (hb : b ∈ extra) (hc : c ∈ extra) (hd : d ∈ extra)
    (hnum : num ∈ extra) (hden : den ∈ extra) (hne : num ≠ den)
    (v : ℕ → ℕ) (B : ℕ) (hwidth : ∀ i ∈ ids extra, (v i).bits.length ≤ B)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank (ids extra) v s.val) (hscratch : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input randomTape (basicCode op a b c d num den) cost s t ∧
      cost ≤ basicCostBound B ∧
      NatAssign.Bank (ids extra) (after v num den (pair op (v a) (v b) (v c) (v d))) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (workspace num den) s.val t.val := by
  have ha540 := hextra a ha
  have hb540 := hextra b hb
  have hc540 := hextra c hc
  have hd540 := hextra d hd
  have hn540 := hextra num hnum
  have he540 := hextra den hden
  have hids : ∀ i ∈ ids extra, 4 ≤ i := by
    intro i hi
    simp only [ids,common,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · exact (by omega : 4 ≤ 540).trans (hextra i hi)
    · omega
  have hvalid : ∀ inst ∈ instructions op a b c d num den, inst.Valid (ids extra) := by
    cases op <;> simp [instructions,prepare,operations,copyOut,clear,NatAssign.Instruction.Valid,
      ids,common,ha,hb,hc,hd,hnum,hden] <;> omega
  obtain ⟨cost,t,he,hcost,ht,hs,hf⟩ := NatAssign.executes (ids extra) hids
    (instructions op a b c d num den) hvalid v input randomTape s hbank hscratch
  have hv := values_eq op a b c d num den ha540 hb540 hc540 hd540 hn540 he540 hne v
  refine ⟨cost,t,he,?_,hv ▸ ht,hs,hf.mono ?_⟩
  · have hp := NatAssign.price_bound (ids extra) (instructions op a b c d num den) hvalid v B hwidth
      (by cases op <;> simp [instructions,prepare,operations,copyOut,clear,NatAssign.Instruction.literalWidth])
    have hlen : (instructions op a b c d num den).length ≤ 19 := by
      cases op <;> simp [instructions,prepare,operations,copyOut,clear]
    exact hcost.trans (hp.trans (by
      dsimp only [basicCostBound]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hlen))))
  · intro i hi
    cases op <;>
      simp [NatAssign.changes,instructions,prepare,operations,copyOut,clear,
        NatAssign.Instruction.target,workspace,common] at hi ⊢ <;> omega

end Maxwell.Cost.SelectedParameters.Rational
