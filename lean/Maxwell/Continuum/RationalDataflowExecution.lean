import Maxwell.Continuum.RationalDataflowBinaryValues

/-! Checked execution and charged Boolean cost of the shared rational arithmetic stages. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def stageCost (B : ℕ) : ℕ := 2^96*(B+2)^2

theorem changes_subset (S : Finset ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀ a∈ins, a.Valid (ids S)) : NatAssign.changes ins⊆workspace S := by
  intro i hi
  rcases Finset.mem_union.mp hi with hs | ht
  · exact Finset.mem_union_left _ hs
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    apply Finset.mem_union_right
    have hh := hv a ha
    cases a <;> first | exact hh | exact hh.2.1

theorem fixedStage_executes (S : Finset ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀ a∈ins, a.Valid (ids S)) (hl : ins.length≤25)
    (v : ℕ→ℕ) (B : ℕ) (hw : ∀ i∈ids S, (v i).bits.length≤B)
    (hc : ∀ a∈ins, a.literalWidth≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank (ids S) v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code ins) cost s t ∧ cost≤stageCost B ∧
      NatAssign.Bank (ids S) (NatAssign.values ins v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨cost,t,he,hcost,hb,hsc',hf⟩ :=
    NatAssign.executes (ids S) (ids_ge S) ins hv v input tape s hs hsc
  have hp := NatAssign.price_bound (ids S) ins hv v B hw hc
  have hcoef : 3000*8^ins.length≤(2:ℕ)^96 := by
    calc
      _ ≤ 3000*8^25 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_right (by decide) hl)
      _ ≤ _ := by norm_num
  exact ⟨cost,t,he,hcost.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),hb,hsc',
    hf.mono (changes_subset S ins hv)⟩

theorem binary_executes (S : Finset ℕ) (op : BinaryOp) (target left right : ℕ)
    (ht : target∈S) (hl : left∈S) (hr : right∈S) (v : ℕ→Parts) (B : ℕ)
    (hw : ∀ i∈S, (v i).Width B) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) :
    ∃ cost t, Executes input tape (NatAssign.code (binaryStage op target left right)) cost s t ∧
      cost≤stageCost B ∧ Ready S (Function.update v target (op.eval (v left) (v right))) t ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨cost,t,he,hc,hb,hsc,hf⟩ := fixedStage_executes S (binaryStage op target left right)
    (binaryStage_valid S op target left right ht hl hr) (by rw [binaryStage_length])
    (dataValues v) B (dataValues_width S v B hw)
    (fun a ha => by rw [binaryStage_literalWidth op target left right a ha]; omega)
    input tape s hs.1 hs.2
  rw [binaryStage_values] at hb
  exact ⟨cost,t,he,hc,⟨hb,hsc⟩,hf⟩

theorem BinaryOp.eval_value (op : BinaryOp) (x y : Parts) (hx : x.Valid) (hy : y.Valid) :
    (op.eval x y).value = match op with
      | .add => x.value+y.value
      | .sub => x.value-y.value
      | .mul => x.value*y.value := by
  cases op
  · exact Parts.add_value x y hx hy
  · exact Parts.sub_value x y hx hy
  · exact Parts.mul_value x y

theorem BinaryOp.eval_valid (op : BinaryOp) {x y : Parts} (hx : x.Valid) (hy : y.Valid) :
    (op.eval x y).Valid := by
  cases op
  · exact Parts.add_valid hx hy
  · exact Parts.sub_valid hx hy
  · exact Parts.mul_valid hx hy

theorem BinaryOp.eval_width (op : BinaryOp) {x y : Parts} {B C : ℕ}
    (hx : x.Width B) (hy : y.Width C) : (op.eval x y).Width (B+C+1) := by
  cases op
  · exact Parts.Width.add hx hy
  · exact Parts.Width.sub hx hy
  · exact Parts.Width.mul hx hy

#print axioms binary_executes

end Maxwell.Continuum.RationalDataflow
