import Maxwell.Cost.CalibrationSource.Index

namespace Maxwell.Cost.CalibrationSource
open Structured
open RationalAccumulator (Word)
open Defect.FiniteStencil Spectral.Lattice
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Input274 is the actual inverse degree,275 the chosen spacing,276 the
retained work-cube radix. Banks280..285 are temporary natural words. -/
def indexIds : Finset ℕ := {274,275,276,280,281,282,283,284,285}

def commonInstructions : List NatAssign.Instruction :=
  [.copy 274 283,.literal 284 4,.multiply 284 283,.literal 284 2,.add 284 283]

def coordinateInstructions (R0 L : ℕ) (v : Site) (e : Edge) (j : Direction) :
    List NatAssign.Instruction :=
  [.literal (280+j.val) ((R0 : ℤ)+e.2 j).toNat,.add 283 (280+j.val),
    .literal 284 (20*slope L v j),.multiply 275 284,.add 284 (280+j.val)]

def indexInstructions (R0 L : ℕ) (v : Site) (e : Edge) : List NatAssign.Instruction :=
  commonInstructions ++ coordinateInstructions R0 L v e 0 ++
    coordinateInstructions R0 L v e 1 ++ coordinateInstructions R0 L v e 2 ++
      [.literal 285 e.1.val,.multiply 276 285,.add 280 285,
        .multiply 276 285,.add 281 285,.multiply 276 285,.add 282 285]

def indexCode (R0 L : ℕ) (v : Site) (e : Edge) : Code :=
  NatAssign.code (indexInstructions R0 L v e)

theorem indexInstructions_length (R0 L : ℕ) (v : Site) (e : Edge) :
    (indexInstructions R0 L v e).length = 27 := rfl

theorem indexInstructions_valid (R0 L : ℕ) (v : Site) (e : Edge)
    (a : NatAssign.Instruction) (ha : a ∈ indexInstructions R0 L v e) : a.Valid indexIds := by
  simp only [indexInstructions,commonInstructions,coordinateInstructions,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at ha
  simp only [or_assoc] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [NatAssign.Instruction.Valid,indexIds]


def indexWork : Finset ℕ := {0,1,2,3,280,281,282,283,284,285}

theorem index_changes (R0 L : ℕ) (v : Site) (e : Edge) :
    NatAssign.changes (indexInstructions R0 L v e) ⊆ indexWork := by
  simp [NatAssign.changes,indexInstructions,commonInstructions,coordinateInstructions,
    NatAssign.Instruction.target,indexWork]
  decide

theorem indexInstructions_value (R0 L : ℕ) (v : Site) (e : Edge)
    (d N : ℕ) (values : ℕ → ℕ)
    (hN : values 274 = N) (hd : values 275 = d)
    (hw : values 276 = cubeWidth (radius R0 L d N)) :
    NatAssign.values (indexInstructions R0 L v e) values 285 = address R0 L v e d N := by
  simp [indexInstructions,commonInstructions,coordinateInstructions,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    hN,hd,hw,address,digit]
  ring

/-- A fixed finite arithmetic program computes the address of one actual
translated source edge. Its bit cost is quadratic in stored word width. -/
theorem index_executes (R0 L : ℕ) (v : Site) (e : Edge)
    (d N B : ℕ) (values : ℕ → ℕ)
    (hN : values 274 = N) (hd : values 275 = d)
    (hw : values 276 = cubeWidth (radius R0 L d N))
    (hb : ∀ i ∈ indexIds, (values i).bits.length ≤ B)
    (hc : ∀ a ∈ indexInstructions R0 L v e, a.literalWidth ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (stored : NatAssign.Bank indexIds values s.val) (scratch : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (indexCode R0 L v e) cost s t ∧
      cost ≤ 3000*8^27*(B+2)^2 ∧
      Word t.val 285 (address R0 L v e d N) ∧
      NatAssign.Bank indexIds (NatAssign.values (indexInstructions R0 L v e) values) t.val ∧
      NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (NatAssign.changes (indexInstructions R0 L v e)) s.val t.val := by
  obtain ⟨cost,t,he,hcost,ht,hs,hf⟩ := NatAssign.executes indexIds
    (by intro i hi; simp only [indexIds,Finset.mem_insert,Finset.mem_singleton] at hi; omega)
    (indexInstructions R0 L v e) (indexInstructions_valid R0 L v e) values input tape s stored scratch
  refine ⟨cost,t,he,?_,?_,ht,hs,hf⟩
  · have hp := NatAssign.price_bound indexIds (indexInstructions R0 L v e)
      (indexInstructions_valid R0 L v e) values B hb hc
    rw [indexInstructions_length] at hp
    exact hcost.trans hp
  · simpa only [indexInstructions_value R0 L v e d N values hN hd hw] using ht 285 (by decide)

end Maxwell.Cost.CalibrationSource
