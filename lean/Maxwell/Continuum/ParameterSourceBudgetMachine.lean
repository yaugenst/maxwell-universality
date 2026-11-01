import Maxwell.Continuum.ParameterSourceBudgetValues

namespace Maxwell.Continuum.Parameters.SourceBudgetMachine
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

def code (κ η e : ℕ) : Code := NatAssign.code (instructions κ η e)
def workspace : Finset ℕ := {0,1,2,3}∪ids
def literalBound (e : ℕ) : ℕ := (minimumLengthExponent e).bits.length+e+70
def width (κ η e B : ℕ) : ℕ := 2^(instructions κ η e).length*(B+literalBound e+1)
def cost (κ η e B : ℕ) : ℕ := 3000*8^(instructions κ η e).length*(B+literalBound e+2)^2

theorem ids_lower : ∀i∈ids,4≤ i := by
  intro i hi
  simp only [ids,extra,outputs,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem valid (κ η e : ℕ) : ∀a∈instructions κ η e,a.Valid ids := by
  intro a ha
  simp only [instructions,powers,List.mem_append] at ha
  rcases ha with (((ha|ha)|ha)|ha)|ha
  · exact NatAssign.power_valid ids 2301 2310 (κ+1) (by decide) (by decide) (by decide) a ha
  · exact NatAssign.power_valid ids 2301 2311 η (by decide) (by decide) (by decide) a ha
  all_goals simp only [conditionInstructions,errorInstructions,outputInstructions,
    List.mem_cons,List.not_mem_nil,or_false] at ha
  all_goals rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [NatAssign.Instruction.Valid,ids,extra,outputs]

theorem literals (κ η e : ℕ) : ∀a∈instructions κ η e,a.literalWidth≤literalBound e := by
  intro a ha
  simp only [instructions,powers,List.mem_append] at ha
  rcases ha with (((ha|ha)|ha)|ha)|ha
  · exact (NatAssign.power_literalWidth 2301 2310 (κ+1) a ha).trans (by unfold literalBound;omega)
  · exact (NatAssign.power_literalWidth 2301 2311 η a ha).trans (by unfold literalBound;omega)
  all_goals simp only [conditionInstructions,errorInstructions,outputInstructions,
    List.mem_cons,List.not_mem_nil,or_false] at ha
  all_goals rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [NatAssign.Instruction.literalWidth,literalBound]
  all_goals simp only [show (9:ℕ).bits.length=4 by decide,
    show (256:ℕ).bits.length=9 by decide,show (1024:ℕ).bits.length=11 by decide,
    show (4:ℕ).bits.length=3 by decide,show (16:ℕ).bits.length=5 by decide,
    show (2048:ℕ).bits.length=12 by decide,show (1:ℕ).bits.length=1 by decide,
    show (2^54*129:ℕ).bits.length=62 by decide,Nat.size_eq_bits_len,Nat.size_pow]
  all_goals omega

theorem executes (κ η e B : ℕ) (v : ℕ→ℕ)
    (hw : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape (code κ η e) steps s t ∧ steps≤cost κ η e B ∧
      NatAssign.Bank ids (NatAssign.values (instructions κ η e) v) t.val ∧
      (∀i∈ids,(NatAssign.values (instructions κ η e) v i).bits.length≤width κ η e B) ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨steps,t,he,hc,bt,st,hf⟩:=NatAssign.executes ids ids_lower (instructions κ η e)
    (valid κ η e) v input tape s bank scratch
  have inputWidth : ∀i∈ids,(v i).bits.length≤B+literalBound e := fun i hi=>(hw i hi).trans (by omega)
  have literalWidth : ∀a∈instructions κ η e,a.literalWidth≤B+literalBound e :=
    fun a ha=>(literals κ η e a ha).trans (by omega)
  refine ⟨steps,t,he,hc.trans (NatAssign.price_bound ids _ (valid κ η e) v _ inputWidth literalWidth),
    bt,?_,st,hf.mono ?_⟩
  · have wh:=NatAssign.values_width ids _ (valid κ η e) v _ inputWidth literalWidth
    intro i hi
    exact (Nat.le_add_right _ 1).trans (wh i hi)
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_left _ hi
    · obtain ⟨a,ha,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hi)
      apply Finset.mem_union_right
      have h:=valid κ η e a ha
      cases a <;> first | exact h | exact h.2.1

#print axioms executes
end Maxwell.Continuum.Parameters.SourceBudgetMachine
