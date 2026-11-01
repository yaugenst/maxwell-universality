import Maxwell.Continuum.ParameterSpacingSearch
import Maxwell.Cost.SelectedParameters.AllComparisons

/-! Runtime operands for the literal five-test spacing search. The two
exponential denominators are squared when the candidate spacing doubles. -/

namespace Maxwell.Continuum.Parameters.SpacingMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048

structure Data where
  constant : ℕ
  length : ℕ
  conditionNum : ℕ
  conditionDen : ℕ
  epsilonNum : ℕ
  epsilonDen : ℕ

def extra : Finset ℕ := Finset.Icc 2000 2031
def ids : Finset ℕ := Compare.ids extra

def inputs (D : Data) (k : ℕ) (i : ℕ) : ℕ :=
  if i=2000 then D.constant else if i=2001 then D.length else
  if i=2002 then D.conditionNum else if i=2003 then D.conditionDen else
  if i=2004 then D.epsilonNum else if i=2005 then D.epsilonDen else
  if i=2006 then 2^k else if i=2007 then 3^(2^k) else if i=2008 then 8^(2^k) else
  if i=2009 then 1 else if i=2010 then 2^24 else if i=2011 then 2^1026 else 0

def formulas : List NatAssign.Instruction :=
  [.copy 2000 2020,.multiply 2000 2020,.multiply 2000 2020,.multiply 2000 2020,
   .copy 2020 2021,.multiply 2020 2021,
   .copy 2001 2022,.multiply 2001 2022,
   .copy 2001 2023]++List.replicate 11 (.multiply 2001 2023)++
  [.copy 2006 2024]++List.replicate 14 (.multiply 2006 2024)++
  [.copy 2011 2025,.multiply 2008 2025,
   .copy 2020 2026,.multiply 2023 2026,
   .copy 2005 2027,.multiply 2010 2027,
   .copy 2007 2028,.multiply 2007 2028,
   .copy 2022 2029,.multiply 2004 2029,.multiply 2003 2029,
   .copy 2025 2030,.multiply 2027 2030,.multiply 2002 2030,
   .copy 2020 2031,.multiply 2001 2031]

def values (D : Data) (k : ℕ) : ℕ→ℕ := NatAssign.values formulas (inputs D k)

def tests : List AllComparisons.Test :=
  [((2021,2009),(2006,2009)),((2031,2009),(2024,2009)),
   ((2022,2025),(2009,2009)),((2026,2007),(2004,2027)),
   ((2026,2028),(2029,2030))]

theorem ids_ge (i : ℕ) (hi : i ∈ ids) : 4 ≤ i := by
  simp only [ids,Compare.ids,extra,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem formulas_valid : ∀ inst ∈ formulas, inst.Valid ids := by
  simp [formulas,NatAssign.Instruction.Valid,ids,Compare.ids,extra]

theorem tests_valid : ∀ q ∈ tests, AllComparisons.Valid extra q := by
  simp [tests,AllComparisons.Valid,extra]

theorem fields (D : Data) (k : ℕ) :
    values D k 2020=D.constant^4 ∧
    values D k 2021=D.constant^8 ∧
    values D k 2022=D.length^2 ∧
    values D k 2023=D.length^12 ∧
    values D k 2024=(2^k)^15 ∧
    values D k 2025=2^1026*8^(2^k) ∧
    values D k 2026=D.constant^4*D.length^12 ∧
    values D k 2027=D.epsilonDen*2^24 ∧
    values D k 2028=(3^(2^k))^2 ∧
    values D k 2029=D.length^2*D.epsilonNum*D.conditionDen ∧
    values D k 2030=(2^1026*8^(2^k))*(D.epsilonDen*2^24)*D.conditionNum ∧
    values D k 2031=D.constant^4*D.length := by
  simp [values,formulas,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,inputs,List.replicate_succ]
  ring_nf
  simp

theorem input_fields (D : Data) (k i : ℕ) (hi : i≤2019) :
    values D k i=inputs D k i := by
  simp [values,formulas,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,List.replicate_succ,
    show i≠2020 by omega,show i≠2021 by omega,show i≠2022 by omega,
    show i≠2023 by omega,show i≠2024 by omega,show i≠2025 by omega,
    show i≠2026 by omega,show i≠2027 by omega,show i≠2028 by omega,
    show i≠2029 by omega,show i≠2030 by omega,show i≠2031 by omega]

#print axioms fields
#print axioms input_fields

end Maxwell.Continuum.Parameters.SpacingMachine
