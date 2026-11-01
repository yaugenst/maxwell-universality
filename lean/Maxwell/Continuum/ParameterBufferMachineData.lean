import Maxwell.Continuum.ParameterBufferSearch
import Maxwell.Cost.SelectedParameters.AllComparisons
import Maxwell.Cost.Structured.NatAssign.Values

/-! Exact stored operands for the continuum buffer search. Positive raw
fractions represent condition, tolerance, detuning, and alpha; every
candidate's box count and stopping ratio are recomputed by fixed arithmetic. -/
namespace Maxwell.Continuum.Parameters.BufferMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.SelectedParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

structure Data where
  constant : ℕ
  length : ℕ
  wells : ℕ
  sourceSize : ℕ
  conditionNum : ℕ
  conditionDen : ℕ
  epsilonNum : ℕ
  epsilonDen : ℕ
  alphaNum : ℕ
  alphaDen : ℕ
  tauNum : ℕ
  tauDen : ℕ
  span : Fin 3→ℕ

def extra : Finset ℕ := Finset.Icc 2100 2156∪{220,221,222,223}
def ids : Finset ℕ := Compare.ids extra

def inputs (D : Data) (k i : ℕ) : ℕ :=
  if i=2100 then D.constant else if i=2101 then D.length else
  if i=2102 then D.wells else if i=2103 then D.sourceSize else
  if i=2104 then D.conditionNum else if i=2105 then D.conditionDen else
  if i=2106 then D.epsilonNum else if i=2107 then D.epsilonDen else
  if i=2108 then D.alphaNum else if i=2109 then D.alphaDen else
  if i=2110 then D.tauNum else if i=2111 then D.tauDen else
  if i=2112 then D.span 0 else if i=2113 then D.span 1 else if i=2114 then D.span 2 else
  if i=2115 then 2^k else if i=2116 then slowDivisor else
  if i=2117 then 2^((2^k)/slowDivisor) else if i=2118 then (2^k)/slowDivisor else
  if i=2120 then 1 else if i=2121 then 2 else if i=2122 then 4 else if i=2123 then 2^35 else 0

def boxFormulas : List NatAssign.Instruction :=
  [.copy 2101 2125,.multiply 2115 2125,
   .copy 2125 2126,.add 2101 2126,.add 2122 2126,
   .copy 2126 2127,.add 2112 2127,.multiply 2122 2127,.add 2120 2127,
   .copy 2126 2128,.add 2113 2128,.multiply 2122 2128,.add 2120 2128,
   .copy 2126 2129,.add 2114 2129,.multiply 2122 2129,.add 2120 2129,
   .copy 2121 2130,.multiply 2127 2130,.multiply 2128 2130,.multiply 2129 2130,
   .copy 2130 2131,.add 2120 2131,.copy 2131 2132,.multiply 2131 2132]

def sizeFormulas : List NatAssign.Instruction :=
  [
   .copy 2102 2133,.add 2103 2133,.add 2120 2133,.copy 2133 2134,.multiply 2133 2134]

def powerFormulas : List NatAssign.Instruction :=
  [
   .copy 2100 2135,.multiply 2100 2135,.copy 2135 2136,.multiply 2135 2136,
   .copy 2136 2137,.multiply 2136 2137,.copy 2137 2138,.multiply 2137 2138,
   .copy 2138 2139,.multiply 2138 2139,
   .copy 2101 2140,.multiply 2101 2140,.copy 2140 2141,.multiply 2140 2141,
   .copy 2141 2142,.multiply 2141 2142,.copy 2142 2143,.multiply 2142 2143,
   .copy 2143 2144,.multiply 2143 2144,.copy 2144 2145,.multiply 2144 2145,
   .copy 2145 2146,.multiply 2144 2146,.multiply 2141 2146]

def fractionFormulas : List NatAssign.Instruction :=
  [
   .copy 2105 2147,.add 2104 2147,.copy 2147 2148,.multiply 2147 2148,
   .copy 2148 2149,.multiply 2148 2149,
   .copy 2108 2150,.add 2109 2150,.copy 2150 2151,.multiply 2150 2151,
   .copy 2105 2152,.multiply 2105 2152,.copy 2152 2153,.multiply 2152 2153,
   .copy 2108 2154,.multiply 2108 2154]

def productFormulas : List NatAssign.Instruction :=
  [
   .copy 2123 2155,.multiply 2139 2155,.multiply 2103 2155,.multiply 2130 2155,
   .multiply 2132 2155,.multiply 2134 2155,.multiply 2149 2155,.multiply 2151 2155,
   .multiply 2146 2155,.multiply 2111 2155,.multiply 2107 2155,
   .copy 2153 2156,.multiply 2154 2156,.multiply 2110 2156,.multiply 2106 2156]

def formulas : List NatAssign.Instruction :=
  boxFormulas++sizeFormulas++powerFormulas++fractionFormulas++productFormulas

def values (D : Data) (k : ℕ) : ℕ→ℕ := NatAssign.values formulas (inputs D k)
def tests : List AllComparisons.Test := [((2155,2156),(2117,2120))]

def numerator (D : Data) (t : ℕ) : ℕ :=
  2^35*D.constant^32*D.sourceSize*boxCount D.span D.length t*(1+boxCount D.span D.length t)^2*
    (1+D.wells+D.sourceSize)^2*(D.conditionDen+D.conditionNum)^4*(D.alphaNum+D.alphaDen)^2*
      D.length^100*D.tauDen*D.epsilonDen

def denominator (D : Data) : ℕ := D.conditionDen^4*D.alphaNum^2*D.tauNum*D.epsilonNum

theorem ids_ge (i : ℕ) (hi : i∈ids) : 10  ≤  i := by
  simp only [ids,Compare.ids,extra,Finset.mem_union,Finset.mem_Icc,
    Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem formulas_extra_valid : ∀a∈formulas,a.Valid extra := by
  simp [formulas,boxFormulas,sizeFormulas,powerFormulas,fractionFormulas,productFormulas,NatAssign.Instruction.Valid,extra]

theorem formulas_valid : ∀a∈formulas,a.Valid ids := by
  simp [formulas,boxFormulas,sizeFormulas,powerFormulas,fractionFormulas,productFormulas,NatAssign.Instruction.Valid,ids,Compare.ids,extra]

theorem tests_valid : ∀q∈tests,AllComparisons.Valid extra q := by
  simp [tests,AllComparisons.Valid,extra]

theorem input_fields (D : Data) (k i : ℕ) (hi : i < 2125) : values D k i=inputs D k i := by
  apply NatAssign.values_preserves
  simp [formulas,boxFormulas,sizeFormulas,powerFormulas,fractionFormulas,productFormulas,NatAssign.Instruction.target]
  omega

theorem boxFormulas_outside (v : ℕ→ℕ) (i : ℕ) (hi : i < 2125 ∨ 2132< i) :
    NatAssign.values boxFormulas v i=v i := by
  apply NatAssign.values_preserves
  simp [boxFormulas,NatAssign.Instruction.target]
  omega

theorem sizeFormulas_outside (v : ℕ→ℕ) (i : ℕ) (hi : i < 2133 ∨ 2134< i) :
    NatAssign.values sizeFormulas v i=v i := by
  apply NatAssign.values_preserves
  simp [sizeFormulas,NatAssign.Instruction.target]
  omega

theorem powerFormulas_outside (v : ℕ→ℕ) (i : ℕ) (hi : i < 2135 ∨ 2146< i) :
    NatAssign.values powerFormulas v i=v i := by
  apply NatAssign.values_preserves
  simp [powerFormulas,NatAssign.Instruction.target]
  omega

theorem fractionFormulas_outside (v : ℕ→ℕ) (i : ℕ) (hi : i < 2147 ∨ 2154< i) :
    NatAssign.values fractionFormulas v i=v i := by
  apply NatAssign.values_preserves
  simp [fractionFormulas,NatAssign.Instruction.target]
  omega

theorem productFormulas_outside (v : ℕ→ℕ) (i : ℕ) (hi : i < 2155 ∨ 2156< i) :
    NatAssign.values productFormulas v i=v i := by
  apply NatAssign.values_preserves
  simp [productFormulas,NatAssign.Instruction.target]
  omega

def inputBox (v : ℕ→ℕ) : ℕ := boxCount (fun j=>v (2112+j.val)) (v 2101) (v 2115)

theorem box_fields (v : ℕ→ℕ) (h1 : v 2120=1) (h2 : v 2121=2) (h4 : v 2122=4) :
    NatAssign.values boxFormulas v 2130=inputBox v ∧
    NatAssign.values boxFormulas v 2132=(1+inputBox v)^2 := by
  simp [boxFormulas,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,inputBox,boxCount,boxSide,Fin.prod_univ_three,h1,h2,h4]
  constructor <;> ring

theorem size_fields (v : ℕ→ℕ) (h1 : v 2120=1) :
    NatAssign.values sizeFormulas v 2134=(1+v 2102+v 2103)^2 := by
  simp [sizeFormulas,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,h1]
  ring

theorem power_fields (v : ℕ→ℕ) :
    NatAssign.values powerFormulas v 2139=(v 2100)^32 ∧
    NatAssign.values powerFormulas v 2146=(v 2101)^100 := by
  simp [powerFormulas,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target]
  constructor <;> ring

theorem fraction_fields (v : ℕ→ℕ) :
    NatAssign.values fractionFormulas v 2149=(v 2105+v 2104)^4 ∧
    NatAssign.values fractionFormulas v 2151=(v 2108+v 2109)^2 ∧
    NatAssign.values fractionFormulas v 2153=(v 2105)^4 ∧
    NatAssign.values fractionFormulas v 2154=(v 2108)^2 := by
  simp [fractionFormulas,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem product_fields (v : ℕ→ℕ) :
    NatAssign.values productFormulas v 2155=
      v 2123*v 2139*v 2103*v 2130*v 2132*v 2134*v 2149*v 2151*v 2146*v 2111*v 2107 ∧
    NatAssign.values productFormulas v 2156=v 2153*v 2154*v 2110*v 2106 := by
  simp [productFormulas,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target]
  constructor <;> ac_rfl

theorem fields (D : Data) (k : ℕ) :
    values D k 2130=boxCount D.span D.length (2^k) ∧
    values D k 2155=numerator D (2^k) ∧ values D k 2156=denominator D := by
  let v0 := inputs D k
  let v1 := NatAssign.values boxFormulas v0
  let v2 := NatAssign.values sizeFormulas v1
  let v3 := NatAssign.values powerFormulas v2
  let v4 := NatAssign.values fractionFormulas v3
  have b0 (i : ℕ) (hi : i < 2125) : v4 i=inputs D k i := by
    dsimp only [v4,v3,v2,v1,v0]
    rw [fractionFormulas_outside _ _ (by omega),powerFormulas_outside _ _ (by omega),
      sizeFormulas_outside _ _ (by omega),boxFormulas_outside _ _ (by omega)]
  have box := box_fields v0 (by simp [v0,inputs]) (by simp [v0,inputs]) (by simp [v0,inputs])
  have box_eq : inputBox v0=boxCount D.span D.length (2^k) := by
    simp only [inputBox,v0,inputs]
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [box_eq] at box
  change v1 2130=_ ∧ v1 2132=_ at box
  have sz := size_fields v1 (by
    dsimp only [v1]
    rw [boxFormulas_outside _ _ (by decide)]
    simp [v0,inputs])
  change v2 2134=_ at sz
  have pw := power_fields v2
  change v3 2139=_ ∧ v3 2146=_ at pw
  have fr := fraction_fields v3
  change v4 2149=_ ∧ v4 2151=_ ∧ v4 2153=_ ∧ v4 2154=_ at fr
  have pr := product_fields v4
  have b1 (i : ℕ) (hi : i < 2125) : v1 i=inputs D k i := boxFormulas_outside _ _ (Or.inl hi)
  have b2 (i : ℕ) (hi : i < 2133) : v2 i=v1 i := sizeFormulas_outside _ _ (Or.inl hi)
  have b3 (i : ℕ) (hi : i < 2135) : v3 i=v2 i := powerFormulas_outside _ _ (Or.inl hi)
  have b4 (i : ℕ) (hi : i < 2147) : v4 i=v3 i := fractionFormulas_outside _ _ (Or.inl hi)
  change NatAssign.values productFormulas v4 2130=_ ∧
    NatAssign.values productFormulas v4 2155=_ ∧ NatAssign.values productFormulas v4 2156=_
  rw [productFormulas_outside _ _ (by decide),pr.1,pr.2]
  simp only [b0 2123 (by decide),
    b0 2103 (by decide),
    b0 2111 (by decide),
    b0 2107 (by decide),
    b0 2110 (by decide),
    b0 2106 (by decide),
    b4 2130 (by decide),
    b4 2132 (by decide),
    b4 2134 (by decide),
    b4 2139 (by decide),
    b4 2146 (by decide),
    b3 2130 (by decide),
    b3 2132 (by decide),
    b3 2134 (by decide),
    b3 2105 (by decide),
    b3 2104 (by decide),
    b3 2108 (by decide),
    b3 2109 (by decide),
    b2 2130 (by decide),
    b2 2132 (by decide),
    b2 2100 (by decide),
    b2 2101 (by decide),
    b2 2105 (by decide),
    b2 2104 (by decide),
    b2 2108 (by decide),
    b2 2109 (by decide),
    b1 2102 (by decide),
    b1 2103 (by decide),
    b1 2100 (by decide),
    b1 2101 (by decide),
    b1 2105 (by decide),
    b1 2104 (by decide),
    b1 2108 (by decide),
    b1 2109 (by decide),fr.1,fr.2.1,fr.2.2.1,fr.2.2.2,pw.1,pw.2,sz,box.1,box.2,
    inputs,numerator,denominator]
  norm_num only [ite_true,ite_false]
  exact ⟨trivial,trivial,trivial⟩

#print axioms fields
end Maxwell.Continuum.Parameters.BufferMachine
