import Maxwell.Cost.RealSimulation.Primitives

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

/-- Input strides are fixed parameters of the compiled wrapper, not runtime
multiplication operations. The source cells and output/log banks have stride4. -/
structure Layout where
  realInputStride : ℕ
  indexInputStride : ℕ

def slot (origin bank address : ℕ) : ℕ := origin + 4 * address + bank

theorem slot_injective (origin bank bank' a a' : ℕ) (hb : bank < 4) (hb' : bank' < 4) :
    slot origin bank a = slot origin bank' a' ↔ bank = bank' ∧ a = a' := by
  unfold slot
  omega

theorem slot_ge_origin (origin bank a : ℕ) : origin ≤ slot origin bank a := by
  unfold slot
  omega

def originRegister : ℕ := 160
def realInputBase : ℕ := 161
def realInputLength : ℕ := 162
def indexInputBase : ℕ := 163
def indexInputLength : ℕ := 164
def fuelRegister : ℕ := 165
def statusRegister : ℕ := 166
def realOutputLength : ℕ := 167
def indexOutputLength : ℕ := 168
def logLength : ℕ := 169
def sourcePC : ℕ := 170
def activeRegister : ℕ := 171

def pointerRegister : ℕ := 0
def coordinateRegister : ℕ := 2
def valueRegister : ℕ := 3
def leftRegister : ℕ := 4
def rightRegister : ℕ := 5
def zeroRegister : ℕ := 6
def oneRegister : ℕ := 7
def dispatchRegister : ℕ := 8

noncomputable def putWord (s : Store) (register : ℕ) (value : ℝ) : Store :=
  ⟨{s.val with words := Function.update s.val.words register value, pc := 0}, rfl⟩

@[simp] theorem putWord_words (s : Store) (r j : ℕ) (v : ℝ) :
    (putWord s r v).val.words j = if j = r then v else s.val.words j := by
  simp [putWord, Function.update_apply]

end Maxwell.Cost.RealPrivate
