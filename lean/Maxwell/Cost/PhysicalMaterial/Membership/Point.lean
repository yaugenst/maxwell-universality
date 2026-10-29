import Maxwell.Cost.PhysicalMaterial.Membership.Coordinate

namespace Maxwell.Cost.PhysicalMaterial.Membership
open Structured RationalAccumulator

abbrev Point := Fin 3 → ℤ

def Width (cell anchor : Fin 3 → ℕ) (B : ℕ) : Prop :=
  ∀ j, (cell j).bits.length ≤ B ∧ (anchor j).bits.length ≤ B

def coordinateFactor (delta : ℤ) : ℕ := 500*(2+offsetSize delta)

def axesCode (d : Point) : List (Fin 3) → Code
  | [] => Code.atom (.literal 2 true)
  | j::js => .seq (coordinateCode j (d j)) (.branch 2 (axesCode d js) .skip)

def axesFactor (d : Point) (js : List (Fin 3)) : ℕ :=
  (js.map (fun j => coordinateFactor (d j)+2)).sum+2

set_option maxRecDepth 8192 in
theorem axes_executes (d : Point) (js : List (Fin 3)) (cell anchor : Fin 3 → ℕ) (B : ℕ)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : Words cell anchor s.val) (hf : Free s.val) (hb : Width cell anchor B) :
    ∃ cost t, cost ≤ axesFactor d js*(B+1) ∧ Executes input tape (axesCode d js) cost s t ∧
      (t.val.registers 2 = true ↔ ∀ j ∈ js, (cell j : ℤ) = (anchor j : ℤ)+d j) ∧
      Free t.val ∧ BinaryPrecision.Frame work s.val t.val := by
  induction js generalizing s with
  | nil =>
    let t := Store.ofState (s.val.setRegister 2 true)
    refine ⟨2,t,by simp [axesFactor],Executes.literal input tape s 2 true,?_,hf,?_⟩
    · simp [t,Store.ofState,BitRAMState.setRegister]
    · exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
  | cons j js ih =>
    obtain ⟨ac,a,hac,ea,abit,af,framea⟩ := coordinate_executes j (d j) cell anchor input tape s hw hf
    have hac' : ac ≤ coordinateFactor (d j)*(B+1) := by
      have hx := (hb j).1
      have hy := (hb j).2
      unfold coordinateFactor
      nlinarith
    have factor : axesFactor d (j::js) = coordinateFactor (d j)+2+axesFactor d js := by
      simp [axesFactor]; omega
    cases ha : a.val.registers 2 with
    | false =>
      refine ⟨ac+(1+1),a,?_,ea.seq (.no ha (.skip a)),?_,af,framea⟩
      · rw [factor]
        nlinarith
      · simp only [ha,Bool.false_eq_true,false_iff]
        intro h
        have hh := abit.mpr (h j (by simp))
        simp [ha] at hh
    | true =>
      obtain ⟨bc,b,hbc,eb,bbit,bf,frameb⟩ := ih a (hw.frame framea) af
      refine ⟨ac+(1+bc),b,?_,ea.seq (.yes ha eb),?_,bf,framea.trans frameb⟩
      · rw [factor]
        nlinarith
      · constructor
        · intro ht k hk
          rcases List.mem_cons.mp hk with he|he
          · subst k; exact abit.mp ha
          · exact bbit.mp ht k he
        · intro ht
          exact bbit.mpr (fun k hk => ht k (List.mem_cons_of_mem j hk))

def pointCode (d : Point) : Code := axesCode d [0,1,2]
def pointFactor (d : Point) : ℕ := axesFactor d [0,1,2]

theorem point_executes (d : Point) (cell anchor : Fin 3 → ℕ) (B : ℕ)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hw : Words cell anchor s.val) (hf : Free s.val) (hb : Width cell anchor B) :
    ∃ cost t, cost ≤ pointFactor d*(B+1) ∧ Executes input tape (pointCode d) cost s t ∧
      (t.val.registers 2 = true ↔ ∀ j, (cell j : ℤ) = (anchor j : ℤ)+d j) ∧
      Free t.val ∧ BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨cost,t,hc,he,hbit,ht,hframe⟩ := axes_executes d [0,1,2] cell anchor B input tape s hw hf hb
  refine ⟨cost,t,hc,he,?_,ht,hframe⟩
  rw [hbit]
  constructor
  · intro h j
    apply h j
    fin_cases j <;> simp
  · intro h j _
    exact h j

end Maxwell.Cost.PhysicalMaterial.Membership
