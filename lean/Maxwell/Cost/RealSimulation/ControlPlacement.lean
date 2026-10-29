import Maxwell.Cost.RealSimulation.ControlSyntax

namespace Maxwell.Cost.RealSimulation.Control

namespace Placed

variable {machine : Machine} {base exitPC : ℕ}

theorem skip (h : Placed machine .skip base exitPC) :
    machine.code[base]? = some (.jump exitPC) := by
  simpa [Code.compileAt] using h ⟨0, by simp [Code.size]⟩

theorem call {body : Machine} (h : Placed machine (.call body) base exitPC) :
    machine.Contains body base exitPC := by
  intro i
  simpa [Code.compileAt] using h i

theorem seq_first {first second : Code} (h : Placed machine (.seq first second) base exitPC) :
    Placed machine first base (base + first.size) := by
  intro i
  have hi : i.val < (first.compileAt base (base + first.size)).length := by rw [Code.compileAt_length]; exact i.isLt
  have hp := h ⟨i.val, by simp only [Code.size]; omega⟩
  simpa only [Code.compileAt, List.getElem?_append_left hi] using hp

theorem seq_second {first second : Code} (h : Placed machine (.seq first second) base exitPC) :
    Placed machine second (base + first.size) exitPC := by
  intro i
  have hi : (first.compileAt base (base + first.size)).length ≤ first.size + i.val := by simp
  have hp := h ⟨first.size + i.val, by simp only [Code.size]; omega⟩
  simpa [Code.compileAt, List.getElem?_append_right hi, Nat.add_assoc, Nat.one_add] using hp

theorem branch_head {left right : ℕ} {yes no : Code}
    (h : Placed machine (.branch left right yes no) base exitPC) :
    machine.code[base]? = some (.branchIndexLE left right (base + 1) (base + 1 + yes.size)) := by
  simpa [Code.compileAt] using h ⟨0, by simp [Code.size]⟩

theorem branch_yes {left right : ℕ} {yes no : Code}
    (h : Placed machine (.branch left right yes no) base exitPC) :
    Placed machine yes (base + 1) exitPC := by
  intro i
  have hi : i.val < (yes.compileAt (base + 1) exitPC).length := by rw [Code.compileAt_length]; exact i.isLt
  have hp := h ⟨1 + i.val, by simp only [Code.size]; omega⟩
  simpa [Code.compileAt, List.getElem?_append_left hi, Nat.add_assoc, Nat.one_add] using hp

theorem branch_no {left right : ℕ} {yes no : Code}
    (h : Placed machine (.branch left right yes no) base exitPC) :
    Placed machine no (base + 1 + yes.size) exitPC := by
  intro i
  have hi : (yes.compileAt (base + 1) exitPC).length ≤ yes.size + i.val := by simp
  have hp := h ⟨(yes.size + i.val) + 1, by simp only [Code.size]; omega⟩
  simp only [Code.compileAt, List.cons_append, List.nil_append,
    List.getElem?_cons_succ] at hp
  rw [List.getElem?_append_right hi] at hp
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp

theorem loop_head {left right : ℕ} {body : Code}
    (h : Placed machine (.loop left right body) base exitPC) :
    machine.code[base]? = some (.branchIndexLE left right (base + 1) exitPC) := by
  simpa [Code.compileAt] using h ⟨0, by simp [Code.size]⟩

theorem loop_body {left right : ℕ} {body : Code}
    (h : Placed machine (.loop left right body) base exitPC) :
    Placed machine body (base + 1) base := by
  intro i
  have hp := h ⟨1 + i.val, by simp only [Code.size]; omega⟩
  simpa [Code.compileAt, Nat.add_assoc, Nat.one_add] using hp

end Placed

theorem Code.compile_placed (code : Code) : Placed code.compile code 0 code.size := by
  intro i
  simp [Code.compile]

@[simp] theorem Code.compile_halt (code : Code) : code.compile.code[code.size]? = some .halt := by
  simp [compile]

end Maxwell.Cost.RealSimulation.Control
