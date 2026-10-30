import Maxwell.Continuum.StoredGeometryLayout
import Maxwell.Continuum.NaturalSignedEmission

/-! Fixed scalar center calculation and signed output. Terminal coordinates
are doubled; mediator coordinates add the consecutive endpoints. Both use
the actually stored physical scale and buffer translation. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def coordinatePlan (terminal : Bool) (j : Fin 3) : List NatAssign.Instruction :=
  [.copy (976+j.val) 987,.add ((if terminal then 976 else 979)+j.val) 987,
    .multiply (983+j.val) 987,.add 982 987]

def coordinateValue (terminal : Bool) (j : Fin 3) (v : ℕ→ℕ) : ℕ :=
  v 982+v (983+j.val)*(v (976+j.val)+v ((if terminal then 976 else 979)+j.val))

def coordinateCode (terminal : Bool) (j : Fin 3) : Code :=
  .seq (NatAssign.code (coordinatePlan terminal j)) (EmitNonnegative.code 987)

theorem coordinatePlan_valid (terminal : Bool) (j : Fin 3) :
    ∀a∈coordinatePlan terminal j,a.Valid ids := by
  cases terminal <;> fin_cases j <;> simp [coordinatePlan,NatAssign.Instruction.Valid,ids]

theorem coordinate_values (terminal : Bool) (j : Fin 3) (v : ℕ→ℕ) :
    NatAssign.values (coordinatePlan terminal j) v=
      Function.update v 987 (coordinateValue terminal j v) := by
  ext i
  cases terminal <;> fin_cases j <;>
    simp [coordinatePlan,coordinateValue,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,Nat.add_comm]

theorem coordinate_bits (terminal : Bool) (j : Fin 3) (v : ℕ→ℕ) (B : ℕ)
    (hv : ∀i∈ids,(v i).bits.length≤B) : (coordinateValue terminal j v).bits.length≤2*B+2 := by
  have h₀ := hv 982 (by decide)
  have hA := hv (983+j.val) (by fin_cases j <;> decide)
  have hx := hv (976+j.val) (by fin_cases j <;> decide)
  have hy := hv ((if terminal then 976 else 979)+j.val) (by cases terminal <;> fin_cases j <;> decide)
  have hsum := bits_add_le (v (976+j.val)) (v ((if terminal then 976 else 979)+j.val))
  have hmul := bits_mul_le (v (983+j.val))
    (v (976+j.val)+v ((if terminal then 976 else 979)+j.val))
  have hout := bits_add_le (v 982)
    (v (983+j.val)*(v (976+j.val)+v ((if terminal then 976 else 979)+j.val)))
  unfold coordinateValue
  omega

structure OutputFrame (work : Finset ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  tapes : ∀i,i∉work→t.tapes i=s.tapes i

theorem Ready.emit {v : ℕ→ℕ} {s t : Store} (h : Ready v s) (f : EmitNatural.Frame s t) : Ready v t := by
  have keep (i : ℕ) := congrFun f.2.2.2.2 i
  exact ⟨fun i hi => word_of_eq (keep i) (h.bank i hi),
    ⟨blank_of_eq (keep 0) h.scratch.1,blank_of_eq (keep 1) h.scratch.2.1,
      blank_of_eq (keep 2) h.scratch.2.2.1,blank_of_eq (keep 3) h.scratch.2.2.2.1,
      blank_of_eq (keep 5) h.scratch.2.2.2.2.1,blank_of_eq (keep 6) h.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8) h.scratch.2.2.2.2.2.2.1,
      blank_of_eq (keep 9) h.scratch.2.2.2.2.2.2.2⟩,
    blank_of_eq (keep 7) h.seven⟩

theorem coordinate_executes (terminal : Bool) (j : Fin 3) (v : ℕ→ℕ) (B : ℕ)
    (hv : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready v s) :
    ∃cost t,Executes input tape (coordinateCode terminal j) cost s t ∧
      cost≤2^25*(B+3)^2 ∧ Ready (Function.update v 987 (coordinateValue terminal j v)) t ∧
      t.val.output=(Codec.int (coordinateValue terminal j v:ℤ)).reverse++s.val.output ∧
      OutputFrame {0,1,2,3,987} s.val t.val := by
  obtain ⟨c₀,a,e₀,hc₀,hb,hz,hf⟩ := NatAssign.executes ids
    (fun i hi => (by omega : 4≤960).trans (ids_ge i hi)) (coordinatePlan terminal j)
    (coordinatePlan_valid terminal j) v input tape s hs.bank hs.natural
  have hc : c₀≤3000*8^4*(B+2)^2 := hc₀.trans (NatAssign.price_bound ids _
    (coordinatePlan_valid terminal j) v B hv (by simp [coordinatePlan,NatAssign.Instruction.literalWidth]))
  have hchanges : NatAssign.changes (coordinatePlan terminal j)={0,1,2,3,987} := by
    cases terminal <;> fin_cases j <;> decide
  rw [coordinate_values] at hb
  have ha : Ready (Function.update v 987 (coordinateValue terminal j v)) a :=
    hs.stage hb hz (hf.mono (by rw [hchanges];decide))
  obtain ⟨t,e₁,out₁,f₁⟩ := EmitNonnegative.executes 987 (coordinateValue terminal j v) input tape a
    (by simpa only [Function.update_self] using hb 987 (by decide))
  have hcBits := coordinate_bits terminal j v B hv
  refine ⟨c₀+(20*(coordinateValue terminal j v).bits.length+28),t,e₀.seq e₁,?_,ha.emit f₁,?_,?_⟩
  · nlinarith only [hc,hcBits,Nat.zero_le B]
  · simpa only [hf.output] using out₁
  · refine ⟨f₁.2.2.1.trans hf.memory,f₁.2.1.trans hf.inputHead,
      f₁.2.2.2.1.trans hf.randomCursor,?_⟩
    intro i hi
    exact (congrFun f₁.2.2.2.2 i).trans (hf.tapes i (by simpa only [hchanges] using hi))

#print axioms coordinate_executes
end Maxwell.Continuum.GeometryOutput
