import Maxwell.Continuum.MachinRuntimeCore

/-! Runtime precision setup and cleanup for the fixed Machin program. -/
namespace Maxwell.Continuum.Machin.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def setupIds : Finset ℕ := {630,631,633}
def setup : List NatAssign.Instruction :=
  [.copy 630 631,.literal 633 6,.add 633 631,.literal 633 0]
def fullWorkspace : Finset ℕ := workspace∪{631,633}
def program : Code := .seq (NatAssign.code setup) (.seq core (.call (TapeOps.clear 631)))
def costBound (N : ℕ) : ℕ := 2^30*(N+8)^2+coreCost N+6*(N+6).bits.length+4

structure InputReady (N : ℕ) (s : BitRAMState) : Prop where
  precision : Word s 630 N
  index : Blank s 619
  two : Blank s 628
  terms : Blank s 631
  count : Blank s 632
  six : Blank s 633

theorem nat_bits_le_self (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

theorem setup_executes (N : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hz : NatAssign.Scratch s.val) (ha : InputReady N s.val) :
    ∃cost t,Executes input tape (NatAssign.code setup) cost s t ∧ cost≤2^30*(N+8)^2 ∧
      NatAssign.Scratch t.val ∧ AuxReady N t.val ∧ Blank t.val 633 ∧
      BinaryPrecision.Frame (NatAssign.changes setup) s.val t.val := by
  let v : ℕ→ℕ := fun i => if i=630 then N else 0
  have hv : ∀ i ∈ setupIds, 4 ≤ i := by simp only [setupIds,Finset.mem_insert,Finset.mem_singleton];omega
  have hb : NatAssign.Bank setupIds v s.val := by
    intro i hi
    simp only [setupIds,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl
    · simpa [v] using ha.precision
    · simpa [v,zero_word_iff_blank] using ha.terms
    · simpa [v,zero_word_iff_blank] using ha.six
  have hi : ∀a∈setup,a.Valid setupIds := by simp [setup,setupIds,NatAssign.Instruction.Valid]
  obtain ⟨c,t,e,hc,bt,zt,ft⟩ := NatAssign.executes setupIds hv setup hi v input tape s hb hz
  have hp := NatAssign.price_bound setupIds setup hi v (N+6) (by
      intro i _
      dsimp [v]
      split_ifs
      · exact (nat_bits_le_self N).trans (by omega)
      · simp)
    (by
      intro a ha
      simp only [setup,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;>
        simp [NatAssign.Instruction.literalWidth,show (6:ℕ).bits.length=3 from rfl])
  have hout : NatAssign.values setup v 631=N+6 ∧ NatAssign.values setup v 633=0 := by
    simp [setup,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,v,Nat.add_comm]
  refine ⟨c,t,e,?_,zt,⟨?_,?_,?_,?_⟩,?_,ft⟩
  · exact hc.trans (hp.trans (by
      change 3000*8^4*(N+6+2)^2≤2^30*(N+8)^2
      exact Nat.mul_le_mul_right _ (by norm_num)))
  · exact blank_of_eq (ft.tapes 619 (by decide)) ha.index
  · exact blank_of_eq (ft.tapes 628 (by decide)) ha.two
  · exact blank_of_eq (ft.tapes 632 (by decide)) ha.count
  · simpa only [hout.1] using bt 631 (by decide)
  · simpa only [hout.2,zero_word_iff_blank] using bt 633 (by decide)

theorem program_executes (N : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank allIds (fun _ => 0) s.val) (hz : NatAssign.Scratch s.val)
    (ha : InputReady N s.val) :
    ∃cost t,Executes input tape program cost s t ∧ cost≤costBound N ∧
      NatAssign.Bank allIds (finalValues N) t.val ∧ NatAssign.Scratch t.val ∧
      InputReady N t.val ∧ BinaryPrecision.Frame fullWorkspace s.val t.val := by
  obtain ⟨c0,u,e0,h0,zu,au,z633,f0⟩ := setup_executes N input tape s hz ha
  have bu : NatAssign.Bank allIds (fun _ => 0) u.val := by
    intro i hi
    have hne : i∉NatAssign.changes setup :=
      Finset.disjoint_left.mp (show Disjoint allIds (NatAssign.changes setup) by decide) hi
    exact word_of_eq (f0.tapes i hne) (hs i hi)
  obtain ⟨c1,r,e1,h1,br,zr,ar,f1⟩ := core_executes N input tape u bu zu au
  obtain ⟨origin,hw⟩ := ar.terms
  obtain ⟨t,e2,zt,f2⟩ := RuntimeCounter.clear_executes 631 input tape (N+6).bits origin r hw
  have ff : BinaryPrecision.Frame fullWorkspace s.val t.val :=
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))
  refine ⟨c0+(c1+(6*(N+6).bits.length+4)),t,e0.seq (e1.seq e2),?_,?_,?_,
    ⟨word_of_eq (ff.tapes 630 (by decide)) ha.precision,?_,?_,zt,?_,?_⟩,ff⟩
  · unfold costBound
    omega
  · intro i hi
    have hn : i≠631 := by intro he;subst i;exact (show 631∉allIds by decide) hi
    exact word_of_eq (f2.tapes i (by simpa using hn)) (br i hi)
  · intro i hi
    exact blank_of_eq (f2.tapes i (by simp only [Finset.mem_singleton];omega)) (zr i hi)
  · exact blank_of_eq (f2.tapes 619 (by decide)) ar.index
  · exact blank_of_eq (f2.tapes 628 (by decide)) ar.two
  · exact blank_of_eq (f2.tapes 632 (by decide)) ar.count
  · exact blank_of_eq (f2.tapes 633 (by decide))
      (blank_of_eq (f1.tapes 633 (by decide)) z633)

#print axioms program_executes
end Maxwell.Continuum.Machin.Runtime
