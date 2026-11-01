import Maxwell.Continuum.RationalDataflowStoredParts
import Maxwell.Cost.Structured.NatAssign.Values
import Maxwell.Cost.Structured.WordCleanup

/-! The final edge midpoint gives the physical energy after subtracting the
actual reciprocal squared length. Signed numerator parts are retained for
later canonical serialization. All overwritten words are charged. -/
namespace Maxwell.Continuum.Calibration.EdgeEnergy
open Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def result (p : Parts) (L : ℕ) : Parts :=
  ⟨p.positive*L^2,p.negative*L^2+p.denominator,p.denominator*L^2⟩

theorem result_valid {p : Parts} {L : ℕ} (hp : p.Valid) (hL : 0<L) : (result p L).Valid :=
  Nat.mul_pos hp (Nat.pow_pos hL)

theorem result_value {p : Parts} {L : ℕ} (hp : p.Valid) (hL : 0<L) :
    (result p L).value=p.value-(L:ℚ)⁻¹^2 := by
  have pd : (p.denominator:ℚ)≠0 := by exact_mod_cast hp.ne'
  have ld : (L:ℚ)≠0 := by exact_mod_cast hL.ne'
  unfold result Parts.value
  push_cast
  field_simp
  ring

theorem result_width {p : Parts} {L B : ℕ} (hp : p.Width B) (hL : L.bits.length ≤ B) :
    (result p L).Width (3*B+1) := by
  have square : (L^2).bits.length ≤ 2*B := by
    rw [pow_two]
    exact (bits_mul_le L L).trans (by omega)
  have mul (x : ℕ) (hx : x.bits.length ≤ B) : (x*L^2).bits.length ≤ 3*B :=
    (bits_mul_le x _).trans (by omega)
  have add := (bits_add_le (p.negative*L^2) p.denominator).trans
    (Nat.add_le_add_right (max_le (mul _ hp.2.1) (hp.2.2.trans (by omega : B ≤ 3*B))) 1)
  exact ⟨(mul _ hp.1).trans (Nat.le_succ _),add,(mul _ hp.2.2).trans (Nat.le_succ _)⟩

def outputList : List ℕ := [860,1711,1712,1713]
def outputs : Finset ℕ := outputList.toFinset
def inputs : Finset ℕ := {867,7906,7907,7908}
def ids : Finset ℕ := inputs∪outputs
def work : Finset ℕ := {0,1,2,3}∪outputs
def plan : List NatAssign.Instruction :=
  [.copy 867 860,.multiply 867 860,
   .copy 7906 1711,.multiply 860 1711,
   .copy 7907 1712,.multiply 860 1712,.add 7908 1712,
   .copy 7908 1713,.multiply 860 1713]
def initial (p : Parts) (L i : ℕ) : ℕ :=
  if i=867 then L else if i=7906 then p.positive else if i=7907 then p.negative
  else if i=7908 then p.denominator else 0
def code : Code := .seq (WordCleanup.code outputList) (NatAssign.code plan)
def costBound (B H : ℕ) : ℕ := 4*(6*H+4)+1+3000*8^9*(B+2)^2

theorem values (p : Parts) (L : ℕ) :
    NatAssign.values plan (initial p L) 1711=(result p L).positive ∧
    NatAssign.values plan (initial p L) 1712=(result p L).negative ∧
    NatAssign.values plan (initial p L) 1713=(result p L).denominator := by
  simp [NatAssign.values,plan,initial,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,result]
  all_goals (repeat' constructor) <;> ring

theorem executes (p : Parts) (L B H : ℕ) (pw : p.Width B) (lw : L.bits.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (length : Word s.val 867 L) (midpoint : StoredParts.Stored (positivePort 2302) p s.val)
    (scratch : NatAssign.Scratch s.val) (old : WordCleanup.Bounded outputList H s.val) :
    ∃cost t,Executes input tape code cost s t ∧cost ≤ costBound B H ∧
      StoredParts.Stored (positivePort 237) (result p L) t.val ∧
      NatAssign.Scratch t.val ∧BinaryPrecision.Frame work s.val t.val := by
  obtain ⟨c,a,e,hc,blank,frame⟩:=WordCleanup.executes outputList H input tape s old
  have ba : NatAssign.Bank ids (initial p L) a.val := by
    intro i hi
    rcases Finset.mem_union.mp hi with hin|hout
    · simp only [inputs,Finset.mem_insert,Finset.mem_singleton] at hin
      rcases hin with rfl|rfl|rfl|rfl
      · simpa only [initial,ite_true] using word_of_eq (frame.tapes 867 (by decide)) length
      · simpa [initial,positivePort] using word_of_eq (frame.tapes 7906 (by decide)) midpoint.1
      · simpa [initial,positivePort] using word_of_eq (frame.tapes 7907 (by decide)) midpoint.2.1
      · simpa [initial,positivePort] using word_of_eq (frame.tapes 7908 (by decide)) midpoint.2.2
    · have zero : initial p L i=0 := by
        simp only [outputs,outputList,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hout
        rcases hout with rfl|rfl|rfl|rfl <;> rfl
      rw [zero]
      exact (zero_word_iff_blank _ _).mpr (blank i (List.mem_toFinset.mp hout))
  have wa : ∀i∈ids,(initial p L i).bits.length ≤ B := by
    intro i _
    unfold initial
    split_ifs <;> first | exact lw | exact pw.1 | exact pw.2.1 | exact pw.2.2 | simp
  have za : NatAssign.Scratch a.val := by
    intro i hi
    exact blank_of_eq (frame.tapes i (by simp [outputList];omega)) (scratch i hi)
  have valid : ∀q∈plan,q.Valid ids := by
    simp [plan,NatAssign.Instruction.Valid,ids,inputs,outputs,outputList]
  obtain ⟨d,t,ed,hd,bt,zt,ft⟩:=NatAssign.executes ids (by decide +kernel) plan valid
    (initial p L) input tape a ba za
  have price:=NatAssign.price_bound ids plan valid (initial p L) B wa
    (by simp [plan,NatAssign.Instruction.literalWidth])
  have fields:=values p L
  refine ⟨c+d,t,e.seq ed,Nat.add_le_add hc (hd.trans price),?_,zt,
    (frame.mono Finset.subset_union_right).trans (ft.mono (by decide +kernel))⟩
  exact ⟨fields.1 ▸ bt 1711 (by decide),fields.2.1 ▸ bt 1712 (by decide),
    fields.2.2 ▸ bt 1713 (by decide)⟩

#print axioms executes
#print axioms result_value
end Maxwell.Continuum.Calibration.EdgeEnergy
