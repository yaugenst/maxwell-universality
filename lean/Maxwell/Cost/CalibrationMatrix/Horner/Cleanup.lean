import Maxwell.Cost.CalibrationMatrix.Horner.Multiply
import Maxwell.Cost.Structured.WordCleanup

/-! Stored matrix descriptors already carry the concrete bounded words
needed to charge their cleanup. No fresh-workspace assumption is required. -/
namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured

def metadataCleanup : List ℕ := [100,101,110,111]++List.range' 120 14
def portCleanup : List ℕ := [112,113,114,115]
def workCleanup : List ℕ := [107,108,109]
def activeCleanup : List ℕ := workCleanup++[110,111]++portCleanup++List.range' 120 14

private theorem baseBank_covers (i : ℕ) (lo : 120≤ i) (hi : i≤133)
    (h126 : i≠126) (h127 : i≠127) : ∃j : Fin 12,baseBank j=i := by
  let j:=if i<126 then i-120 else if i<130 then i-122 else if i<132 then i-120 else i-124
  have hj : j<12 := by dsimp [j];split_ifs <;> omega
  refine ⟨⟨j,hj⟩,?_⟩
  unfold baseBank
  dsimp only
  dsimp [j]
  split_ifs <;> omega

theorem Stored.bounded_metadata {n B : ℕ} {d : Data n} {values : Fin 12→Vector (List Bool) n}
    {s : BitRAMState} (h : Stored d values s) (size : d.Sized B) :
    WordCleanup.Bounded metadataCleanup B s := by
  intro i hi
  simp only [metadataCleanup,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    List.mem_range'_1] at hi
  rcases hi with (rfl|rfl|rfl|rfl)|⟨lo,hi⟩
  · exact ⟨d.width,size.1,h.width⟩
  · exact ⟨d.clock,d.clock_length ▸ size.2.1,h.clock⟩
  · exact ⟨d.matrixPositiveBase,size.2.2.1,h.matrixPositiveBase⟩
  · exact ⟨d.matrixNegativeBase,size.2.2.2.1,h.matrixNegativeBase⟩
  · by_cases eq : i=126
    · subst i;exact ⟨d.K.bits,size.2.2.2.2.2.1,h.K⟩
    by_cases eq' : i=127
    · subst i;exact ⟨d.S.bits,size.2.2.2.2.2.2,h.S⟩
    obtain ⟨j,rfl⟩:=baseBank_covers i lo (by omega) eq eq'
    exact ⟨d.bases j,size.2.2.2.2.1 j,h.bases j⟩

theorem Ports.bounded {n B : ℕ} {d : Data n} {ip iq op oq : Fin 12} {s : BitRAMState}
    (h : Ports d ip iq op oq s) (size : d.Sized B) : WordCleanup.Bounded portCleanup B s := by
  intro i hi
  simp only [portCleanup,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl
  · exact ⟨d.bases ip,size.2.2.2.2.1 ip,h.inputPositive⟩
  · exact ⟨d.bases iq,size.2.2.2.2.1 iq,h.inputNegative⟩
  · exact ⟨d.bases op,size.2.2.2.2.1 op,h.outputPositive⟩
  · exact ⟨d.bases oq,size.2.2.2.2.1 oq,h.outputNegative⟩

theorem WorkReady.bounded {count : List Bool} {B : ℕ} {s : BitRAMState}
    (h : WorkReady count B s) (countWidth : count.length≤B) : WordCleanup.Bounded workCleanup B s := by
  obtain ⟨_,_,_,_,_,_,stored,_,_,empty108,empty109⟩:=h
  intro i hi
  simp only [workCleanup,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl
  · exact ⟨count,countWidth,stored⟩
  · exact ⟨[],Nat.zero_le _,(RationalAccumulator.zero_word_iff_blank _ _).mpr empty108⟩
  · exact ⟨[],Nat.zero_le _,(RationalAccumulator.zero_word_iff_blank _ _).mpr empty109⟩

theorem bounded_active {n B : ℕ} {d : Data n} {values : Fin 12→Vector (List Bool) n}
    {ip iq op oq : Fin 12} {count : List Bool} {s : BitRAMState}
    (work : WorkReady count B s) (stored : Stored d values s) (ports : Ports d ip iq op oq s)
    (size : d.Sized B) (countWidth : count.length≤B) : WordCleanup.Bounded activeCleanup B s := by
  intro i hi
  have hw:=work.bounded countWidth
  have hs:=stored.bounded_metadata size
  have hp:=ports.bounded size
  simp only [activeCleanup,List.mem_append] at hi
  rcases hi with ((hi|hi)|hi)|hi
  · exact hw i hi
  · apply hs i
    simp only [metadataCleanup,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
    tauto
  · exact hp i hi
  · exact hs i (List.mem_append_right _ hi)

#print axioms bounded_active
end Maxwell.Cost.CalibrationMatrix.Horner
