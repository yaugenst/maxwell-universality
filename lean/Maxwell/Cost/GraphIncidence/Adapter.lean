import Maxwell.Cost.PositiveGraph.Metadata.Plan
import Maxwell.Cost.IncidencePass.Loop
import Maxwell.Cost.Structured.WordAssign
import Maxwell.Cost.SparseEmission.Prepend

namespace Maxwell.Cost.GraphIncidence
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def destinations : List ℕ := [80,81,82,83,84,85,86,87,88,89,90,92]
def sources : List ℕ := [140,143,144,146,149,151,142]
def ids : List ℕ := destinations++sources

def assignments : List WordAssign.Assignment := [
  (140,80),(151,81),(151,82),(146,83),(149,84),(143,85),(144,86),
  (151,87),(151,88),(151,89),(151,90),(142,92)]

def initial (width dimension count : ℕ) (clock : List Bool) (old : ℕ → List Bool) (i : ℕ) : List Bool :=
  if i=140 then (width+3).bits else
  if i=143 then (4*count*(width+3)).bits else
  if i=144 then (4*count*(width+3)+2*(2*dimension+count)).bits else
  if i=146 then clock else
  if i=149 then (2:ℕ).bits else
  if i=151 then [] else
  if i=142 then (4*count).bits else old i

def layout (width dimension count : ℕ) : IncidenceEncoding.Layout :=
  ⟨width+3,0,4*count*(width+3),4*count*(width+3)+2*(2*dimension+count)⟩

def code : Code := .seq (WordAssign.code assignments) (SparseEmission.Prepend.literals 87 [false,false])
def price (width dimension count : ℕ) (clock : List Bool) (old : ℕ → List Bool) : ℕ :=
  WordAssign.price assignments (initial width dimension count clock old)+13

theorem valid : WordAssign.Valid ids assignments := by
  simp [WordAssign.Valid,assignments,ids,destinations,sources]

theorem initial_bank (width dimension count : ℕ) (clock : List Bool) (old : ℕ → List Bool)
    (s : BitRAMState) (numeric : PositiveGraph.Metadata.Numeric width dimension count s)
    (hclock : Word s 146 clock) (hold : WordAssign.Bank destinations s old) :
    WordAssign.Bank ids s (initial width dimension count clock old) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · have hlo : i<140 := by
      simp only [destinations,List.mem_cons,List.not_mem_nil,or_false] at hi
      omega
    simpa only [initial,show i≠140 by omega,show i≠143 by omega,show i≠144 by omega,
      show i≠146 by omega,show i≠149 by omega,show i≠151 by omega,show i≠142 by omega,ite_false]
      using hold i hi
  · simp only [sources,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [initial,Word,RationalAccumulator.Word] using numeric.widthWord
    · simpa [initial,Word,RationalAccumulator.Word] using numeric.counterBase
    · simpa [initial,Word,RationalAccumulator.Word] using numeric.rankBase
    · simp [initial]; exact hclock
    · simpa [initial,Word,RationalAccumulator.Word] using numeric.two
    · simpa [initial,Word,RationalAccumulator.Word] using numeric.endpointBase
    · simpa [initial,Word,RationalAccumulator.Word] using numeric.incidences

/-- Install the graph's executed descriptors, clear the actual old routing
banks, and initialize the physical two-symbol clock. -/
theorem executes (width dimension count : ℕ) (clock : List Bool) (old : ℕ → List Bool)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (numeric : PositiveGraph.Metadata.Numeric width dimension count s.val)
    (hclock : Word s.val 146 clock) (hold : WordAssign.Bank destinations s.val old)
    (scratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) :
    ∃ t, Executes input tape code (price width dimension count clock old) s t ∧
      IncidencePass.Config (layout width dimension count) [] clock t.val ∧
      IncidencePass.Workspace t.val ∧ Word t.val 92 (4*count).bits ∧
      t.val.memory=s.val.memory ∧ t.val.address=s.val.address ∧
      SourceCircuit.Frame destinations.toFinset s.val t.val := by
  obtain ⟨a,ea,ab,af⟩ := WordAssign.executes assignments ids input tape
    (initial width dimension count clock old) valid s (initial_bank width dimension count clock old s.val numeric hclock hold)
  have getWord (i : ℕ) (hi : i∈destinations) := ab i (List.mem_append_left _ hi)
  have azero (i : ℕ) (hi : i=81 ∨ i=82 ∨ i=87 ∨ i=88 ∨ i=89 ∨ i=90) : Word a.val i [] := by
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · convert getWord 81 (by decide) using 1; norm_num [WordAssign.values,assignments,initial,Function.update_apply]
    · convert getWord 82 (by decide) using 1; norm_num [WordAssign.values,assignments,initial,Function.update_apply]
    · convert getWord 87 (by decide) using 1; norm_num [WordAssign.values,assignments,initial,Function.update_apply]
    · convert getWord 88 (by decide) using 1; norm_num [WordAssign.values,assignments,initial,Function.update_apply]
    · convert getWord 89 (by decide) using 1; norm_num [WordAssign.values,assignments,initial,Function.update_apply]
    · convert getWord 90 (by decide) using 1; norm_num [WordAssign.values,assignments,initial,Function.update_apply]
  obtain ⟨origin,a87⟩ := azero 87 (by omega)
  obtain ⟨t,et,ttapes,ta,tm,tf⟩ := SparseEmission.Prepend.literals_executes 87 [false,false] [] origin input tape a a87
  have keepT (i : ℕ) (hi : i≠87) : t.val.tapes i=a.val.tapes i := by simp [ttapes,hi]
  have updated (i : ℕ) (hi : i∈destinations) (hn : i≠87) := BankArray.word_of_eq (keepT i hn) (getWord i hi)
  have config : IncidencePass.Config (layout width dimension count) [] clock t.val := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,⟨origin-2,by simp [ttapes]⟩⟩
    · convert updated 80 (by decide) (by omega) using 1; norm_num [layout,WordAssign.values,assignments,initial,Function.update_apply]
    · convert updated 81 (by decide) (by omega) using 1; norm_num [layout,WordAssign.values,assignments,initial,Function.update_apply]
    · convert updated 82 (by decide) (by omega) using 1; norm_num [layout,WordAssign.values,assignments,initial,Function.update_apply]
    · convert updated 83 (by decide) (by omega) using 1; norm_num [layout,WordAssign.values,assignments,initial,Function.update_apply]
    · convert updated 84 (by decide) (by omega) using 1; norm_num [layout,WordAssign.values,assignments,initial,Function.update_apply]
    · convert updated 85 (by decide) (by omega) using 1; norm_num [layout,WordAssign.values,assignments,initial,Function.update_apply]
    · convert updated 86 (by decide) (by omega) using 1; norm_num [layout,WordAssign.values,assignments,initial,Function.update_apply]
  have keep (i : ℕ) (hi : i<10) : t.val.tapes i=s.val.tapes i :=
    (keepT i (by omega)).trans (af.2.2.2.2.2.1 i (by simp [assignments]; omega))
  have blank (i : ℕ) (hi : i=88 ∨ i=89 ∨ i=90) : Blank t.val i := by
    apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    exact BankArray.word_of_eq (keepT i (by omega)) (azero i (by omega))
  have frameA : SourceCircuit.Frame destinations.toFinset s.val a.val := by
    refine ⟨af.2.1,af.2.2.2.1,af.2.2.2.2.1,?_,?_,?_⟩
    · intro i _ hi
      apply af.2.2.2.2.2.1 i
      simpa only [assignments,List.map_cons,List.map_nil,destinations,List.mem_toFinset] using hi
    · exact af.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)
    · intro i hi
      exact af.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)
  refine ⟨t,?_,config,⟨SourceCircuit.scratch_of_tapes scratch keep,
    RationalAccumulator.blank_of_eq (keep 7 (by omega)) h7,blank 88 (by omega),blank 89 (by omega),blank 90 (by omega)⟩,
    ?_,tm.trans af.2.2.1,ta.trans af.1,frameA.trans (tf.mono (by simp [destinations]))⟩
  · simpa only [code,price,List.length_cons,List.length_nil] using ea.seq et
  · convert updated 92 (by simp [destinations]) (by omega) using 1; norm_num [WordAssign.values,assignments,initial,Function.update_apply]

end Maxwell.Cost.GraphIncidence
