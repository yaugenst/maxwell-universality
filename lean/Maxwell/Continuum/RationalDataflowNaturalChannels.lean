import Maxwell.Continuum.NaturalBankImportWord
import Maxwell.Continuum.RationalDataflowProgram

/-! Literal runtime words can supply rational channels directly. In
particular, a padded loop counter is copied and normalized, without a
host-generated rational input table. -/
namespace Maxwell.Continuum.RationalDataflow.NaturalChannel
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000

inductive Channel where
  | positive | negative | denominator
  deriving DecidableEq, Repr

def port : Channel→ℕ→ℕ
  | .positive => positivePort
  | .negative => negativePort
  | .denominator => denominatorPort

def replace : Channel→Parts→ℕ→Parts
  | .positive,x,n => ⟨n,x.negative,x.denominator⟩
  | .negative,x,n => ⟨x.positive,n,x.denominator⟩
  | .denominator,x,n => ⟨x.positive,x.negative,n⟩

def code (channel : Channel) (source target : ℕ) : Code := NaturalImport.code source (port channel target)

theorem port_ge (channel : Channel) (target : ℕ) : 1000≤port channel target := by
  cases channel
  · exact positivePort_ge _
  · exact negativePort_ge _
  · exact denominatorPort_ge _

theorem port_mem (channel : Channel) (S : Finset ℕ) (target : ℕ) (ht : target∈S) :
    port channel target∈ids S := by
  apply cell_mem ht
  cases channel <;> simp [port,cellPorts]

theorem replace_dataValues (channel : Channel) (v : ℕ→Parts) (target n : ℕ) :
    Function.update (dataValues v) (port channel target) n=
      dataValues (Function.update v target (replace channel (v target) n)) := by
  rw [←writeParts_dataValues]
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  ext i
  by_cases hip : i=positivePort target
  · subst i
    cases channel <;> simp [writeParts,port,replace,positivePort,negativePort,denominatorPort] <;>
      exact dataValues_positive v target
  by_cases hin : i=negativePort target
  · subst i
    cases channel <;> simp [writeParts,port,replace,positivePort,negativePort,denominatorPort] <;>
      exact dataValues_negative v target
  by_cases hid : i=denominatorPort target
  · subst i
    cases channel <;> simp [writeParts,port,replace,positivePort,negativePort,denominatorPort] <;>
      exact dataValues_denominator v target
  cases channel <;> simp [writeParts,port,replace,hip,hin,hid]

theorem executes (S : Finset ℕ) (channel : Channel) (source target : ℕ)
    (ht : target∈S) (hne : source≠port channel target) (v : ℕ→Parts) (xs : List Bool)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready S v s)
    (hx : BankArray.Word s.val source xs) :
    ∃cost t,Executes input tape (code channel source target) cost s t ∧
      cost≤6*(dataValues v (port channel target)).bits.length+31*xs.length+39 ∧
      Ready S (Function.update v target (replace channel (v target) (addressValue xs))) t ∧
      BinaryPrecision.Frame {port channel target} s.val t.val := by
  obtain ⟨cost,t,he,hc,hb,hf⟩ := NaturalImport.executes (ids S) source (port channel target)
    (port_mem channel S target ht) hne (dataValues v) xs input tape s hr.1 hx
  rw [replace_dataValues] at hb
  refine ⟨cost,t,he,hc,⟨hb,?_⟩,hf⟩
  intro i hi
  apply blank_of_eq (hf.tapes i _) (hr.2 i hi)
  simp only [Finset.mem_singleton]
  have hg := port_ge channel target
  omega

#print axioms executes
end Maxwell.Continuum.RationalDataflow.NaturalChannel
