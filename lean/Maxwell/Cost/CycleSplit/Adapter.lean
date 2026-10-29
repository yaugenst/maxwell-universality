import Maxwell.Cost.DoublingPass.Round
import Maxwell.Cost.DecoderConstants.Helpers
import Maxwell.Cost.ColorPass.Correctness

namespace Maxwell.Cost.CycleSplit
open Structured DoublingPass
open RationalAccumulator (Blank)
open BankArray (Word)

/-- The color pass reads the original pairing, the computed minimum array,
and writes one bit per token into the former jump scratch buffer. -/
def colorLayout (layout : Layout) (pairingBase : ℕ) : Layout :=
  ⟨layout.width,pairingBase,layout.oldMinimum,layout.newJump,1⟩

def adapterCode : Code := .seq (.call (TapeOps.clear 82))
  (.seq (.call (WordTransfer.clone 98 82))
  (.seq (.call (TapeOps.clear 86)) (.call (DecoderConstants.oneProgram 86))))

def adapterCost (layout : Layout) (pairingBase : ℕ) : ℕ :=
  6*layout.oldJump.bits.length+15*pairingBase.bits.length+6*layout.newMinimum.bits.length+28

theorem adapter_executes (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (pairingBase : ℕ) (clock : List Bool) (s : Store)
    (cfg : Config layout [] clock s.val) (pairing : Word s.val 98 pairingBase.bits)
    (work : Workspace s.val) :
    ∃ t, Executes input tape adapterCode (adapterCost layout pairingBase) s t ∧
      Config (colorLayout layout pairingBase) [] clock t.val ∧ Workspace t.val ∧
      t.val.memory=s.val.memory ∧
      (∀ i, i≠82 → i≠86 → t.val.tapes i=s.val.tapes i) ∧ RoundFrame s.val t.val := by
  obtain ⟨jo,hj⟩ := cfg.oldJump
  obtain ⟨ao,ha⟩ := pairing
  obtain ⟨mo,hm⟩ := cfg.newMinimum
  obtain ⟨c,ec,ct,cf⟩ := WordCall.clear 82 input tape layout.oldJump.bits jo s hj
  obtain ⟨d,ed,dt,df⟩ := WordCall.clone 98 82 (by omega) input tape pairingBase.bits ao
    (jo+layout.oldJump.bits.length) c (by simpa [ct] using ha) (by simp [ct])
  obtain ⟨e,ee,et,ef⟩ := WordCall.clear 86 input tape layout.newMinimum.bits mo d (by simpa [dt,ct] using hm)
  have e86 : Blank e.val 86 := ⟨mo+layout.newMinimum.bits.length,by simp [et]⟩
  obtain ⟨eo,ow,oframe⟩ := DecoderConstants.one 86 input tape e e86
  let t := Store.ofState (DecoderConstants.oneState 86 e.val)
  have keep (i : ℕ) (h82 : i≠82) (h86 : i≠86) : t.val.tapes i=s.val.tapes i := by
    simp [t,Store.ofState,DecoderConstants.oneState,et,dt,ct,h82,h86]
  have t82 : Word t.val 82 pairingBase.bits := by
    refine ⟨jo+layout.oldJump.bits.length,?_⟩
    simp [t,Store.ofState,DecoderConstants.oneState,et,dt]
  have t86 : Word t.val 86 (1:ℕ).bits := ow
  have tc : Config (colorLayout layout pairingBase) [] clock t.val :=
    ⟨BankArray.word_of_eq (keep 80 (by omega) (by omega)) cfg.width,
     BankArray.word_of_eq (keep 81 (by omega) (by omega)) cfg.index,t82,
     BankArray.word_of_eq (keep 83 (by omega) (by omega)) cfg.clock,
     BankArray.word_of_eq (keep 84 (by omega) (by omega)) cfg.oldMinimum,
     BankArray.word_of_eq (keep 85 (by omega) (by omega)) cfg.newJump,t86⟩
  have tw : Workspace t.val := by
    rcases work with ⟨⟨w0,w1,w2,w3,w5,w6,w8,w9⟩,w7,wp⟩
    refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
    all_goals first
    | exact RationalAccumulator.blank_of_eq (keep _ (by omega) (by omega)) (by assumption)
    | exact fun i hi => RationalAccumulator.blank_of_eq
        (keep i (by dsimp [Private] at hi; omega) (by dsimp [Private] at hi; omega)) (wp i hi)
  have tm : t.val.memory=s.val.memory := oframe.2.2.1.trans (ef.2.2.1.trans (df.2.2.1.trans cf.2.2.1))
  have rf : RoundFrame s.val t.val := by
    refine ⟨oframe.2.1.trans (ef.2.1.trans (df.2.1.trans cf.2.1)),
      oframe.2.2.2.1.trans (ef.2.2.2.1.trans (df.2.2.2.1.trans cf.2.2.2.1)),
      oframe.2.2.2.2.1.trans (ef.2.2.2.2.1.trans (df.2.2.2.2.1.trans cf.2.2.2.2.1)),?_,?_⟩
    · intro i _ hp
      exact keep i (by intro he; exact hp (by simp [RoundPrivate,he]))
        (by intro he; exact hp (by simp [RoundPrivate,he]))
    · intro i hi h24 h25 h26 h27 _ _
      exact (oframe.2.2.2.2.2.2 i hi h24 h25 h26 h27).trans
        ((ef.2.2.2.2.2.2 i h26 h27).trans
          ((df.2.2.2.2.2.2 i h24 h25 h26 h27).trans (cf.2.2.2.2.2.2 i h26 h27)))
  refine ⟨t,?_,tc,tw,tm,keep,rf⟩
  convert ec.seq (ed.seq (ee.seq eo)) using 1 <;> first | rfl | dsimp [adapterCost]; omega

/-- The output interval may initially contain arbitrary bits. -/
def snapshotColors (memory : ℕ → Bool) (base n : ℕ) : Vector Bool n :=
  Vector.ofFn (fun i => memory (base+i.val))

theorem snapshotColors_represents (memory : ℕ → Bool) (base n : ℕ) :
    BitArray.Represents memory base 1 (ColorPass.colorWords (snapshotColors memory base n)) where
  length i := by simp only [ColorPass.colorWords_get,List.length_singleton]
  bits i j hj := by
    have he : j=0 := by omega
    subst j
    simp [ColorPass.colorWords,snapshotColors,Vector.get,Fin.cast]

end Maxwell.Cost.CycleSplit
