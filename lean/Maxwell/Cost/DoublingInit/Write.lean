import Maxwell.Cost.DoublingInit.Common

namespace Maxwell.Cost.DoublingInit
open Structured
open RationalAccumulator (Blank)
open BankArray (Word)

private theorem write_one {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (index clock payload : List Bool) (base baseBank payloadBank : ℕ) (i : Fin n)
    (hb : 10≤baseBank) (hp : 10≤payloadBank) (hw : 0<layout.route.width)
    (hi : addressValue index=i.val) (hlen : payload.length=layout.route.width)
    (hbase : base.bits.length≤budget layout index) (s : Store)
    (cfg : Config layout index clock s.val) (ss : BankArray.Scratch s.val)
    (baseWord : Word s.val baseBank base.bits) (payloadWord : Word s.val payloadBank payload) :
    ∃ cost t, cost≤30000*(budget layout index+1)^2 ∧
      Executes input tape (BankArray.writeCode 80 81 baseBank payloadBank) cost s t ∧
      BankArray.Scratch t.val ∧ t.val.tapes 7=s.val.tapes 7 ∧
      t.val.memory=MemoryWord.writeBits s.val.memory (base+i.val*layout.route.width) payload ∧
      Config layout index clock t.val ∧ BankArray.Frame s.val t.val := by
  obtain ⟨cost,t,hcost,he,hm,_,hs,h7,hf⟩ := BankArray.write_bank 80 81 baseBank payloadBank
    (by omega) (by omega) hb hp input tape layout.route.width.bits index base.bits payload
    (BitArray.snapshot s.val.memory base layout.route.width n) i (RationalAccumulator.bits_nonempty hw)
    hi (by simpa using hlen) s ss cfg.route.width cfg.route.index baseWord payloadWord
    (by simpa using BitArray.snapshot_represents s.val.memory base layout.route.width n)
  exact ⟨cost,t,hcost.trans (array_cost_bound layout index index payload base
    (by dsimp [budget,DoublingPass.budget]; omega) hbase (by omega)),he,hs,h7,
    by simpa using hm,cfg.of_frame (Frame.of_bank hf),hf⟩

def writeCode : Code := .seq (BankArray.writeCode 80 81 82 89)
  (.seq (BankArray.writeCode 80 81 84 37)
  (.seq (BankArray.writeCode 80 81 85 37) (BankArray.writeCode 80 81 86 37)))

theorem write_executes {n : ℕ} (input : List Bool) (tape : ℕ → Bool)
    (layout : Layout) (a b : Equiv.Perm (Fin n)) (i : Fin n) (index clock : List Bool)
    (hw : 0<layout.route.width) (hi : addressValue index=i.val)
    (s : Store) (cfg : Config layout index clock s.val) (ss : BankArray.Scratch s.val)
    (h89 : Word s.val 89 (IncidenceEncoding.word layout.route.width (a (b i)).val))
    (h37 : Word s.val 37 (IncidenceEncoding.word layout.route.width i.val)) :
    ∃ cost t, cost≤120000*(budget layout index+1)^2 ∧ Executes input tape writeCode cost s t ∧
      BankArray.Scratch t.val ∧ t.val.tapes 7=s.val.tapes 7 ∧
      t.val.memory=stepMemory layout a b i s.val.memory ∧ Config layout index clock t.val ∧
      BankArray.Frame s.val t.val := by
  let p := IncidenceEncoding.word layout.route.width (a (b i)).val
  let w := IncidenceEncoding.word layout.route.width i.val
  obtain ⟨c1,t1,hc1,e1,s1,h17,m1,cfg1,f1⟩ := write_one input tape layout index clock p
    layout.route.oldJump 82 89 i (by omega) (by omega) hw hi (by simp [p])
    (by dsimp [budget,DoublingPass.budget]; omega) s cfg ss cfg.route.oldJump h89
  obtain ⟨c2,t2,hc2,e2,s2,h27,m2,cfg2,f2⟩ := write_one input tape layout index clock w
    layout.route.oldMinimum 84 37 i (by omega) (by omega) hw hi (by simp [w])
    (by dsimp [budget,DoublingPass.budget]; omega) t1 cfg1 s1 cfg1.route.oldMinimum
    (BankArray.word_of_eq (f1.2.2.2.1 37 (by omega)) h37)
  have f12 := f1.trans f2
  obtain ⟨c3,t3,hc3,e3,s3,h37',m3,cfg3,f3⟩ := write_one input tape layout index clock w
    layout.route.newJump 85 37 i (by omega) (by omega) hw hi (by simp [w])
    (by dsimp [budget,DoublingPass.budget]; omega) t2 cfg2 s2 cfg2.route.newJump
    (BankArray.word_of_eq (f12.2.2.2.1 37 (by omega)) h37)
  have f123 := f12.trans f3
  obtain ⟨c4,t,hc4,e4,s4,h47,m4,cfg4,f4⟩ := write_one input tape layout index clock w
    layout.route.newMinimum 86 37 i (by omega) (by omega) hw hi (by simp [w])
    (by dsimp [budget,DoublingPass.budget]; omega) t3 cfg3 s3 cfg3.route.newMinimum
    (BankArray.word_of_eq (f123.2.2.2.1 37 (by omega)) h37)
  refine ⟨c1+(c2+(c3+c4)),t,by omega,e1.seq (e2.seq (e3.seq e4)),s4,
    h47.trans (h37'.trans (h27.trans h17)),?_,cfg4,f123.trans f4⟩
  rw [m4,m3,m2,m1]
  rfl

end Maxwell.Cost.DoublingInit
