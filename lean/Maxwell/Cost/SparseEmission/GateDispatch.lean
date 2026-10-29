import Maxwell.Cost.SparseEmission.GateEmit
import Maxwell.Cost.SparseEmission.GateBinding

namespace Maxwell.Cost.SparseEmission.GateDispatch
open Structured ReadGate GateEmit

def code : Code :=
  .branch 40 addCode
    (.branch 41
      (.branch 42 (scaleCode true false) (scaleCode false false))
      (.branch 42 (scaleCode true true) zeroCode))

def group (kind : Kind) (row : List Bool) (width : ℕ) : List Bool :=
  diagonal row ++ match kind with
  | .zero => []
  | .half _ => offDiagonal row (kind.leftWord width) true true
  | .negative _ => offDiagonal row (kind.leftWord width) false false
  | .copy _ => offDiagonal row (kind.leftWord width) true false
  | .add _ _ => offDiagonal row (kind.leftWord width) true false ++
      offDiagonal row (kind.rightWord width) true false

theorem group_entries (kind : Kind) (width id : ℕ) :
    group kind (SourceCircuit.fixedWidth width id) width =
      entriesWire width (kind.record.entries id) := by
  cases kind <;> norm_num [group,diagonal,offDiagonal,entriesWire,entryWire,valueBits,
    Kind.record,Kind.leftWord,Kind.rightWord,Kind.left,Kind.right,
    Logical.GateRecord.entries,List.append_assoc]

theorem executes (kind : Kind) (input : List Bool) (randomTape : ℕ → Bool)
    (row clock preceding : List Bool) (origin rowOrigin clockOrigin : ℤ) (s : Store)
    (hc : clock.length = row.length) (hctx : Context row clock rowOrigin clockOrigin s)
    (ha : s.val.tapes 110 = BitTape.shifted preceding origin)
    (hl : s.val.tapes 111 = if kind.a || kind.b || kind.c then
      BitTape.atEnd (kind.leftWord row.length) else BitTape.blank)
    (hr : s.val.tapes 112 = if kind.a then
      BitTape.atEnd (kind.rightWord row.length) else BitTape.blank)
    (ht : Tags s.val kind.a kind.b kind.c) :
    ∃ cost t, cost ≤ 170*row.length+186 ∧ Executes input randomTape code cost s t ∧
      t.val.tapes 110 = BitTape.shifted (group kind row row.length++preceding)
        (origin-(group kind row row.length).length) ∧
      t.val.tapes 111 = BitTape.blank ∧ t.val.tapes 112 = BitTape.blank ∧
      Context row clock rowOrigin clockOrigin t ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      SourceCircuit.Frame work s.val t.val ∧ (∀ i, i ∉ work → t.val.tapes i = s.val.tapes i) := by
  cases kind with
  | zero =>
    simp only [Kind.a,Kind.b,Kind.c,Bool.false_or,Bool.false_eq_true,↓reduceIte] at hl hr ht
    obtain ⟨t,et,ta,t111,tc,taA,tm,tf,tk⟩ := zero_executes input randomTape row clock preceding
      origin rowOrigin clockOrigin s hc hctx ha hl
    refine ⟨1+(1+(1+(70*row.length+75))),t,by omega,
      Executes.no ht.1 (Executes.no ht.2.1 (Executes.no ht.2.2 et)),?_,t111,
      (tk 112 (by decide)).trans hr,tc,taA,tm,tf.mono (by decide),?_⟩
    · simpa [group,diagonal,List.length_append,List.length_cons,List.length_nil,Nat.cast_add,
        Nat.cast_mul,two_mul,add_assoc] using ta
    · intro i hi; exact tk i (by simp_all [work,unaryWork])
  | half parent =>
    simp only [Kind.a,Kind.b,Kind.c,Bool.false_or,Bool.false_eq_true,↓reduceIte] at hl hr ht
    obtain ⟨t,et,ta,t111,tc,taA,tm,tf,tk⟩ := scale_executes true true input randomTape row
      ((Kind.half parent).leftWord row.length) clock preceding origin rowOrigin clockOrigin s
      (by simp) hc hctx ha hl
    refine ⟨1+(1+(1+(120*row.length+129))),t,by omega,
      Executes.no ht.1 (Executes.no ht.2.1 (Executes.yes ht.2.2 et)),?_,t111,
      (tk 112 (by decide)).trans hr,tc,taA,tm,tf.mono (by decide),?_⟩
    · convert ta using 1; simp [group,diagonal,offDiagonal,List.append_assoc];
        congr 1; ring
    · intro i hi; exact tk i (by simp_all [work,unaryWork])
  | negative parent =>
    simp only [Kind.a,Kind.b,Kind.c,Bool.false_or,Bool.true_or,Bool.false_eq_true,↓reduceIte] at hl hr ht
    obtain ⟨t,et,ta,t111,tc,taA,tm,tf,tk⟩ := scale_executes false false input randomTape row
      ((Kind.negative parent).leftWord row.length) clock preceding origin rowOrigin clockOrigin s
      (by simp) hc hctx ha hl
    refine ⟨1+(1+(1+(120*row.length+129))),t,by omega,
      Executes.no ht.1 (Executes.yes ht.2.1 (Executes.no ht.2.2 et)),?_,t111,
      (tk 112 (by decide)).trans hr,tc,taA,tm,tf.mono (by decide),?_⟩
    · convert ta using 1; simp [group,diagonal,offDiagonal,List.append_assoc];
        congr 1; ring
    · intro i hi; exact tk i (by simp_all [work,unaryWork])
  | copy parent =>
    simp only [Kind.a,Kind.b,Kind.c,Bool.false_or,Bool.true_or,Bool.false_eq_true,↓reduceIte] at hl hr ht
    obtain ⟨t,et,ta,t111,tc,taA,tm,tf,tk⟩ := scale_executes true false input randomTape row
      ((Kind.copy parent).leftWord row.length) clock preceding origin rowOrigin clockOrigin s
      (by simp) hc hctx ha hl
    refine ⟨1+(1+(1+(120*row.length+129))),t,by omega,
      Executes.no ht.1 (Executes.yes ht.2.1 (Executes.yes ht.2.2 et)),?_,t111,
      (tk 112 (by decide)).trans hr,tc,taA,tm,tf.mono (by decide),?_⟩
    · convert ta using 1; simp [group,diagonal,offDiagonal,List.append_assoc];
        congr 1; ring
    · intro i hi; exact tk i (by simp_all [work,unaryWork])
  | add left right =>
    simp only [Kind.a,Kind.b,Kind.c,Bool.true_or,↓reduceIte] at hl hr ht
    obtain ⟨t,et,ta,t111,t112,tc,taA,tm,tf,tk⟩ := add_executes input randomTape row
      ((Kind.add left right).leftWord row.length) ((Kind.add left right).rightWord row.length)
      clock preceding origin rowOrigin clockOrigin s (by simp) (by simp) hc hctx ha hl hr
    refine ⟨1+(170*row.length+183),t,by omega,Executes.yes ht.1 et,?_,t111,t112,tc,taA,tm,tf,tk⟩
    convert ta using 1; simp [group,diagonal,offDiagonal,List.append_assoc];
      congr 1; ring

end Maxwell.Cost.SparseEmission.GateDispatch
