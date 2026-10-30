import Maxwell.Continuum.SourceRoutingPathLoaded

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryPath
open Structured GeometryArithmetic GeometrySort Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

def prepareBound {q : ℕ} (p : Plan q) (round level cursor : ℕ) : ℕ :=
  p.bound round+level.bits.length+cursor.bits.length+32

def prepareCode (transpose : Bool) : Code := .seq advanceProgram.code
  (.seq (loadCode 1255 1233) (.seq (loadCode 1253 1234) (originProgram transpose).code))

theorem prepare_executes {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) (level cursor : ℕ) (transpose : Bool)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank GeometryArithmetic.ids (decision p round saved i) s.val)
    (ready : GeometryArray.Ready s.val) (privateBlank : Blank s.val 1249)
    (levelWord : Word s.val 1255 level) (cursorWord : Word s.val 1253 cursor) :
    ∃steps t,Executes input tape (prepareCode transpose) steps s t ∧
      steps ≤ 2^224*(prepareBound p round level cursor+3)^2 ∧
      NatAssign.Bank GeometryArithmetic.ids (emissionValues p round saved i level cursor transpose) t.val ∧
      GeometryArray.Ready t.val ∧ Blank t.val 1249 ∧ BinaryPrecision.Frame work s.val t.val := by
  let B:=prepareBound p round level cursor
  have pbound : p.bound round ≤ B := by dsimp only [B,prepareBound];omega
  have levelBound : level.bits.length ≤ B := by dsimp only [B,prepareBound];omega
  have cursorBound : cursor.bits.length ≤ B := by dsimp only [B,prepareBound];omega
  have wide : B ≤ 2^34*(B+3) := by omega
  have widthA : ∀j∈ids,(advanced p round saved i j).bits.length ≤ 2^34*(B+3) :=
    fun j hj => (advanced_width p round saved fit i j hj).trans (Nat.mul_le_mul_left _ (by omega))
  obtain ⟨c0,a,e0,h0,ba,za,a1249,f0⟩:=advance_executes p round saved fit i input tape s bank ready privateBlank
  obtain ⟨c1,b,e1,h1,bb,zb,b1249,f1⟩:=load_executes 1255 1233 (by decide) (by decide)
    (advanced p round saved i) level input tape a ba za a1249
    (RationalAccumulator.word_of_eq (f0.tapes 1255 (by decide)) levelWord)
  obtain ⟨c2,c,e2,h2,bc,zc,c1249,f2⟩:=load_executes 1253 1234 (by decide) (by decide)
    (Function.update (advanced p round saved i) 1233 level) cursor input tape b bb zb b1249
    (RationalAccumulator.word_of_eq ((f1.tapes 1253 (by decide)).trans (f0.tapes 1253 (by decide))) cursorWord)
  have widthC:=pathLoaded_width (advanced p round saved i) level cursor (2^34*(B+3))
    widthA (levelBound.trans wide) (cursorBound.trans wide)
  obtain ⟨c3,t,e3,h3,bt,zt,t1249,f3⟩:=origin_executes transpose
    (pathLoaded (advanced p round saved i) level cursor) (2^34*(B+3)) (by omega)
    (pathLoaded_zero _ level cursor (advanced_zero p round saved i)) widthC input tape c bc zc c1249
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,bt,zt,t1249,
    f0.trans ((f1.mono (by decide)).trans ((f2.mono (by decide)).trans f3))⟩
  have first:=h0.trans (Nat.mul_le_mul_left (2^184) (Nat.pow_le_pow_left (show p.bound round+3 ≤ B+3 by omega) 2))
  have w33:=widthA 1233 (by decide)
  have w34:=widthA 1234 (by decide)
  simp only [Function.update_of_ne (by decide : (1234 : ℕ)≠1233)] at h2
  have last : c3 ≤ 2^222*(B+3)^2 := calc
    c3 ≤ 2^152*(2^34*(B+3)+2)^2 := h3
    _ ≤ 2^152*(2^35*(B+3))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = 2^222*(B+3)^2 := by ring
  change c0+(c1+(c2+c3)) ≤ 2^224*(B+3)^2
  nlinarith only [first,h1,h2,w33,w34,levelBound,cursorBound,last]

private theorem emission_width_arithmetic (B : ℕ) : 2^14*(2^34*(B+3)+1) ≤ 2^49*(B+3) := by omega

theorem emission_width {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q)
    (fit : Fits p.width saved) (i : Fin (q*q)) (level cursor : ℕ) (transpose : Bool) :
    ∀j∈GeometryArithmetic.ids,(emissionValues p round saved i level cursor transpose j).bits.length ≤
      2^49*(prepareBound p round level cursor+3) := by
  let B:=prepareBound p round level cursor
  have pbound : p.bound round ≤ B := by dsimp only [B,prepareBound];omega
  have levelBound : level.bits.length ≤ B := by dsimp only [B,prepareBound];omega
  have cursorBound : cursor.bits.length ≤ B := by dsimp only [B,prepareBound];omega
  have wide : B ≤ 2^34*(B+3) := by omega
  have widthA : ∀j∈ids,(advanced p round saved i j).bits.length ≤ 2^34*(B+3) :=
    fun j hj => (advanced_width p round saved fit i j hj).trans (Nat.mul_le_mul_left _ (by omega))
  have h:=origin_width transpose (pathLoaded (advanced p round saved i) level cursor) (2^34*(B+3))
    (by omega) (pathLoaded_width _ level cursor _ widthA (levelBound.trans wide) (cursorBound.trans wide))
  intro j hj
  exact (h j hj).trans (emission_width_arithmetic B)

#print axioms prepare_executes
#print axioms emission_width
end Maxwell.Cost.RoutingPorts.Complete.GeometryPath
