import Maxwell.Continuum.RationalDataflowLayout
import Maxwell.Cost.EmitNatural

/-! Canonical signed-integer output directly from the represented Parts
channels. All tapes and memory survive the emission unchanged. -/
namespace Maxwell.Continuum.RationalDataflow.IntegerEmit
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def code (source : ℕ) : Code :=
  .seq (.atom (.readTape (negativePort source) 24 23))
    (.seq (.atom (.output 23))
      (.branch 23 (EmitNatural.code (negativePort source)) (EmitNatural.code (positivePort source))))

def readState (source : ℕ) (s : Store) : Store := Store.ofState {s.val with
  registers := Function.update
    (Function.update s.val.registers 24 ((s.val.tapes (negativePort source)).read.getD false))
    23 ((s.val.tapes (negativePort source)).read.isSome)}

theorem read_executes (source : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store) :
    Executes input tape (.atom (.readTape (negativePort source) 24 23)) 3 s (readState source s) := by
  apply Executes.atom (extra := 1) (t := {s.val.setRegister 24
    ((s.val.tapes (negativePort source)).read.getD false) with
    registers := Function.update
      (Function.update s.val.registers 24 ((s.val.tapes (negativePort source)).read.getD false))
      23 ((s.val.tapes (negativePort source)).read.isSome)})
  · simp [BitRAM.next,s.property]
  · simp [BitRAMState.setRegister,s.property]

theorem word_present {s : BitRAMState} {port n : ℕ} (h : Word s port n) :
    (s.tapes port).read.isSome=decide (0<n) := by
  obtain ⟨origin,h⟩ := h
  simp only [h,BitTape.read,BitTape.shifted,le_refl,ite_true,Int.sub_self,Int.toNat_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [isSome_getElem?,decide_eq_true_eq,Nat.size_eq_bits_len,Nat.size_pos]

theorem executes (source : ℕ) (z : ℤ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hp : Word s.val (positivePort source) z.toNat)
    (hn : Word s.val (negativePort source) (-z).toNat) :
    ∃t,Executes input tape (code source) (20*z.natAbs.bits.length+30) s t ∧
      t.val.output=(Codec.int z).reverse++s.val.output ∧ EmitNatural.Frame s t := by
  let a := readState source s
  let b := Store.ofState {a.val with pc := 1,output := a.val.registers 23::a.val.output}
  have ea := read_executes source input tape s
  have eb : Executes input tape (.atom (.output 23)) 2 a b := Executes.output input tape a 23
  have hsign : b.val.registers 23=decide (z<0) := by
    change (s.val.tapes (negativePort source)).read.isSome=_
    rw [word_present hn]
    exact decide_eq_decide.mpr (by omega : 0<(-z).toNat ↔ z<0)
  have htapes : b.val.tapes=s.val.tapes := rfl
  have hout : b.val.output=decide (z<0)::s.val.output := by
    change (s.val.tapes (negativePort source)).read.isSome::s.val.output=_
    rw [word_present hn]
    simp only [show (0<(-z).toNat)↔(z<0) from by omega]
  by_cases hz : z<0
  · have hm : (-z).toNat=z.natAbs := by omega
    obtain ⟨origin,hw⟩ := hn
    rw [hm] at hw
    obtain ⟨t,et,ot,ft⟩ := EmitNatural.executes (negativePort source) z.natAbs origin input tape b
      ((congrFun htapes _).trans hw)
    refine ⟨t,?_,?_,ft⟩
    · convert ea.seq (eb.seq (Executes.yes (by simpa only [hz,decide_true] using hsign) et)) using 1 <;>
        first | rfl | omega
    · rw [ot,hout]
      simp only [Codec.int,List.reverse_cons,List.append_assoc,List.singleton_append]
  · have hm : z.toNat=z.natAbs := by omega
    obtain ⟨origin,hw⟩ := hp
    rw [hm] at hw
    obtain ⟨t,et,ot,ft⟩ := EmitNatural.executes (positivePort source) z.natAbs origin input tape b
      ((congrFun htapes _).trans hw)
    refine ⟨t,?_,?_,ft⟩
    · convert ea.seq (eb.seq (Executes.no (by simpa only [hz,decide_false] using hsign) et)) using 1 <;>
        first | rfl | omega
    · rw [ot,hout]
      simp only [Codec.int,List.reverse_cons,List.append_assoc,List.singleton_append]

#print axioms executes
end Maxwell.Continuum.RationalDataflow.IntegerEmit
