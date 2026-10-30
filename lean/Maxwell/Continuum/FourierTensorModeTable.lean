import Maxwell.Continuum.FourierTensorModeRow
import Maxwell.Continuum.FourierTensorModeTableData

/-! A fixed counted program generates all five-column Fourier input
rows from the actual normalized calibration array. All iterations retain
the same input-width invariant and all output writes are charged. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def tableCode (j : Fin 3) : Code := countedProgram 201 (rowCode j)

structure TableState (P R : ℕ) (a : Table (2*aliasArraySize R))
    (b : Table (5*RowArithmetic.rowCount R)) (j : Fin 3) (v : ℕ→Parts)
    (emitted : List Bool) (remaining : ℕ) (s : Store) : Prop where
  remaining_le : remaining≤RowArithmetic.rowCount R
  ready : RationalDataflow.Ready RowArithmetic.bank (canonical v) s
  source : a.Ready s
  destination : (b.filled (entries P R a j (canonical v)) (5*remaining)).OutputReady s
  naturals : NatAssign.Bank ModeIndex.ports (ModeIndex.initial R (aliasArraySize R) 0) s.val
  floor : DyadicFloor.Clean s.val
  power : Word s.val 144 (2^P)
  output : s.val.output=emitted

theorem TableState.count_frame {P R : ℕ} {a : Table (2*aliasArraySize R)}
    {b : Table (5*RowArithmetic.rowCount R)} {j : Fin 3} {v : ℕ→Parts} {emitted : List Bool}
    {remaining : ℕ} {s t : Store} (h : TableState P R a b j v emitted remaining s)
    (f : CountedShifted.Frame 201 s t) : TableState P R a b j v emitted remaining t := by
  have keep := f.2.2.2.2.2.1
  refine ⟨h.remaining_le,Ready.count_frame _ _ 201 (by decide) h.ready f,
    h.source.count_frame f,h.destination.count_frame f,?_,?_,
    RationalAccumulator.word_of_eq (keep 144 (by decide)) h.power,f.2.2.2.2.1.trans h.output⟩
  · intro i hi
    have hh : 310 ≤ i := (Finset.mem_Icc.mp hi).1
    exact RationalAccumulator.word_of_eq (keep i (by omega)) (h.naturals i hi)
  · refine ⟨RationalAccumulator.blank_of_eq (keep 4 (by decide)) h.floor.1,?_⟩
    intro i hi
    have hn : i≠201 := by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact RationalAccumulator.blank_of_eq (keep i hn) (h.floor.2 i hi)

theorem table_executes (P R W : ℕ) (hW : 2≤W)
    (a : Table (2*aliasArraySize R)) (b : Table (5*RowArithmetic.rowCount R))
    (j : Fin 3) (v : ℕ→Parts) (hma : a.MetadataWidth W) (hmb : b.MetadataWidth W)
    (hw : WidthBank RowArithmetic.bank W v) (hg : Good RowArithmetic.bank v)
    (hav : ∀i,(a.get i).Valid) (hR : R.bits.length≤W) (hsize : (aliasArraySize R).bits.length≤W)
    (hfit : ∀r : Fin (RowArithmetic.rowCount R),∀x∈writePlan,
      (values P R a j r (canonical v) x.2).Width (addressValue b.width))
    (hpos : 0<addressValue b.width) (hsep : b.Separated) (hdisj : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (hlen : xs.length≤W)
    (hcount : addressValue xs=RowArithmetic.rowCount R) (s : Store)
    (hc : s.val.tapes 201=BitTape.shifted xs origin)
    (hr : RationalDataflow.Ready RowArithmetic.bank (canonical v) s)
    (ha : a.Ready s) (hb : b.OutputReady s)
    (hn : NatAssign.Bank ModeIndex.ports (ModeIndex.initial R (aliasArraySize R) 0) s.val)
    (hz : DyadicFloor.Clean s.val) (hp : Word s.val 144 (2^P)) :
    ∃cost t ys,Executes input tape (tableCode j) cost s t ∧
      cost≤2^215*(RowArithmetic.rowCount R+1)*(P+W+12)^2 ∧
      TableState P R a b j v s.val.output 0 t ∧
      t.val.tapes 201=BitTape.shifted ys origin ∧ ys.length=xs.length := by
  let inv := TableState P R a b j v s.val.output
  have stable : ∀r s t,CountedShifted.Frame 201 s t→inv r s→inv r t := by
    intro r u t f h
    exact h.count_frame f
  have step : ∀r ys u,inv (r+1) u→u.val.tapes 201=BitTape.shifted ys origin→
      addressValue ys=r→ys.length=xs.length→
      ∃cost t,Executes input tape (rowCode j) cost u t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted ys origin ∧ cost≤2^210*(P+W+11)^2 := by
    intro r ys u h hword hval hlen'
    have hrange : r<RowArithmetic.rowCount R := by have := h.remaining_le;omega
    let ri : Fin (RowArithmetic.rowCount R) := ⟨r,hrange⟩
    obtain ⟨cost,t,e,hcost,ready,_,_,source,dest,naturals,floor,power,_,counter,output⟩ := row_executes P R W hW a
      (b.filled (entries P R a j (canonical v)) (5*(r+1))) j ri (canonical v) hma
      ⟨hmb.width,hmb.basePositive,hmb.baseNegative,hmb.baseDenominator,hmb.clock⟩
      (canonical_width v W (by omega) hw) (canonical_good v hg) hav hR hsize (hfit ri) hpos hsep hdisj
      input tape ys (by omega) hval u h.ready h.source h.destination ⟨origin,hword⟩ h.naturals h.floor h.power
    rw [canonical_idempotent] at ready
    have dest' : (b.filled (entries P R a j (canonical v)) (5*r)).OutputReady t := by
      change (written P R a (b.filled (entries P R a j (canonical v)) (5*(ri.val+1)))
        j ri (canonical v)).OutputReady t at dest
      rw [filled_write_step] at dest
      exact dest
    have counter' : t.val.tapes 201=BitTape.shifted ys origin := counter.trans hword
    exact ⟨cost,t,e,⟨by omega,ready,source,dest',naturals,floor,power,output.trans h.output⟩,counter',hcost⟩
  have initial : inv (RowArithmetic.rowCount R) s :=
    ⟨le_rfl,hr,ha,by simpa only [Table.filled_initial] using hb,hn,hz,hp,rfl⟩
  obtain ⟨cost,t,ys,e,final,word,length,_,hcost⟩ := counted_executes_sized 201 origin (rowCode j)
    input tape xs.length inv (fun _ => 2^210*(P+W+11)^2) stable step
    (RowArithmetic.rowCount R) xs s hcount hc rfl initial
  refine ⟨cost,t,ys,e,?_,final,word,length⟩
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hcost
  have hstep : (P+W+11)^2≤(P+W+12)^2 := Nat.pow_le_pow_left (by omega) 2
  have hclock : 13*xs.length+15≤16*(P+W+12)^2 := by nlinarith only [hlen,Nat.zero_le P,Nat.zero_le W]
  have hs := Nat.mul_le_mul_left (RowArithmetic.rowCount R*2^210) hstep
  have hc' := Nat.mul_le_mul_left (RowArithmetic.rowCount R+1) hclock
  nlinarith only [hcost,hs,hc',Nat.zero_le ((P+W+12)^2)]

#print axioms table_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
