import Maxwell.Continuum.SourceRoutingSortNeighbors
import Maxwell.Continuum.SourceRoutingSortSelection
import Maxwell.Continuum.SourceRoutingGeometryAccess
import Maxwell.Continuum.SourceRoutingScatterArray
import Maxwell.Continuum.SourceRoutingTreeMemory

namespace Maxwell.Cost.RoutingPorts.Complete.GeometrySort
open Structured GeometryArithmetic Maxwell.Logical.Routing
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Plan (q : ℕ) where
  source : ℕ
  destination : ℕ
  clock : List Bool
  positive : 0<q
  clock_length : clock.length=(q*q).bits.length
  separated : IncidenceEncoding.Separated source (q*q*(q*q).bits.length) destination (q*q*(q*q).bits.length)

def Plan.width {q : ℕ} (_p : Plan q) : ℕ := (q*q).bits.length
def Plan.bound {q : ℕ} (p : Plan q) (round : ℕ) : ℕ :=
  p.width+q.bits.length+round.bits.length+p.source.bits.length+p.destination.bits.length+32

theorem Plan.width_positive {q : ℕ} (p : Plan q) : 0<p.width :=
  RationalAccumulator.bits_nonempty (Nat.mul_pos p.positive p.positive)
theorem Plan.width_bound {q : ℕ} (p : Plan q) (round : ℕ) : p.width ≤ p.bound round := by dsimp only [Plan.bound];omega
theorem Plan.index_fit {q : ℕ} (p : Plan q) (i : Fin (q*q)) : i.val.bits.length ≤ p.width :=
  Maxwell.Continuum.RationalWords.bits_mono i.isLt.le

structure Metadata {q : ℕ} (p : Plan q) (s : BitRAMState) : Prop where
  width : Word s 711 p.width
  clock : BankArray.Word s 718 p.clock

theorem Metadata.frame {q : ℕ} {p : Plan q} {s t : BitRAMState} {changed : Finset ℕ}
    (m : Metadata p s) (f : ArchiveFrame changed s t) (keep : Disjoint ({711,718} : Finset ℕ) changed) : Metadata p t :=
  ⟨RationalAccumulator.word_of_eq (f.tapes 711 (by decide) (Finset.disjoint_left.mp keep (by decide))) m.width,
    BankArray.word_of_eq (f.tapes 718 (by decide) (Finset.disjoint_left.mp keep (by decide))) m.clock⟩

def seed {q : ℕ} (p : Plan q) (round k j : ℕ) : ℕ :=
  if j=1200 then q else if j=1201 then k else if j=1202 then round else
    if j=1215 then p.source else if j=1216 then p.destination else if j=1217 then p.width else
      if j=1219 then 1 else if j=1220 then 2 else 0

theorem seed_setup {q : ℕ} (p : Plan q) (round k : ℕ) : PartnerSetup q k round (seed p round k) :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem seed_width {q : ℕ} (p : Plan q) (round k : ℕ) (hk : k ≤ q*q) :
    ∀j∈GeometryArithmetic.ids,(seed p round k j).bits.length ≤ p.bound round := by
  have kfit : k.bits.length ≤ p.width := Maxwell.Continuum.RationalWords.bits_mono hk
  have widthBits : p.width.bits.length ≤ p.width := natural_bits_length_le _
  intro j _
  dsimp only [seed]
  split_ifs <;> dsimp only [Plan.bound]
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [show (1 : ℕ).bits.length=1 by decide];omega
  · rw [show (2 : ℕ).bits.length=2 by decide];omega
  · rw [show (0 : ℕ).bits.length=0 by decide];omega
theorem seed_zero {q : ℕ} (p : Plan q) (round k : ℕ) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,seed p round k j=0 := by
  intro j hj
  simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,
    Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl|rfl|rfl|rfl <;> rfl

def Fits {q : ℕ} (width : ℕ) (saved : SortArrays.Keys q) : Prop := ∀i,(saved.get i).bits.length ≤ width
def intermediate {q : ℕ} (p : Plan q) (round : ℕ) (i : Fin (q*q)) : ℕ→ℕ :=
  partnerProgram.evaluate (seed p round i.val)
def afterSelf {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) : ℕ→ℕ :=
  Function.update (intermediate p round i) 1208 (saved.get i)
def beforeSelect {q : ℕ} (p : Plan q) (round : ℕ) (saved : SortArrays.Keys q) (i : Fin (q*q)) : ℕ→ℕ :=
  Function.update (afterSelf p round saved i) 1209 (saved.get (neighbor round i))

theorem intermediate_other {q : ℕ} (p : Plan q) (round : ℕ) (i : Fin (q*q)) (j : ℕ)
    (hj : j∉partnerProgram.writes) : intermediate p round i j=seed p round i.val j :=
  partnerProgram.evaluate_other _ j hj

theorem intermediate_width {q : ℕ} (p : Plan q) (round : ℕ) (i : Fin (q*q)) :
    ∀j∈GeometryArithmetic.ids,(intermediate p round i j).bits.length ≤ 2^20*(p.bound round+1) := by
  have h:=partnerProgram.evaluate_width partner_valid (seed p round i.val) (p.bound round)
    (seed_width p round i.val i.isLt.le) (partner_literals _ (by dsimp only [Plan.bound];omega))
  intro j hj
  exact (Nat.le_add_right _ _).trans ((h j hj).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) partner_steps)))

#print axioms intermediate_width
end Maxwell.Cost.RoutingPorts.Complete.GeometrySort
