import Maxwell.Cost.CalibrationMatrix.Horner.Round
import Maxwell.Cost.CalibrationMatrix.Horner.Recycle

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured

structure Snapshot (n : ℕ) where
  data : Data n
  words : Fin 12 → Vector (List Bool) n

def Snapshot.advance {n : ℕ} (a : Snapshot n) : Snapshot n :=
  ⟨recycleData a.data,recycleWords (roundWords a.data a.words)⟩

def Snapshot.Ready {n : ℕ} (a : Snapshot n) (count : List Bool) (B : ℕ) (s : BitRAMState) : Prop :=
  WorkReady count B s ∧ Stored a.data a.words s ∧ Ports a.data 2 3 10 11 s

def Snapshot.iterate {n : ℕ} (a : Snapshot n) : ℕ → Snapshot n
  | 0 => a
  | k+1 => (a.iterate k).advance

@[simp] theorem Snapshot.iterate_width {n : ℕ} (a : Snapshot n) (k : ℕ) :
    (a.iterate k).data.width = a.data.width := by
  induction k <;> simp_all [Snapshot.iterate,Snapshot.advance,recycleData,Data.permute]

theorem Snapshot.iterate_sized {n B : ℕ} (a : Snapshot n) (h : a.data.Sized B) (k : ℕ) :
    (a.iterate k).data.Sized B := by
  induction k with
  | zero => exact h
  | succ k ih => exact recycle_sized ih

theorem Snapshot.iterate_outside {n : ℕ} (a : Snapshot n) (k : ℕ) (s t : BitRAMState) :
    Outside (a.iterate k).data s t ↔ Outside a.data s t := by
  induction k with
  | zero => rfl
  | succ k ih => exact Outside.recycle.trans ih

def stepCode : Code := .seq roundCode recycleCode

def stepCost (n B : ℕ) : ℕ := roundCost n B+228*B+216

/-- One complete, reusable Horner iteration, including all buffer swaps. -/
theorem step {n : ℕ} (a : Snapshot n) (B : ℕ) (hsized : a.data.Sized B)
    (hm : n*n < 2^B) (hn : n < 2^B) (hfit : Fits a.data a.words)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B) (s : Store) (hs : a.Ready count B s.val) :
    ∃ cost, ∃ t : Store, cost ≤ stepCost n B ∧ Executes input tape stepCode cost s t ∧
      a.advance.Ready count B t.val ∧ t.val.tapes 140 = s.val.tapes 140 ∧
      Frame s.val t.val ∧ Outside a.data s.val t.val := by
  obtain ⟨cost1,b,hc1,eb,hbW,hbD,hbP,hb140,fb,mb⟩ := round a.data a.words B hsized hm hn hfit
    input tape count hcount hcl s hs.1 hs.2.1 hs.2.2
  obtain ⟨cost2,t,hc2,et,htW,htD,htP,ht140,mt,ft⟩ := recycle a.data (roundWords a.data a.words)
    B hsized input tape count b hbW hbD hbP
  exact ⟨cost1+cost2,t,by dsimp [stepCost];omega,eb.seq et,⟨htW,htD,htP⟩,
    ht140.trans hb140,fb.trans ft,mb.trans (Outside.of_memory mt)⟩

end Maxwell.Cost.CalibrationMatrix.Horner
