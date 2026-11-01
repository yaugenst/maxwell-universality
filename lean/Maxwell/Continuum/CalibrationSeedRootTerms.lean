import Maxwell.Continuum.CalibrationSeedRootGuarded

/-! Fixed finite composition of the guarded cache contributions.  The
eight-alias specialization is independent of the output cube's runtime size. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def termsCode (j : Fin 3) (part : Fin 2) : List Corner.Parity→Code
  | [] => .skip
  | parity::rest => .seq (guardedCode parity j part) (termsCode j part rest)
def stepWidth (B : ℕ) : ℕ := termWidth (guardedWidth B)
def termsWidth : ℕ→ℕ→ℕ
  | 0,B => B
  | k+1,B => termsWidth k (stepWidth B)
def termsCost : ℕ→ℕ→ℕ
  | 0,_ => 1
  | k+1,B => guardedCost B+termsCost k (stepWidth B)
def termsValues (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (u : Fin 3→ℕ) (j : Fin 3) (part : Fin 2) : List Corner.Parity→(ℕ→Parts)→(ℕ→Parts)
  | [],v => v
  | parity::rest,v => termsValues M D a u j part rest (guardedValues M D a u parity j part v)
def parities : List Corner.Parity := List.ofFn parityFinEight.symm

theorem stepWidth_ge (B : ℕ) : B≤stepWidth B := by
  have h := le_max_left B (indexWidth (testWidth B))
  change B≤guardedWidth B at h
  unfold stepWidth termWidth
  omega
theorem guardedWidth_le_stepWidth (B : ℕ) : guardedWidth B≤stepWidth B := by
  unfold stepWidth termWidth
  omega

theorem terms_executes (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (ps : List Corner.Parity) (j : Fin 3) (part : Fin 2) (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ)
    (hM : n 750=M) (hD : n 751=D) (half : n 752=n 750/2)
    (naturalWidth : ∀i∈ids,(n i).bits.length≤B)
    (width : WidthBank slots B v) (good : Good slots v)
    (metadata : a.MetadataWidth B) (entryWidth : ∀i,(a.get i).Width B)
    (entryValid : ∀i,(a.get i).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (natural : NatAssign.Bank ids n s.val) (ready : Ready slots v s) (table : a.Ready s) :
    ∃cost t w,Executes input tape (termsCode j part ps) cost s t ∧ cost≤termsCost ps.length B ∧
      Ready slots (termsValues M D a (coordinates n) j part ps v) t ∧
      Good slots (termsValues M D a (coordinates n) j part ps v) ∧
      WidthBank slots (termsWidth ps.length B) (termsValues M D a (coordinates n) j part ps v) ∧
      NatAssign.Bank ids w t.val ∧ (∀i∈ids,(w i).bits.length≤termsWidth ps.length B) ∧
      (∀i∈retained,w i=n i) ∧ a.Ready t ∧ Frame s t := by
  induction ps generalizing n v B s with
  | nil =>
    exact ⟨1,s,n,Executes.skip s,le_rfl,ready,good,width,natural,naturalWidth,
      by intro i hi;rfl,table,⟨rfl,rfl,rfl,rfl,by intro i hi ho;rfl,rfl⟩⟩
  | cons parity rest ih =>
    obtain ⟨c0,b,w,e0,h0,rb,gb,wb,nb,nwb,keep,tb,f0⟩ := guarded_executes M D a parity j part n v B
      hM hD half naturalWidth width good metadata entryWidth entryValid input tape s natural ready table
    have m : w 750=M := (keep 750 (by decide)).trans hM
    have d : w 751=D := (keep 751 (by decide)).trans hD
    have hp : w 752=w 750/2 := by rw [keep 752 (by decide),keep 750 (by decide)];exact half
    have co : coordinates w=coordinates n := by
      funext k
      fin_cases k <;> simp [coordinates,keep 753 (by decide),keep 754 (by decide),keep 755 (by decide)]
    obtain ⟨c1,t,z,e1,h1,rt,gt,wt,nt,nwt,kt,tt,f1⟩ := ih w
      (guardedValues M D a (coordinates n) parity j part v) (stepWidth B) m d hp
      (fun i hi=>(nwb i hi).trans (guardedWidth_le_stepWidth B)) wb gb
      (metadata.mono (stepWidth_ge B)) (fun i=>(entryWidth i).mono (stepWidth_ge B))
      b nb rb tb
    refine ⟨c0+c1,t,z,e0.seq e1,Nat.add_le_add h0 h1,?_,?_,?_,nt,nwt,
      fun i hi=>(kt i hi).trans (keep i hi),tt,f0.trans f1⟩
    · simpa only [termsValues,co] using rt
    · simpa only [termsValues,co] using gt
    · simpa only [termsValues,co,List.length_cons,termsWidth] using wt

#print axioms terms_executes
end Maxwell.Continuum.Calibration.SeedRoot
