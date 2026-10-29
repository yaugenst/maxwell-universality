import Maxwell.Cost.Address.Width

namespace Maxwell.Cost

theorem PricedSteps.endpoint_eq {σ : Type} {next : σ→Option (PricedStep σ)}
    {n m : ℕ} {s t u : σ} (h : PricedSteps next n s t) (k : PricedSteps next m s u)
    (hn : n=m) : t=u := by
  induction h generalizing m u with
  | refl s =>
    cases k with
    | refl => rfl
    | step _ _ => omega
  | @step n extra s v t hs rest ih =>
    cases k with
    | refl => omega
    | @step m extra' _ w _ hk tail =>
      have he := Option.some.inj (hk.symm.trans hs)
      cases he
      exact ih tail (by omega)

/-- Deterministic terminating executions have the same charged cost and
state, allowing stronger trace proofs to enrich existing endpoint APIs. -/
theorem PricedSteps.halted_unique {σ : Type} {next : σ→Option (PricedStep σ)}
    {n m : ℕ} {s t u : σ} (h : PricedSteps next n s t) (ht : next t=none)
    (k : PricedSteps next m s u) (hu : next u=none) : n=m ∧ t=u := by
  have a := h.runPriced_ge ht (n+m+1) (by omega)
  have b := k.runPriced_ge hu (n+m+1) (by omega)
  exact ⟨a.2.symm.trans b.2,Option.some.inj (a.1.symm.trans b.1)⟩

/-- A halted checked trace controls every actual prefix, even when the
caller supplies a fuel cap larger than the terminating execution. -/
theorem VisitedPriced.prefix_halt {σ : Type} {next : σ→Option (PricedStep σ)}
    {P : σ→Prop} {n k : ℕ} {s t u : σ} (h : VisitedPriced next P n s t)
    (halt : next t=none) (hp : PricedSteps next k s u) : P u := by
  induction h generalizing k u with
  | refl hs =>
    cases hp with
    | refl => exact hs
    | step hn _ => rw [halt] at hn; contradiction
  | @step n extra s v t hs hn rest ih =>
    cases hp with
    | refl => exact hs
    | @step k extra' _ w _ hk tail =>
      have he := Option.some.inj (hk.symm.trans hn)
      cases he
      exact ih halt tail

theorem PricedSteps.visited_invariant {σ : Type} {next : σ→Option (PricedStep σ)}
    {P : σ→Prop} {n : ℕ} {s t : σ} (h : PricedSteps next n s t) (hs : P s)
    (preserved : ∀ a b extra,P a→next a=some ⟨b,extra⟩→P b) :
    VisitedPriced next P n s t := by
  induction h with
  | refl => exact .refl hs
  | step hn rest ih => exact .step hs hn (ih (preserved _ _ _ hs hn))

theorem BitRAM.Contains.visited_address {outer body : BitRAM} {base returnPC W cost : ℕ}
    (hc : outer.Contains body base returnPC) (input : List Bool) (tape : ℕ→Bool)
    {s t : BitRAMState} (h : VisitedPriced (body.next input tape) (Address.Within W) cost s t) :
    VisitedPriced (outer.next input tape) (Address.Within W) cost (s.relocate base) (t.relocate base) :=
  h.map (BitRAMState.relocate base) (fun _ _ _ hn => hc.next input tape hn) (fun _ hp => hp)

theorem BitRAM.Contains.visited_call {outer body : BitRAM} {base returnPC W cost : ℕ}
    (hc : outer.Contains body base returnPC) (input : List Bool) (tape : ℕ→Bool)
    {s t : BitRAMState} (h : VisitedPriced (body.next input tape) (Address.Within W) cost s t)
    (halt : body.code[t.pc]?=some .halt) :
    VisitedPriced (outer.next input tape) (Address.Within W) (cost+1)
      (s.relocate base) {t with pc:=returnPC} := by
  have tail : VisitedPriced (outer.next input tape) (Address.Within W) 1
      (t.relocate base) {t with pc:=returnPC} := by
    apply VisitedPriced.step (extra := 0)
      (rest := .refl (s := {t with pc:=returnPC}) (show Address.Within W _ from h.finish))
    · exact h.finish
    · exact hc.return_step input tape t halt
  exact (hc.visited_address input tape h).trans tail

theorem BitRAM.Contains.visited_call_at {outer body : BitRAM} {base returnPC W cost : ℕ}
    (hc : outer.Contains body base returnPC) (input : List Bool) (tape : ℕ→Bool)
    (s t : BitRAMState) (hpc : s.pc=base)
    (h : VisitedPriced (body.next input tape) (Address.Within W) cost {s with pc:=0} t)
    (halt : body.code[t.pc]?=some .halt) :
    VisitedPriced (outer.next input tape) (Address.Within W) (cost+1) s {t with pc:=returnPC} := by
  have hh := hc.visited_call input tape h halt
  have he : ({s with pc:=0}:BitRAMState).relocate base=s := by simp [BitRAMState.relocate,←hpc]
  simpa only [he] using hh

/-- Only an actual addressPush can increase the explicit address word. -/
def BitRAMInstruction.noAddressPush : BitRAMInstruction→Bool
  | .addressPush _ => false
  | _ => true

def BitRAM.noAddressPush (M : BitRAM) : Bool := M.code.all BitRAMInstruction.noAddressPush

theorem BitRAM.noAddressPush_next {M : BitRAM} (h : M.noAddressPush=true)
    (input : List Bool) (tape : ℕ→Bool) (s t : BitRAMState) (extra : ℕ)
    (hn : M.next input tape s=some ⟨t,extra⟩) : t.address.length≤s.address.length := by
  cases hi : M.code[s.pc]? with
  | none => simp [BitRAM.next,hi] at hn
  | some instruction =>
    have hs := List.all_eq_true.mp h instruction (List.mem_of_getElem? hi)
    cases instruction <;>
      simp only [BitRAM.next,hi,Option.some.injEq,PricedStep.mk.injEq,BitRAMInstruction.noAddressPush] at hn hs <;>
      first
      | contradiction
      | rcases hn with ⟨rfl,rfl⟩
        simp [BitRAMState.setRegister,BitRAMState.setTape]

theorem PricedSteps.visited_noAddressPush {M : BitRAM} {input : List Bool} {tape : ℕ→Bool}
    {n W : ℕ} {s t : BitRAMState} (h : PricedSteps (M.next input tape) n s t)
    (hp : M.noAddressPush=true) (hs : Address.Within W s) :
    VisitedPriced (M.next input tape) (Address.Within W) n s t :=
  h.visited_invariant hs (fun a b extra ha hn =>
    (M.noAddressPush_next hp input tape a b extra hn).trans ha)

end Maxwell.Cost
