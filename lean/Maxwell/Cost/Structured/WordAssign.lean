import Maxwell.Cost.WordReplace

/-! Compile a static list of metadata copies to literal clearing and cloning
programs. Assigned values are computed only by those actual tape operations. -/
namespace Maxwell.Cost.Structured.WordAssign
open BankArray (Word)

abbrev Assignment := ℕ × ℕ

def code : List Assignment → Code
  | [] => .skip
  | (source,target)::rest => .seq (WordReplace.code source target) (code rest)

def values (assignments : List Assignment) (initial : ℕ → List Bool) : ℕ → List Bool :=
  assignments.foldl (fun current assignment => Function.update current assignment.2 (current assignment.1)) initial

def price : List Assignment → (ℕ → List Bool) → ℕ
  | [], _ => 1
  | (source,target)::rest, initial =>
      6*(initial target).length+15*(initial source).length+21+
        price rest (Function.update initial target (initial source))

def Bank (ids : List ℕ) (s : BitRAMState) (words : ℕ → List Bool) : Prop :=
  ∀ i, i∈ids → Word s i (words i)

def Valid (ids : List ℕ) (assignments : List Assignment) : Prop :=
  ∀ assignment∈assignments, assignment.1≠assignment.2 ∧ assignment.1∈ids ∧ assignment.2∈ids

def Frame (assignments : List Assignment) (s t : BitRAMState) : Prop :=
  t.address=s.address ∧ t.inputHead=s.inputHead ∧ t.memory=s.memory ∧
  t.randomCursor=s.randomCursor ∧ t.output=s.output ∧
  (∀ i, i∉assignments.map Prod.snd → t.tapes i=s.tapes i) ∧
  (∀ i, i≠24 → i≠25 → i≠26 → i≠27 → t.registers i=s.registers i)

theorem executes (assignments : List Assignment) (ids : List ℕ)
    (input : List Bool) (tape : ℕ → Bool) (initial : ℕ → List Bool)
    (hv : Valid ids assignments) (s : Store) (bank : Bank ids s.val initial) :
    ∃ t, Executes input tape (code assignments) (price assignments initial) s t ∧
      Bank ids t.val (values assignments initial) ∧ Frame assignments s.val t.val := by
  induction assignments generalizing initial s with
  | nil => exact ⟨s,.skip s,bank,by simp [Frame]⟩
  | cons assignment rest ih =>
    rcases assignment with ⟨source,target⟩
    obtain ⟨hne,hs,ht⟩ := hv (source,target) (by simp)
    obtain ⟨a,ea,aw,af⟩ := WordReplace.executes source target hne input tape (initial source) (initial target)
      s (bank source hs) (bank target ht)
    have ab : Bank ids a.val (Function.update initial target (initial source)) := by
      intro i hi
      by_cases hit : i=target
      · subst i; simpa using aw
      · simpa only [Function.update_of_ne hit] using BankArray.word_of_eq (af.2.2.2.2.2.1 i hit) (bank i hi)
    obtain ⟨t,et,tb,tf⟩ := ih _ (fun a ha => hv a (List.mem_cons_of_mem _ ha)) a ab
    refine ⟨t,ea.seq et,tb,?_⟩
    rcases af with ⟨aa,ai,am,ar,ao,atapes,aregs⟩
    rcases tf with ⟨ta,ti,tm,tr,tout,ttapes,tregs⟩
    refine ⟨ta.trans aa,ti.trans ai,tm.trans am,tr.trans ar,tout.trans ao,?_,?_⟩
    · intro i hi
      have hs : i≠target ∧ i∉rest.map Prod.snd := by simpa only [List.map_cons,List.mem_cons,not_or] using hi
      exact (ttapes i hs.2).trans (atapes i hs.1)
    · intro i h24 h25 h26 h27
      exact (tregs i h24 h25 h26 h27).trans (aregs i h24 h25 h26 h27)

theorem price_bound (assignments : List Assignment) (ids : List ℕ)
    (initial : ℕ → List Bool) (bound : ℕ) (hv : Valid ids assignments)
    (hl : ∀ i, i∈ids → (initial i).length ≤ bound) :
    price assignments initial ≤ assignments.length*(21*bound+21)+1 := by
  induction assignments generalizing initial with
  | nil => simp [price]
  | cons assignment rest ih =>
    rcases assignment with ⟨source,target⟩
    obtain ⟨_,hs,ht⟩ := hv (source,target) (by simp)
    have hrest := ih (Function.update initial target (initial source))
      (fun a ha => hv a (List.mem_cons_of_mem _ ha)) (by
        intro i hi
        by_cases hit : i=target
        · subst i; simpa using hl source hs
        · simpa only [Function.update_of_ne hit] using hl i hi)
    have hsource := hl source hs
    have htarget := hl target ht
    simp only [price,List.length_cons]
    nlinarith

end Maxwell.Cost.Structured.WordAssign
