import Maxwell.Cost.Structured.NatAssign.StoredLength
import Maxwell.Cost.Structured.NatAssign.Bounds

/-! A fixed list of actual tape scans adds the lengths of stored natural words.
The inputs survive, the temporary word returns to zero, and the accumulator
contains the exact sum. This supplies runtime storage budgets without an
uncomputed width certificate. -/
namespace Maxwell.Cost.Structured.NatAssign.LengthSum
set_option maxHeartbeats 4000000

def total (sources : List ℕ) (v : ℕ→ℕ) : ℕ := (sources.map fun k=>(v k).bits.length).sum

def combine (target temp : ℕ) : List Instruction := [.add temp target,.literal temp 0]
def code (target temp : ℕ) : List ℕ→Code
  | [] => .skip
  | source::rest => .seq (WordLength.code source temp)
      (.seq (NatAssign.code (combine target temp)) (code target temp rest))
def changed (target temp : ℕ) : Finset ℕ := {0,1,2,3,target,temp}

theorem total_congr (sources : List ℕ) (v w : ℕ→ℕ) (h : ∀k∈sources,v k=w k) :
    total sources v=total sources w := by
  unfold total
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [h k hk]

theorem total_cons (source : ℕ) (rest : List ℕ) (v : ℕ→ℕ) :
    total (source::rest) v=(v source).bits.length+total rest v := rfl

theorem total_le (sources : List ℕ) (v : ℕ→ℕ) (B : ℕ)
    (h : ∀k∈sources,(v k).bits.length≤B) : total sources v≤sources.length*B := by
  induction sources with
  | nil => simp [total]
  | cons k rest ih =>
    rw [total_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    have hh:=h k (by simp)
    have hr:=ih (fun k hk=>h k (by simp [hk]))
    omega

theorem member_le_total (sources : List ℕ) (v : ℕ→ℕ) (k : ℕ) (hk : k∈sources) :
    (v k).bits.length≤total sources v := by
  induction sources with
  | nil => simp at hk
  | cons j rest ih =>
    rw [total_cons]
    rcases List.mem_cons.mp hk with rfl|hr
    · omega
    · have h:=ih hr;omega

theorem combined (target temp source : ℕ) (hne : target≠temp) (v : ℕ→ℕ) (hv : v temp=0) :
    values (combine target temp) (Function.update v temp (v source).bits.length)=
      Function.update v target (v target+(v source).bits.length) := by
  funext k
  by_cases ht:k=target
  · subst k
    simp [combine,values,Instruction.update,Instruction.target,Instruction.value,hne,Nat.add_comm]
  · by_cases hh:k=temp
    · subst k
      simp [combine,values,Instruction.update,Instruction.target,Instruction.value,hv,Ne.symm hne]
    · simp [combine,values,Instruction.update,Instruction.target,Instruction.value,ht,hh]

private theorem bits_le (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact Nat.lt_two_pow_self

theorem executes (ids : Finset ℕ) (ge : ∀k∈ids,4≤k) (target temp : ℕ)
    (ht : target∈ids) (hp : temp∈ids) (hne : target≠temp)
    (sources : List ℕ) (valid : ∀k∈sources,k∈ids ∧ k≠target ∧ k≠temp)
    (v : ℕ→ℕ) (B T : ℕ) (hv : ∀k∈ids,k≠target → k≠temp → (v k).bits.length≤B)
    (zero : v temp=0) (bound : v target+total sources v≤T)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (bank : Bank ids v s.val) (scratch : Scratch s.val) :
    ∃cost t,Executes input tape (code target temp sources) cost s t ∧
      cost≤sources.length*(200000*(B+T+2)^2)+1 ∧
      Bank ids (Function.update v target (v target+total sources v)) t.val ∧ Scratch t.val ∧
      BinaryPrecision.Frame (changed target temp) s.val t.val := by
  induction sources generalizing v s with
  | nil =>
    have eq : Function.update v target (v target+total [] v)=v := by simp [total]
    exact ⟨1,s,.skip s,by simp,by simpa only [eq] using bank,scratch,BinaryPrecision.Frame.refl _ _⟩
  | cons source rest ih =>
    have hs:=valid source (by simp)
    have sw:=hv source hs.1 hs.2.1 hs.2.2
    obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := stored_length ids source temp hs.2.2 hs.1 hp (ge temp hp)
      v zero input tape s bank scratch
    have width : ∀k∈ids,((Function.update v temp (v source).bits.length) k).bits.length≤B+T := by
      intro k hk
      by_cases ht':k=temp
      · subst k
        simp only [Function.update_self]
        exact ((bits_le _).trans sw).trans (Nat.le_add_right _ _)
      · rw [Function.update_of_ne ht']
        by_cases ha:k=target
        · subst k
          have h : v target≤T := by omega
          exact ((bits_le _).trans h).trans (Nat.le_add_left _ _)
        · exact (hv k hk ha ht').trans (Nat.le_add_right _ _)
    have vp : ∀a∈combine target temp,a.Valid ids := by simp [combine,Instruction.Valid,ht,hp,Ne.symm hne]
    obtain ⟨c1,u1,e1,hc1,b1,z1,f1⟩ := NatAssign.executes ids ge (combine target temp) vp _ input tape u b0 z0
    have price:=price_bound ids (combine target temp) vp _ (B+T) width (by simp [combine,Instruction.literalWidth])
    rw [combined target temp source hne v zero] at b1
    let next := Function.update v target (v target+(v source).bits.length)
    have preserved (k : ℕ) (hk : k∈rest) : next k=v k :=
      Function.update_of_ne (valid k (by simp [hk])).2.1 _ _
    have sum : total rest next=total rest v := total_congr rest next v preserved
    have nextTemp : next temp=0 := by simp only [next,Function.update_of_ne (Ne.symm hne),zero]
    obtain ⟨c2,t,e2,hc2,b2,z2,f2⟩ := ih (fun k hk=>valid k (by simp [hk])) next
      (fun k hk ha hb=>by simpa only [next,Function.update_of_ne ha] using hv k hk ha hb)
      nextTemp (by simp only [next,Function.update_self,sum,total_cons] at *;omega) u1 b1 z1
    have finish : Function.update next target (next target+total rest next)=
        Function.update v target (v target+total (source::rest) v) := by
      rw [sum,total_cons]
      simp only [next,Function.update_self,Function.update_idem,Nat.add_assoc]
    refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,by simpa only [finish] using b2,z2,
      (f0.mono ?_).trans ((f1.mono ?_).trans f2)⟩
    · have ps : (B+1)^2≤(B+T+2)^2 := Nat.pow_le_pow_left (by omega) 2
      have pos : 1≤(B+T+2)^2 := Nat.one_le_pow _ _ (by omega)
      have p0:=Nat.pow_le_pow_left (Nat.add_le_add_right sw 1) 2
      norm_num only [combine,List.length_cons,List.length_nil] at price
      dsimp only [combine] at hc1
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      nlinarith only [hc0,hc1,price,hc2,p0,ps,pos]
    · intro k hk
      have he:=Finset.mem_singleton.mp hk
      subst k
      simp [changed]
    · simp [changes,combine,Instruction.target,changed,Finset.subset_iff]

def initialPlan (target temp bias : ℕ) : List Instruction := [.literal target bias,.literal temp 0]
def initializedCode (target temp bias : ℕ) (sources : List ℕ) : Code :=
  .seq (NatAssign.code (initialPlan target temp bias)) (code target temp sources)
def initializedValues (target temp bias : ℕ) (sources : List ℕ) (v : ℕ→ℕ) : ℕ→ℕ :=
  Function.update (Function.update v temp 0) target (bias+total sources v)

theorem initialized_executes (ids : Finset ℕ) (ge : ∀k∈ids,4≤k) (target temp bias : ℕ)
    (ht : target∈ids) (hp : temp∈ids) (hne : target≠temp)
    (sources : List ℕ) (valid : ∀k∈sources,k∈ids ∧ k≠target ∧ k≠temp)
    (v : ℕ→ℕ) (B : ℕ) (hv : ∀k∈ids,(v k).bits.length≤B) (hbias : bias.bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (bank : Bank ids v s.val) (scratch : Scratch s.val) :
    ∃cost t,Executes input tape (initializedCode target temp bias sources) cost s t ∧
      cost≤192000*(B+2)^2+sources.length*(200000*(B+bias+sources.length*B+2)^2)+1 ∧
      Bank ids (initializedValues target temp bias sources v) t.val ∧ Scratch t.val ∧
      BinaryPrecision.Frame (changed target temp) s.val t.val := by
  have validInit : ∀a∈initialPlan target temp bias,a.Valid ids := by simp [initialPlan,Instruction.Valid,ht,hp]
  obtain ⟨c0,u,e0,hc0,b0,z0,f0⟩ := NatAssign.executes ids ge (initialPlan target temp bias) validInit v input tape s bank scratch
  have price:=price_bound ids (initialPlan target temp bias) validInit v B hv (by simp [initialPlan,Instruction.literalWidth,hbias])
  let initial := values (initialPlan target temp bias) v
  have eq : initial=Function.update (Function.update v temp 0) target bias := by
    funext k
    by_cases ha:k=target
    · subst k;simp [initial,initialPlan,values,Instruction.update,Instruction.target,Instruction.value,hne]
    · by_cases hh:k=temp
      · subst k;simp [initial,initialPlan,values,Instruction.update,Instruction.target,Instruction.value,Ne.symm hne]
      · simp [initial,initialPlan,values,Instruction.update,Instruction.target,Instruction.value,ha,hh]
  have keep (k : ℕ) (ha:k≠target) (hh:k≠temp) : initial k=v k := by
    rw [eq,Function.update_of_ne ha,Function.update_of_ne hh]
  have sum : total sources initial=total sources v := total_congr sources initial v
    (fun k hk=>keep k (valid k hk).2.1 (valid k hk).2.2)
  have accumulated : initial target=bias := by rw [eq,Function.update_self]
  obtain ⟨c1,t,e1,hc1,b1,z1,f1⟩ := executes ids ge target temp ht hp hne sources valid initial B
    (bias+total sources v) (fun k hk ha hh=>by rw [keep k ha hh];exact hv k hk)
    (by rw [eq,Function.update_of_ne (Ne.symm hne),Function.update_self])
    (by rw [sum,accumulated]) input tape u b0 z0
  have result : Function.update initial target (initial target+total sources initial)=
      initializedValues target temp bias sources v := by
    rw [sum,accumulated,eq,Function.update_idem]
    rfl
  refine ⟨c0+c1,t,e0.seq e1,?_,by simpa only [result] using b1,z1,(f0.mono ?_).trans f1⟩
  · have totalBound:=total_le sources v B (fun k hk=>hv k (valid k hk).1)
    have square:=Nat.pow_le_pow_left (show B+(bias+total sources v)+2≤B+bias+sources.length*B+2 by omega) 2
    have scaled:=Nat.mul_le_mul_left (sources.length*200000) square
    norm_num only [initialPlan,List.length_cons,List.length_nil] at price
    dsimp only [initialPlan] at hc0
    nlinarith only [hc0,hc1,price,scaled]
  · simp [changes,initialPlan,Instruction.target,changed,Finset.subset_iff]

#print axioms executes
#print axioms initialized_executes
end Maxwell.Cost.Structured.NatAssign.LengthSum
