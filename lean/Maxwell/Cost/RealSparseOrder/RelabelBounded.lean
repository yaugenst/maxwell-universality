import Maxwell.Cost.RealSparseOrder.RelabelIndexBounds

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSimulation.Control RealSimulation.IndexWidth

theorem bounded_loop (input : RAMInput) (tape : ℕ→Bool) (B : ℕ)
    (s : Store) (b : Buffer) (es : List SparseEntry) (previous : Option ℕ)
    (count m map rhs : ℕ)
    (h : Config s.val b es.length previous count m map rhs)
    (hb : b.Safe) (hm : b.coordinates+2*es.length≤map)
    (hv : b.coefficients+es.length≤rhs) (hr : Records b s.val es)
    (hs : IndexBound B s.val) (hc : b.coordinates+2*es.length≤B)
    (hmap : map+count+es.length≤B) (hrhs : rhs+count+es.length≤B)
    (hi : ∀e∈es,m+e.row≤B) :
    ∃cost t,cost≤21*es.length+1 ∧BoundedExecutes B 20 input tape loopCode cost s t := by
  induction es generalizing s b previous count with
  | nil =>
    exact ⟨1,s,by simp,BoundedExecutes.done (by rw [h.one,h.remaining]; simp) hs⟩
  | cons e es ih =>
    have hmaplo : 100≤map := by have hh:=hb.2; simp only [List.length_cons] at hm; omega
    have hrhslo : 100≤rhs := by have hh:=hb.1; simp only [List.length_cons] at hv; omega
    let mid := processed input previous e.row s
    let c := nextCount previous count e.row
    have hcl : count≤c := by dsimp [c,nextCount]; split <;> omega
    have hcu : c≤count+1 := by dsimp [c,nextCount]; split <;> omega
    have hmid : Config mid.val (b.shift 1) es.length (some e.row) c m map rhs := by
      simpa only [List.length_cons,Nat.add_sub_cancel] using processed_config h hb.2 hmaplo hr.1
    have hms : IndexBound B mid.val := processed_index_bound input h hs hmaplo
      (by simp only [List.length_cons] at hc; omega)
      (by simp only [List.length_cons] at hmap; omega)
      (by simp only [List.length_cons] at hrhs; omega)
      (hi e (by simp)) (by simp only [List.length_cons] at hmap; omega) hr.1
    have hmrecords := processed_records h hb hm hv hr (input:=input)
    obtain ⟨first,hfirst,firstRun⟩ := step input tape s b (e::es).length previous count m map rhs
      e.row h hb.2 hmaplo hrhslo hr.1
    obtain ⟨rest,t,hrest,tailRun⟩ := ih mid (b.shift 1) (some e.row) c hmid (hb.shift 1)
      (by simp only [Buffer.shift,List.length_cons] at *; omega)
      (by simp only [Buffer.shift,List.length_cons] at *; omega)
      hmrecords.2.2.2 hms
      (by simp only [Buffer.shift,List.length_cons] at *; omega)
      (by simp only [List.length_cons] at hmap; omega)
      (by simp only [List.length_cons] at hrhs; omega)
      (fun f hf=>hi f (by simp [hf]))
    refine ⟨1+first+rest,t,by simp only [List.length_cons]; omega,?_⟩
    exact BoundedExecutes.more (by rw [h.one,h.remaining]; simp)
      (BoundedExecutes.atom firstRun hfirst hs hms) tailRun

/-- The fixed boundary cap is restored after every record. Thus the entire
initialized scan has a constant atom overhead of twenty, independent of m. -/
theorem bounded_scan (original es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (B : ℕ) (s : Store) (b : Buffer) (hlen : es.length=original.length)
    (h0 : s.val.indices 0=0) (h1 : s.val.indices 1=1) (h2 : s.val.indices 2=2)
    (hm : s.val.indices 26=es.length) (hc : s.val.indices 27=b.coordinates)
    (hb : b.Safe) (hmap : b.coordinates+2*es.length≤outputBase es.length)
    (hrhs : b.coefficients+es.length≤outputBase es.length) (hr : Records b s.val es)
    (hs : IndexBound B s.val) (hcoords : b.coordinates+2*es.length≤B)
    (houtput : outputBase es.length+es.length≤B) (hi : ∀e∈es,es.length+e.row≤B) :
    ∃cost t,cost≤21*es.length+12 ∧
      BoundedExecutes B 20 (RealSparse.input original vector) tape code cost s t ∧
      Result b es vector s.val t.val := by
  let mid := Store.ofState (initialized s.val)
  have hconfig : Config mid.val b es.length none 0 es.length
      (outputBase es.length) (outputBase es.length) :=
    (config_ofState _ _ _ _ _ _ _ _).mpr (init_config s.val b es.length h0 h1 h2 hm hc)
  have hrecords : Records b mid.val es := by
    have hh := initialized_records hr hb
    rw [records_stored] at hh ⊢
    exact hh
  have hmidbound : IndexBound B mid.val :=
    initialized_index_bound hs (by rw [hm]; omega)
  obtain ⟨cost,t,hcost,run⟩ := bounded_loop (RealSparse.input original vector) tape B mid b es none 0
    es.length (outputBase es.length) (outputBase es.length) hconfig hb hmap hrhs hrecords
    hmidbound hcoords (by simpa using houtput) (by simpa using houtput) hi
  have full : BoundedExecutes B 20 (RealSparse.input original vector) tape code (11+cost) s t :=
    BoundedExecutes.seq (BoundedExecutes.atom (init_executes _ tape s) (by omega) hs hmidbound) run
  obtain ⟨actualCost,actual,hactual,hactualRun,hresult⟩ :=
    scan_executes original es vector tape s b hlen h0 h1 h2 hm hc hb hmap hrhs hr
  obtain ⟨heq,hstate⟩ := full.executes.deterministic hactualRun
  subst actual
  exact ⟨11+cost,t,by omega,full,hresult⟩

end Maxwell.Cost.RealSparseOrder.Relabel
