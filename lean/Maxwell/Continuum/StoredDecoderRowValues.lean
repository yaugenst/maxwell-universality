import Maxwell.Continuum.StoredDecoderRowStep

namespace Maxwell.Continuum.DecoderRow
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def constantPorts : Finset ℕ:={144,982,983,984,985,4705,4706,4707,4708}
def rowValues {n : ℕ} (data : Vector ℕ n) (constants : ℕ→ℕ) (index : ℕ) (x : Parts) (k : ℕ):=
  if k=1000 then x.positive else
  if k=976 then GeometryOutput.arrayValue data (3*index) else
  if k=977 then GeometryOutput.arrayValue data (3*index+1) else
  if k=978 then GeometryOutput.arrayValue data (3*index+2) else constants k

theorem bits_congr (v w : ℕ→ℕ) (h : ∀k∈inputs,v k=w k):bits v=bits w:=by
  have ca : address v=address w:=by
    change v 982+v 985*(2*v 978)+v 4706*(v 982+v 984*(2*v 977))+
      (v 4705*v 4706)*(v 982+v 983*(2*v 976))=_
    rw [h 982 (by decide),h 983 (by decide),h 984 (by decide),h 985 (by decide),
      h 976 (by decide),h 977 (by decide),h 978 (by decide),h 4705 (by decide),h 4706 (by decide)]
    rfl
  unfold bits
  rw [ca,h 1000 (by decide),h 4707 (by decide),h 144 (by decide),h 4708 (by decide)]

theorem loaded_row {n : ℕ} (data : Vector ℕ n) (constants gv v : ℕ→ℕ) (j : ℕ) (x : Parts)
    (fixed : ∀k∈constantPorts,v k=constants k) (cursor : gv 971=3*j):
    bits (loaded data gv v x)=bits (rowValues data constants j x):=by
  apply bits_congr
  intro k hk
  simp only [inputs,Finset.mem_insert,Finset.mem_singleton] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp [loaded,coordinateValues,coordinatePorts,rowValues,GeometryOutput.readPlanValues,
      GeometryOutput.tripleTargets,GeometryOutput.readAdvanceValues,cursor,Nat.add_assoc]
  all_goals exact fixed _ (by decide)

theorem step_fixed {n : ℕ} (data : Vector ℕ n) (constants gv v : ℕ→ℕ) (x : Parts)
    (fixed : ∀k∈constantPorts,v k=constants k):
    ∀k∈constantPorts,reset (loaded data gv v x) k=constants k:=by
  intro k hk
  have out : k∉outputs:=fun hm=>Finset.disjoint_left.mp
    (by decide : Disjoint constantPorts outputs) hk hm
  have point : k∉coordinatePorts:=fun hm=>Finset.disjoint_left.mp
    (by decide : Disjoint constantPorts coordinatePorts) hk hm
  have h1000 : k≠1000:=by
    intro he;subst k;exact (by decide : 1000∉constantPorts) hk
  rw [reset,ite_eq_right out,loaded_kept _ _ _ _ _ point h1000]
  exact fixed k hk

#print axioms loaded_row
end Maxwell.Continuum.DecoderRow
