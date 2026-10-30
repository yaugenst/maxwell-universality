import Maxwell.Continuum.DyadicFloorPowerPreparation
import Maxwell.Continuum.RationalDataflowArrayFrame

/-! Fixed dyadic-floor execution from a stored precision. The binary scale
is constructed by actual counted writes before the exact signed division. -/
namespace Maxwell.Continuum.RationalDataflow.DyadicFloor.StoredPower
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def runtimeCode (target source : ℕ) : Code := .seq powerCode (code target source)
def runtimeWorkspace (S : Finset ℕ) : Finset ℕ := insert 146 (workspace S)

theorem reserved_outside (S : Finset ℕ) (i : ℕ) (hi : 144 < i ∧ i ≤ 146) : i∉workspace S := by
  have hr := RationalDataflow.outside_workspace S i (by omega)
  have hids : i∉RationalDataflow.ids S := fun h => hr (Finset.mem_union_right _ h)
  simp (disch := omega) [workspace,DyadicFloor.workspace,DyadicFloor.allIds,
    extraIds,NaturalQuotient.workPorts,hids]
  omega

theorem runtime_executes (S : Finset ℕ) (P target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v) (hx : (v source).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) (hz : Clean s.val)
    (hp : Word s.val 145 P) (hc : Blank s.val 146) (hblank : Blank s.val 144) :
    ∃ cost t,Executes input tape (runtimeCode target source) cost s t ∧ cost≤2^141*(P+W+4)^2 ∧
      Ready S (Function.update v target (result P (v source))) t ∧ Clean t.val ∧
      Word t.val 145 P ∧ Word t.val 144 (2^P) ∧ Blank t.val 146 ∧
      BinaryPrecision.Frame (runtimeWorkspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,p0,d0,z0,f0⟩ := power_executes P input tape s hp hc hblank
  have keep (i : ℕ) (hi : i≠144 ∧ i≠146) : s0.val.tapes i=s.val.tapes i := by
    exact f0.tapes i (by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hi)
  have b0 : Ready S v s0 := by
    refine ⟨?_,?_⟩
    · intro i hi
      have h144 := RationalDataflow.outside_workspace S 144 (by decide)
      have h146 := RationalDataflow.outside_workspace S 146 (by decide)
      have hg : i≠144 ∧ i≠146 := by
        constructor <;> intro he <;> subst i
        · exact h144 (Finset.mem_union_right _ hi)
        · exact h146 (Finset.mem_union_right _ hi)
      exact word_of_eq (keep i hg) (hs.1 i hi)
    · intro i hi;exact blank_of_eq (keep i (by omega)) (hs.2 i hi)
  have clean0 : Clean s0.val := by
    refine ⟨blank_of_eq (keep 4 (by decide)) hz.1,?_⟩
    intro i hi
    have hn : i≠144 ∧ i≠146 := by
      simp only [extraIds,NaturalQuotient.workPorts,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact blank_of_eq (keep i hn) (hz.2 i hi)
  obtain ⟨c1,t,e1,h1,hr,hz',hp',f1⟩ := executes S P target source ht hs' v W hw hx
    input tape s0 b0 clean0 d0
  have hstep := h1.trans (DyadicFloor.costBound_polynomial P W)
  have hscale : 2^10*(P+2)^2≤2^10*(P+W+4)^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  refine ⟨c0+c1,t,e0.seq e1,?_,hr,hz',word_of_eq (f1.tapes 145 (reserved_outside S 145 (by decide))) p0,
    hp',blank_of_eq (f1.tapes 146 (reserved_outside S 146 (by decide))) z0,
    (f0.mono ?_).trans (f1.mono (Finset.subset_insert _ _))⟩
  · have hsum := Nat.add_le_add (h0.trans hscale) hstep
    calc
      _≤(2^10+2^140)*(P+W+4)^2 := by simpa only [Nat.add_mul] using hsum
      _≤_ := Nat.mul_le_mul_right _ (by norm_num)
  · intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_self _ _

theorem runtime_computes (S : Finset ℕ) (P target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v) (hx : (v source).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) (hz : Clean s.val)
    (hp : Word s.val 145 P) (hc : Blank s.val 146) (hblank : Blank s.val 144) :
    ∃ t : Store, (runPriced ((runtimeCode target source).compile.next input tape)
      (2^141*(P+W+4)^2+1) s.val).finished=some (t.place (runtimeCode target source).size) ∧
      (runPriced ((runtimeCode target source).compile.next input tape)
      (2^141*(P+W+4)^2+1) s.val).instructions≤2^141*(P+W+4)^2 ∧
      Ready S (Function.update v target (result P (v source))) t ∧ Clean t.val ∧
      Word t.val 145 P ∧ Word t.val 144 (2^P) ∧ Blank t.val 146 ∧
      BinaryPrecision.Frame (runtimeWorkspace S) s.val t.val ∧
      (result P (v source)).value=((roundDyadic P (v source).value).numerator:ℚ) := by
  obtain ⟨cost,t,ex,hc,hr,hz',hp',hd,hblank',hf⟩ := runtime_executes S P target source ht hs' v W hw hx
    input tape s hs hz hp hc hblank
  have hout := ex.compiled_run (2^141*(P+W+4)^2+1) (by omega)
  exact ⟨t,hout.1,hout.2 ▸ hc,hr,hz',hp',hd,hblank',hf,result_value P (v source) hx⟩

#print axioms runtime_computes
end Maxwell.Continuum.RationalDataflow.DyadicFloor.StoredPower
