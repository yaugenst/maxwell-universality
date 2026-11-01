import Maxwell.Continuum.CalibrationBasisForcingData

/-! Actual fixed code for each of the 24 Schur forcing columns. Runtime
coordinates, rather than a supplied source table, determine every value. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow PointSupport
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536
set_option exponentiation.threshold 2048

def code (column : Fin 24) : Code := (PointSupport.control (support column) 32).code

private theorem distance_nodes (p : Point) : (distance p).nodes=8*p.length+1 := by
  induction p with
  | nil => rfl
  | cons a rest ih =>
    simp only [distance,PolynomialExpression.nodes,List.length_cons,ih]
    omega

private theorem support_space (column : Fin 24) : space (support column)=198 := by
  simp only [space,support,List.map_append,List.sum_append,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,weightedKey,distance_nodes,key,List.length_cons,List.length_nil]
  norm_num

theorem registers_eq (column : Fin 24) : PointSupport.registers (support column) 32=Finset.range 232 := by
  rw [registers,support_space]


private theorem distance_length (p : Point) (base : ℕ) :
    ((distance p).instructions base).length=10*p.length+1 := by
  induction p generalizing base with
  | nil => rfl
  | cons a rest ih =>
    simp only [distance,PolynomialExpression.instructions,List.length_append,List.length_cons,
      List.length_nil,ih]
    omega

private theorem point_steps (ν : Alias) (j : Fin 3) (w : ℚ) :
    (pointControl (key ν j) w 32).steps=44 := by
  simp only [pointControl,Control.andThen_steps,PolynomialExpression.control,Control.prepend_steps,
    Control.steps,distance_length,key,List.length_cons,List.length_nil]
  norm_num

private theorem traversal_steps (ps : Support) (h : ∀p∈ps,(pointControl p.1 p.2 32).steps=44) :
    (traversal 32 ps).steps=44*ps.length := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    rw [traversal,Control.andThen_steps,h p (by simp),ih (fun q hq => h q (by simp [hq]))]
    simp only [List.length_cons]
    omega

theorem steps_eq (column : Fin 24) : (PointSupport.control (support column) 32).steps=265 := by
  change 1+(traversal 32 (support column)).steps=265
  rw [traversal_steps]
  · simp [support]
  · intro p hp
    simp only [support,List.mem_append,List.mem_ofFn] at hp
    rcases hp with ⟨j,rfl⟩|⟨j,rfl⟩ <;> exact point_steps _ _ _


private theorem zero_width : (Parts.literal 0).Width 103 := by
  norm_num [Parts.Width,Parts.literal]

private theorem distance_literals (p : Point) (h : ∀a∈p,(Parts.literal a.2).Width 103) :
    (distance p).LiteralsFit 103 := by
  induction p with
  | nil => exact zero_width
  | cons a rest ih =>
    have ha := h a (by simp)
    exact ⟨⟨⟨trivial,ha⟩,⟨trivial,ha⟩⟩,ih (fun b hb => h b (by simp [hb]))⟩

private theorem coordinate_width (z : ℤ) (hz : -2≤z ∧ z≤1) : (Parts.literal (z:ℚ)).Width 103 := by
  obtain ⟨lo,hi⟩ := hz
  interval_cases z <;> norm_num [Parts.Width,Parts.literal]
  all_goals decide


private theorem cube_bounds (column : Fin 24) (k : Fin 3) :
    -1≤corner column k ∧ corner column k≤0 := by
  unfold corner rationalCubeAlias
  split_ifs <;> norm_num

private theorem shift_bounds (column : Fin 24) (axis k : Fin 3) :
    (-2≤(corner column-unitAlias axis) k ∧ (corner column-unitAlias axis) k≤1) ∧
    (-2≤(corner column+unitAlias axis) k ∧ (corner column+unitAlias axis) k≤1) := by
  have h := cube_bounds column k
  by_cases he : axis=k
  · subst k
    simp only [Pi.sub_apply,Pi.add_apply,unitAlias,Pi.single_eq_same]
    omega
  · simp only [Pi.sub_apply,Pi.add_apply,unitAlias,Pi.single_eq_of_ne (Ne.symm he),sub_zero,add_zero]
    omega


private theorem weight_width (axis : Fin 3) :
    (Parts.literal (-rationalAmplitude*rationalWeight axis)).Width 103 := by
  fin_cases axis <;> norm_num [rationalAmplitude,rationalWeight,Parts.Width,Parts.literal]
  all_goals decide


private theorem literal_bounds (column : Fin 24) : PointSupport.LiteralsFit (support column) 103 := by
  intro p hp
  simp only [support,List.mem_append,List.mem_ofFn] at hp
  rcases hp with ⟨axis,rfl⟩|⟨axis,rfl⟩
  all_goals constructor
  case inl.left =>
    apply distance_literals
    simp only [weightedKey,key,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    refine ⟨coordinate_width _ (shift_bounds column axis 0).1,
      coordinate_width _ (shift_bounds column axis 1).1,
      coordinate_width _ (shift_bounds column axis 2).1,?_⟩
    generalize polarization column=j
    fin_cases j <;> norm_num [Parts.Width,Parts.literal]
    all_goals decide
  case inr.left =>
    apply distance_literals
    simp only [weightedKey,key,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    refine ⟨coordinate_width _ (shift_bounds column axis 0).2,
      coordinate_width _ (shift_bounds column axis 1).2,
      coordinate_width _ (shift_bounds column axis 2).2,?_⟩
    generalize polarization column=j
    fin_cases j <;> norm_num [Parts.Width,Parts.literal]
    all_goals decide
  all_goals
    simp only [weightedKey]
    split_ifs
    · exact zero_width
    · exact weight_width axis

theorem literals (column : Fin 24) (B : ℕ) (hB : 103≤B) :
    PointSupport.LiteralsFit (support column) B := by
  intro p hp
  have h := literal_bounds column p hp
  refine ⟨?_,h.2.mono hB⟩
  have monotone : ∀e : PolynomialExpression,e.LiteralsFit 103 → e.LiteralsFit B := by
    intro e
    induction e with
    | literal q => exact fun hh => hh.mono hB
    | inputRegister => exact id
    | binary op x y hx hy => exact fun hh => ⟨hx hh.1,hy hh.2⟩
  exact monotone _ h.1

theorem executes (column : Fin 24) (B : ℕ) (hB : 103≤B) (v : ℕ → Parts)
    (hw : WidthBank (Finset.range 232) B v) (hg : Good (Finset.range 232) v)
    (ν : Alias) (j : Fin 3)
    (hcoord : (v 13).value=(ν 0:ℚ) ∧ (v 14).value=(ν 1:ℚ) ∧ (v 15).value=(ν 2:ℚ))
    (hpol : (v 23).value=(j.val:ℚ))
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready (Finset.range 232) v s) :
    ∃cost t output,Executes input tape (code column) cost s t ∧ cost≤2^650*(B+1)^2 ∧
      Ready (Finset.range 232) output t ∧ Good (Finset.range 232) output ∧
      WidthBank (Finset.range 232) (2^265*(B+1)) output ∧ (output 32).Width 625 ∧
      (output 32).value=rationalRightCoupling (rationalBasisField column) ν j ∧
      (∀i,i<32 → output i=v i) ∧
      BinaryPrecision.Frame (workspace (Finset.range 232)) s.val t.val := by
  have hw' : WidthBank (PointSupport.registers (support column) 32) B v := by
    simpa only [registers_eq] using hw
  have hg' : Good (PointSupport.registers (support column) 32) v := by
    simpa only [registers_eq] using hg
  have hs' : Ready (PointSupport.registers (support column) 32) v s := by
    simpa only [registers_eq] using hs
  obtain ⟨c,t,out,e,hc,ready,good,width,result,keep,raw,frame⟩ :=
    PointSupport.executes (support column) 32 B (support_scoped column) (by omega)
      (literals column B hB) v hw' hg' input tape s hs'
  have coefficient : costCoefficient (support column) 32≤2^650 := by
    simp only [costCoefficient,steps_eq]
    norm_num
  refine ⟨c,t,out,e,hc.trans (Nat.mul_le_mul_right _ coefficient),?_,?_,?_,?_,
    result.trans (value_correct column ν j (valueBank v) hcoord hpol),keep,?_⟩
  · simpa only [registers_eq] using ready
  · simpa only [registers_eq] using good
  · simpa only [registers_eq,PointSupport.width,steps_eq] using width
  · rw [raw]
    have h := PointSupport.accumulator_width (support column) 32 103 v
      (fun p hp => (literals column 103 le_rfl p hp).2)
    simpa only [support,List.length_append,List.length_ofFn,Fintype.card_fin] using h
  · simpa only [registers_eq] using frame

#print axioms executes
end Maxwell.Continuum.Calibration.BasisForcing
