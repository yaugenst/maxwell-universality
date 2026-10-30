import Maxwell.Continuum.SourceRoutingPortIndices

/-! The computed arithmetic addresses are injective on the actual bounded
degree incidence data and on the paired destination enumeration. -/

namespace Maxwell.Cost.RoutingPorts.Complete.PortIndices
open Maxwell.Logical.Routing Maxwell.Logical.Routing.Gluing
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

def sourcePort {vertices k : ℕ} (half : ℕ) (hroom : vertices≤half*half)
    (endpoint : Fin k→Fin vertices) (rank : Fin k→Fin 3) (i : Fin k) : Fin ((2*half)*(2*half)) :=
  finProdFinEquiv (tilePort (finProdFinEquiv.symm (Fin.castLE hroom (endpoint i))) (rank i))

theorem sourcePort_value {vertices k : ℕ} (half : ℕ) (hroom : vertices≤half*half)
    (endpoint : Fin k→Fin vertices) (rank : Fin k→Fin 3) (i : Fin k) :
    (sourcePort half hroom endpoint rank i).val=sourceIndex half (endpoint i).val (rank i).val :=
  source_exact half (Fin.castLE hroom (endpoint i)) (rank i)

theorem sourcePort_injective {vertices k : ℕ} (half : ℕ) (hroom : vertices≤half*half)
    (endpoint : Fin k→Fin vertices) (rank : Fin k→Fin 3)
    (hpair : Function.Injective (fun i => (endpoint i,rank i))) :
    Function.Injective (sourcePort half hroom endpoint rank) := by
  intro a b hab
  have ht := tilePort_injective half
    (a₁ := (finProdFinEquiv.symm (Fin.castLE hroom (endpoint a)),rank a))
    (a₂ := (finProdFinEquiv.symm (Fin.castLE hroom (endpoint b)),rank b))
    (finProdFinEquiv.injective hab)
  have hv := finProdFinEquiv.symm.injective (congrArg Prod.fst ht)
  apply hpair
  exact Prod.ext (Fin.ext (congrArg (fun x : Fin (half*half) => x.val) hv))
    (congrArg (fun p : Port half×Fin 3 => p.2) ht)

def edgeIndex (half : ℕ) (i : Fin (2*(half*(2*half)))) : Fin (half*(2*half)) :=
  ⟨i.val/2,(Nat.div_lt_iff_lt_mul (by decide)).mpr (by have := i.isLt; omega)⟩
def side (i : ℕ) : Bool := decide (i%2=1)

theorem side_value (i : ℕ) : (if side i then 1 else 0)=i%2 := by
  have h := Nat.mod_lt i (by decide : 0<2)
  simp only [side,Bool.decide_iff]
  split_ifs <;> omega

theorem edge_side_value (half : ℕ) (i : Fin (2*(half*(2*half)))) :
    2*(edgeIndex half i).val+(if side i.val then 1 else 0)=i.val := by
  rw [side_value]
  simpa only [edgeIndex,Nat.mul_comm] using Nat.div_add_mod' i.val 2

theorem targetIndex_injective (half : ℕ) :
    Function.Injective (fun i : Fin (2*(half*(2*half))) => targetIndex half i.val) := by
  intro a b hab
  have ha := pair_exact half (edgeIndex half a) (side a.val)
  have hb := pair_exact half (edgeIndex half b) (side b.val)
  rw [edge_side_value] at ha hb
  have hport : pairPort (finProdFinEquiv.symm (edgeIndex half a)) (side a.val)=
      pairPort (finProdFinEquiv.symm (edgeIndex half b)) (side b.val) :=
    finProdFinEquiv.injective (Fin.ext (ha.trans (hab.trans hb.symm)))
  have hpair := pairPort_injective half
    (a₁ := (finProdFinEquiv.symm (edgeIndex half a),side a.val))
    (a₂ := (finProdFinEquiv.symm (edgeIndex half b),side b.val)) hport
  have hedge := finProdFinEquiv.symm.injective (congrArg Prod.fst hpair)
  have hside : side a.val=side b.val := congrArg (fun p : (Fin half×Fin (2*half))×Bool => p.2) hpair
  apply Fin.ext
  rw [←edge_side_value half a,←edge_side_value half b,hedge,hside]

def targetPort {k : ℕ} (half : ℕ) (hroom : k≤2*(half*(2*half))) (i : Fin k) :
    Fin ((2*half)*(2*half)) :=
  ⟨targetIndex half i.val,target_lt half i.val (lt_of_lt_of_le i.isLt hroom)⟩

theorem targetPort_injective {k : ℕ} (half : ℕ) (hroom : k≤2*(half*(2*half))) :
    Function.Injective (targetPort half hroom) := by
  intro a b hab
  have he : (Fin.castLE hroom a : Fin (2*(half*(2*half))))=Fin.castLE hroom b :=
    targetIndex_injective half (congrArg Fin.val hab)
  exact Fin.ext (congrArg (fun x : Fin (2*(half*(2*half))) => x.val) he)

#print axioms sourcePort_injective
#print axioms targetPort_injective

end Maxwell.Cost.RoutingPorts.Complete.PortIndices
