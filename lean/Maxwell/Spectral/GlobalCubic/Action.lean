import Maxwell.Spectral.GlobalCubic.Raw

namespace Maxwell.Spectral.GlobalCubic
open PeriodicYee
open PrimitiveYee (RawCell rawUnit)
open scoped Matrix
set_option maxHeartbeats 1800000

inductive Generator where
  | swap01 | swap12 | reflect0
  deriving DecidableEq

def linear (g : Generator) (r : RawCell) : RawCell := match g with
  | .swap01 => ![r 1,r 0,r 2]
  | .swap12 => ![r 0,r 2,r 1]
  | .reflect0 => ![-r 0,r 1,r 2]

def node (g : Generator) (a : ℤ) (r : RawCell) : RawCell :=
  linear g r + if g = .reflect0 then ![0,a,a] else 0

def unitImage (g : Generator) (j : Direction) : RawCell := match g with
  | .swap01 => rawUnit (![1,0,2] j)
  | .swap12 => rawUnit (![0,2,1] j)
  | .reflect0 => if j=0 then -rawUnit 0 else rawUnit j

theorem node_add_unit (g : Generator) (a : ℤ) (r : RawCell) (j : Direction) :
    node g a (r+rawUnit j) = node g a r+unitImage g j := by
  cases g <;> fin_cases j <;> funext i <;> fin_cases i <;>
    norm_num [node, linear, unitImage, rawUnit, Pi.single_apply] <;> ring

theorem node_sub_unit (g : Generator) (a : ℤ) (r : RawCell) (j : Direction) :
    node g a (r-rawUnit j) = node g a r-unitImage g j := by
  cases g <;> fin_cases j <;> funext i <;> fin_cases i <;>
    norm_num [node, linear, unitImage, rawUnit, Pi.single_apply] <;> ring

noncomputable section

def edgeAction (g : Generator) (a : ℤ) (v : RawField) : RawField := match g with
  | .swap01 => ![fun r => v 1 (node g a r),fun r => v 0 (node g a r),fun r => v 2 (node g a r)]
  | .swap12 => ![fun r => v 0 (node g a r),fun r => v 2 (node g a r),fun r => v 1 (node g a r)]
  | .reflect0 => ![fun r => -v 0 (node g a r-rawUnit 0),fun r => v 1 (node g a r),fun r => v 2 (node g a r)]

def faceAction (g : Generator) (a : ℤ) (v : RawField) : RawField := match g with
  | .swap01 => ![fun r => -v 1 (node g a r),fun r => -v 0 (node g a r),fun r => -v 2 (node g a r)]
  | .swap12 => ![fun r => -v 0 (node g a r),fun r => -v 2 (node g a r),fun r => -v 1 (node g a r)]
  | .reflect0 => ![fun r => v 0 (node g a r),fun r => -v 1 (node g a r-rawUnit 0),fun r => -v 2 (node g a r-rawUnit 0)]

theorem curl_edgeAction (g : Generator) (a : ℤ) (v : RawField) :
    rawCurl (edgeAction g a v) = faceAction g a (rawCurl v) := by
  funext j r
  cases g <;> fin_cases j <;>
    simp [rawCurl, edgeAction, faceAction, derivative, node_add_unit, unitImage] <;>
    simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] <;> ring

theorem adjoint_faceAction (g : Generator) (a : ℤ) (v : RawField) :
    rawCurlAdjoint (faceAction g a v) = edgeAction g a (rawCurlAdjoint v) := by
  funext j r
  cases g <;> fin_cases j <;>
    simp [rawCurlAdjoint, edgeAction, faceAction, adjDerivative, node_sub_unit, unitImage] <;>
    simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] <;> ring

theorem gram_edgeAction (g : Generator) (a : ℤ) (v : RawField) :
    rawCurlAdjoint (rawCurl (edgeAction g a v)) = edgeAction g a (rawCurlAdjoint (rawCurl v)) := by
  rw [curl_edgeAction, adjoint_faceAction]

end
end Maxwell.Spectral.GlobalCubic
