import Maxwell.Certificate.ProjectionWitness.UpperResult22
import Maxwell.Certificate.PointInertia.FieldNorm
namespace Maxwell.Certificate.FieldNormWitness
open DyadicRectangle FourierBinding PointInertia ProjectionWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def UpperField22Rows : Fin 20 → ℤ := ![26625123669893036664264107002005, 8848707839635473947134746211003, 12452921230409972138299879721678, 604427673662206173391194813279, 155731292314915888791414728382, 86784916062743745957468791855, 19361849446367838511316610774, 22989824568233635740233606876, 6459583165641642477767772822, 9156597845258972710053421662, 9156597845259109003372834667, 6459583165641507425198726245, 22989824568234060107460033008, 19361849446367550440966043170, 86784916062746317527249122326, 155731292314917467091903052469, 604427673662222064295403034419, 12452921230410127124350542301272, 8848707839635605390565204832561, 26625123669892657754713074282232]
theorem UpperField22X0 : highNormUpperX UpperResult22 0 = UpperField22Rows 0 := by decide +kernel
theorem UpperField22X1 : highNormUpperX UpperResult22 1 = UpperField22Rows 1 := by decide +kernel
theorem UpperField22X2 : highNormUpperX UpperResult22 2 = UpperField22Rows 2 := by decide +kernel
theorem UpperField22X3 : highNormUpperX UpperResult22 3 = UpperField22Rows 3 := by decide +kernel
theorem UpperField22X4 : highNormUpperX UpperResult22 4 = UpperField22Rows 4 := by decide +kernel
theorem UpperField22X5 : highNormUpperX UpperResult22 5 = UpperField22Rows 5 := by decide +kernel
theorem UpperField22X6 : highNormUpperX UpperResult22 6 = UpperField22Rows 6 := by decide +kernel
theorem UpperField22X7 : highNormUpperX UpperResult22 7 = UpperField22Rows 7 := by decide +kernel
theorem UpperField22X8 : highNormUpperX UpperResult22 8 = UpperField22Rows 8 := by decide +kernel
theorem UpperField22X9 : highNormUpperX UpperResult22 9 = UpperField22Rows 9 := by decide +kernel
theorem UpperField22X10 : highNormUpperX UpperResult22 10 = UpperField22Rows 10 := by decide +kernel
theorem UpperField22X11 : highNormUpperX UpperResult22 11 = UpperField22Rows 11 := by decide +kernel
theorem UpperField22X12 : highNormUpperX UpperResult22 12 = UpperField22Rows 12 := by decide +kernel
theorem UpperField22X13 : highNormUpperX UpperResult22 13 = UpperField22Rows 13 := by decide +kernel
theorem UpperField22X14 : highNormUpperX UpperResult22 14 = UpperField22Rows 14 := by decide +kernel
theorem UpperField22X15 : highNormUpperX UpperResult22 15 = UpperField22Rows 15 := by decide +kernel
theorem UpperField22X16 : highNormUpperX UpperResult22 16 = UpperField22Rows 16 := by decide +kernel
theorem UpperField22X17 : highNormUpperX UpperResult22 17 = UpperField22Rows 17 := by decide +kernel
theorem UpperField22X18 : highNormUpperX UpperResult22 18 = UpperField22Rows 18 := by decide +kernel
theorem UpperField22X19 : highNormUpperX UpperResult22 19 = UpperField22Rows 19 := by decide +kernel
theorem UpperField22_rows (x : Fin 20) : highNormUpperX UpperResult22 x = UpperField22Rows x := by
  fin_cases x
  · exact UpperField22X0
  · exact UpperField22X1
  · exact UpperField22X2
  · exact UpperField22X3
  · exact UpperField22X4
  · exact UpperField22X5
  · exact UpperField22X6
  · exact UpperField22X7
  · exact UpperField22X8
  · exact UpperField22X9
  · exact UpperField22X10
  · exact UpperField22X11
  · exact UpperField22X12
  · exact UpperField22X13
  · exact UpperField22X14
  · exact UpperField22X15
  · exact UpperField22X16
  · exact UpperField22X17
  · exact UpperField22X18
  · exact UpperField22X19
theorem UpperField22_bound : highNormUpper UpperResult22 ≤ 97663328954007628992798556942705 :=
  highNormUpper_le_of_rows UpperResult22 UpperField22Rows 97663328954007628992798556942705 UpperField22_rows (by decide +kernel)
end Maxwell.Certificate.FieldNormWitness
