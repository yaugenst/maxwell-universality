import Maxwell.Cost.RealSparseOrder.ColumnMaxPure
import Maxwell.Cost.RealSparseOrder.PureSort

namespace Maxwell.Cost.RealSparseOrder.ColumnMax

theorem columnCount_perm {es fs : List SparseEntry} (h : es.Perm fs) :
    columnCount es=columnCount fs := by
  apply Nat.le_antisymm
  · exact columnCount_le es _ (fun e he=>column_lt fs e (h.mem_iff.mp he))
  · exact columnCount_le fs _ (fun e he=>column_lt es e (h.mem_iff.mpr he))

theorem columnCount_bottomUpSort (es : List SparseEntry) :
    columnCount (bottomUpSort es)=columnCount es :=
  columnCount_perm (bottomUpSort_perm es)

end Maxwell.Cost.RealSparseOrder.ColumnMax
