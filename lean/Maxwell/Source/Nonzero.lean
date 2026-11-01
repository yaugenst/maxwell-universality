import Maxwell.Source

namespace Maxwell.Source

theorem dimension_pos_of_source_ne_zero (S : SparseSystem) (hb : S.source≠0) : 0<S.n := by
  by_contra hn
  apply hb
  funext i
  have hi:=i.isLt
  omega

#print axioms dimension_pos_of_source_ne_zero
end Maxwell.Source
