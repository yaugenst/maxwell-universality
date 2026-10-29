import Maxwell.Certificate.Trigonometric

/-! Three actual 48-bit phase rectangles from the global certificate producer.
Their acceptance is reduced by Lean's kernel, without a native-evaluation axiom. -/

namespace Maxwell.Certificate.Trigonometric

def sourceRectangle48 (re im : ℤ) : ComplexRectangle :=
  ⟨⟨re / (2 : ℚ)^48, 1 / (2 : ℚ)^48, by positivity⟩,
   ⟨im / (2 : ℚ)^48, 1 / (2 : ℚ)^48, by positivity⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem first_center_phase_accepted :
    cisCheck (3 / 640) (sourceRectangle48 281352903406362 8288923879141) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem root_phase_accepted :
    cisCheck (1 / 20) (sourceRectangle48 267698610774695 86980551294885) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem reverse_phase_accepted :
    cisCheck (19 / 20) (sourceRectangle48 267698610774695 (-86980551294886)) = true := by
  decide +kernel

theorem first_center_phase_contains :
    (sourceRectangle48 281352903406362 8288923879141).Contains (cis (3 / 640)) :=
  cisCheck_sound first_center_phase_accepted

theorem root_phase_contains :
    (sourceRectangle48 267698610774695 86980551294885).Contains (cis (1 / 20)) :=
  cisCheck_sound root_phase_accepted

theorem reverse_phase_contains :
    (sourceRectangle48 267698610774695 (-86980551294886)).Contains (cis (19 / 20)) :=
  cisCheck_sound reverse_phase_accepted

end Maxwell.Certificate.Trigonometric
