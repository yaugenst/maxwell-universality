import Maxwell.Cost.SparseEmission.GateBinding

namespace Maxwell.Cost.SparseEmission

theorem gateBytes_length (width : ℕ) (gate : Logical.GateRecord) (bytes : List Bool)
    (hbytes : SourceCircuit.gateBytes width gate = some bytes) : bytes.length ≤ 2*width+3 := by
  obtain ⟨kind,rfl⟩ := ReadGate.exists_kind width gate bytes hbytes
  rw [← ReadGate.kind_wire_eq width kind bytes hbytes]
  cases kind <;> simp [ReadGate.wire,ReadGate.payload,ReadGate.Kind.a,ReadGate.Kind.b,ReadGate.Kind.c] <;> omega

theorem traceBytes_length (width : ℕ) (gates : List Logical.GateRecord) (bytes : List Bool)
    (hbytes : SourceCircuit.traceBytes width gates = some bytes) :
    bytes.length ≤ gates.length*(2*width+3) := by
  induction gates generalizing bytes with
  | nil => have hb : bytes = [] := by simpa [SourceCircuit.traceBytes] using hbytes.symm
           simp [hb]
  | cons gate rest ih =>
    cases hh : SourceCircuit.gateBytes width gate with
    | none => simp [SourceCircuit.traceBytes,hh] at hbytes
    | some head =>
      cases ht : SourceCircuit.traceBytes width rest with
      | none => simp [SourceCircuit.traceBytes,hh,ht] at hbytes
      | some tail =>
        have hb : head++tail = bytes := by simpa [SourceCircuit.traceBytes,hh,ht] using hbytes
        have he := gateBytes_length width gate head hh
        have hr := ih tail ht
        rw [← hb,List.length_append,List.length_cons]
        nlinarith

end Maxwell.Cost.SparseEmission
