import Maxwell.Continuum.CalibrationFiniteDataExt
import Maxwell.Continuum.CalibrationGlobalCoordinates
import Maxwell.Continuum.RationalDataflowArray

/-! One authoritative conversion from a stored rational coefficient table
to finite Fourier data, shared by seed production and mode normalization. -/
namespace Maxwell.Continuum.Calibration.GlobalPower
open RationalDataflow.PartArray

def tableData (R : ℕ) (b : Table (2*aliasArraySize R)) : FourierData :=
  ⟨R,unpack R (fun i => (b.get i).value)⟩

theorem tableData_eq (R : ℕ) (b : Table (2*aliasArraySize R)) (v : FourierData)
    (radius : v.radius=R) (values : ∀i,(b.get i).value=sample R v.field i) : tableData R b=v := by
  apply FourierData.eq_of_radius_field radius.symm
  change embed R (fun i=>(b.get i).value)=v.field
  rw [funext values]
  apply embed_sample
  simpa only [radius] using v.supported

#print axioms tableData_eq
end Maxwell.Continuum.Calibration.GlobalPower
