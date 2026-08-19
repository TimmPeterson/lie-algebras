import LieRings.DimensionSubring.MetabelianVanishing.RawCutoffExceptionalSupport
#check smul_zero
#check zsmul_zero
#check zero_zsmul
#check zero_smul
example {M : Type*} [AddCommGroup M] (z : ℤ) : z • (0 : M) = 0 := by
  exact zsmul_zero z
