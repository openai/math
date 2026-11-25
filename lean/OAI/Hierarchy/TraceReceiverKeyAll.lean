import OAI.Hierarchy.TraceDistributionScale
import OAI.ThreeFlat.Diagonal.TraceBitAddresses
import OAI.ThreeFlat.Diagonal.TraceBitRecordWord
import OAI.ThreeFlat.Diagonal.NativeTrace

namespace OAI
/-! # Word capacity of receiver keys at every sufficiently large physical width -/

namespace Hierarchy.TraceReceiverKeyBounds

open Filter ThreeFlat Diagonal TraceAddressRecord Computability.VPVNP.BurstRAM PrivateRAM

/-- At depth at most half a word the row count and all public per-row address
fields together fit strictly below the ambient word cap. -/
theorem eventually_port_capacity :
    ∀ᶠ W : ℕ in atTop, ∀ d p r k : ℕ, d ≤ W/2 → p ≤ W → r ≤ W → k ≤ W →
      40*(2^d * portRowWords W p r k d) < 2^W := by
  filter_upwards [TraceDistribution.polynomial_room 5120 4, eventually_ge_atTop 2] with W room large
  intro d p r k hd hp hr hk
  have row : portRowWords W p r k d ≤ 128*(W+1)^4 := by
    exact portRowWords_polynomial (c:=1) (e:=1) (show d ≤ W by omega)
      (by simpa using hp.trans (Nat.le_succ W)) (by simpa using hr.trans (Nat.le_succ W))
      (by simpa using hk.trans (Nat.le_succ W))
  calc
    40*(2^d * portRowWords W p r k d) ≤ 40*(2^d * (128*(W+1)^4)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ row)
    _ = 2^d * (5120*(W+1)^4) := by ring
    _ ≤ 2^d * 2^(W/100) := Nat.mul_le_mul_left _ room
    _ = 2^(d+W/100) := (pow_add (2 : ℕ) d (W/100)).symm
    _ < 2^W := Nat.pow_lt_pow_right (by decide) (by omega)

/-- The key validity assertion for the actual physical port dictionary. -/
def KeysFitAt (W : ℕ) : Prop :=
  ∀ {pc regs slots S base d fuel : ℕ} (M : Machine W pc regs slots)
    (fit : NativeTrace.Fits M S base d fuel), d ≤ W/2 → pc ≤ W → regs ≤ W → slots ≤ W →
    ∀ (v : Fin (2^d)) i, (TraceBitDescriptor.records (p:=pc) (r:=regs) (k:=slots) (d:=d)
      fit.width base S fuel i).Fits W v.val

theorem eventually_keysFit : ∀ᶠ W : ℕ in atTop, KeysFitAt W := by
  filter_upwards [eventually_port_capacity] with W room
  intro pc regs slots S base d fuel M fit hd hp hr hs v i
  exact staticBitPort_fits_of_capacity fit.width fit.grid fit.mount (room _ _ _ _ hd hp hr hs)
    v ((Fintype.equivFin _).symm i)

/-- In particular every sufficiently large scale with a literal 64-word
expansion has valid keys for every native machine of the stated dimensions. -/
theorem eventually_literal : ∀ᶠ w : ℕ in atTop, KeysFitAt (64*w) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp eventually_keysFit
  filter_upwards [eventually_ge_atTop N] with w hw
  exact hN _ (by omega)


end Hierarchy.TraceReceiverKeyBounds

end OAI
