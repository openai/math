import OAI.Hierarchy.DescentResetAtlasRoom
import OAI.Hierarchy.DescentGLPackedBlocks
import OAI.Hierarchy.DescentDatedOperandHeader

namespace OAI
/-! # The previous signed slots at the true start of the selected reset root program -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod DescentGLPacked DescentGLPacked.BankImage
open DescentPackedColony DescentSIMDLookup DescentPlainTerminal.Suffix
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (roots : a.RootInputs)
local notation "P₀" => a.stencilPhase sh floor count hub g Y
local notation "r₀" w => a.rootPhase sh floor count hub g Y roots w
local notation "d₀" => a.successor.middle
local notation "H₀" => (d₀).signedHosts
local notation "M₀" => (d₀).signedLanes
local notation "G₀" => (d₀).rootGroups
local notation "S₀" => (d₀).stencil

/-- The old stage's signed bank geometry and the next estimator's dyadic pitch are sufficient
for the retile, saved-matrix lookup, old-sign GL stream and all root-window projection instructions. -/
theorem atlas_prefix {w : ℕ} (shape : a.RootShape)
    (old : ∀j x,(roots.old j x).Fits w (P₀).endAddress)
    (space : ∀j x,H₀*chunks G₀ ((d₀).signedRatio*M₀) ≤ (roots.old j x).size)
    (high : (S₀).c=(d₀).high+a.e) (batch : M₀=2^a.e)
    (width : M₀*max (Projected.maxBits (S₀).t a.ports (a.c/2) (2^(d₀).rootDepth)) roots.field ≤ w/2)
    (last : (r₀ w).projectionEnd < 2^w) : (r₀ w).PrefixFits := by
  let Q := r₀ w
  have origin : Q.origin ≤ Q.retileEnd := by
    unfold Projected.Receiver.retileEnd SignedFields.Retile.stop Subwords.destination
    omega
  have sign : Q.retileEnd ≤ Q.signedEnd := by
    have step : Q.retileEnd ≤ Q.signedOrigin := Nat.le_add_right ..
    have after : Q.signedOrigin ≤ Q.signedEnd := by
      unfold Projected.Receiver.signedEnd SignedFields.stop
      simp only [Dated.extent, Nat.add_assoc]
      exact Nat.le_add_right ..
    exact step.trans after
  have signedRoom : Q.signedEnd < 2^w := (Nat.le_add_right ..).trans_lt last
  have stamp : (P₀).saved+1 ≤ Q.origin := by
    have picked : (P₀).first ≤ (P₀).base := by
      unfold PackedFlow.ResetMiddle.base Subwords.finish Subwords.destination
      omega
    have after : (P₀).base ≤ (P₀).endAddress := by
      simp only [PackedFlow.ResetMiddle.endAddress, (P₀).S.extent, Nat.add_assoc]
      exact Nat.le_add_right ..
    exact picked.trans after
  have saved : Q.saved.Fits w Q.retileEnd := by
    have bound := stamp.trans origin
    have room := bound.trans_lt (sign.trans_lt signedRoom)
    exact ⟨Nat.two_pow_pos _,by change 2^0 < 2^w; omega,by simpa [Q,rootPhase,Bank.size] using bound⟩
  let rows := H₀*chunks (2^(S₀).c) M₀
  have outputLE : (P₀).output ≤ Q.origin := by
    change (P₀).S.output (P₀).base ≤ (P₀).S.endAddress (P₀).base
    rw [StencilBook.output_end]
    exact Nat.le_add_right ..
  have rounded : (P₀).output+2^(Nat.clog 2 rows) ≤ Q.retileEnd := by
    have newRoom : SignedFields.Retile.pitch H₀ G₀ M₀ ≤
        ((2*(a.c/2))*(d₀).oldBlocks+1)*SignedFields.Retile.pitch H₀ G₀ M₀ := by
      apply Nat.le_mul_of_pos_left
      omega
    have beginRetile : Q.origin ≤ Subwords.destination Q.origin (DescentSignedCableCodec.width a.ports (a.c/2))
        H₀ G₀ (d₀).signedRatio M₀ := Nat.le_add_right ..
    have paid := Nat.add_le_add (outputLE.trans beginRetile) newRoom
    simpa only [Q,Projected.Receiver.retileEnd,SignedFields.Retile.stop,SignedFields.Retile.pitch,shape.groups,rows]
      using paid
  have stencil : Q.stencil.Fits w Q.signedEnd := by
    have bound := rounded.trans sign
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bound.trans_lt signedRoom),bound⟩
  have length : chunks (2^(S₀).c) M₀=2^(d₀).high := by
    rw [high,batch]
    exact DescentGLPacked.chunk_count _ _
  exact Q.prefix_fits old space saved stencil (Nat.le_pow_clog (by decide) _) length width last

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
