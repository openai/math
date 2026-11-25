import OAI.Hierarchy.DescentResetTrunkStemTables
import OAI.Hierarchy.DescentResetStemProjected

namespace OAI
/-! # Reuse the broadcast tables on the true projected signed-stem image -/
namespace Hierarchy.DescentResetStemPackedIssue.Mixed.Projected
open DescentSIMDLookup DescentDyadicSpan DescentResetStemIncidence DescentResetStemHeaders
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D f Q K w : ℕ} (base ptr b P H G X M₀ M : ℕ)
variable (parse : DescentResetStemKey.Decoder D f) (side : Fin Q→Bool)
  (src : Fin Q→Fin (D+2)→Expr) (ports : Ports (2*K))
local notation "split₀" => splitAt base Q D P G X f M₀ M
local notation "A₀" => plan split₀ ptr K H
local notation "head₀" => (A₀).hdr D f M P H G (X*Q)
local notation "end₀" => extent base ptr D f b K P H G X M₀ M Q

theorem header_image (initial : Memory w) (limit : end₀<2^w) :
    TablesOK H G M (b*7) head₀ (image base ptr b P H G X M₀ M parse side src ports initial):=
  (A₀).header_stays parse (direction X side) (operand base Q D P G X f M₀ M) _ limit

/-- The existing receiver-mask table includes a dyadic row page. Its end
therefore leaves room for the regular one-column broadcast at every date. -/
theorem header_borders :
    base≤head₀ ∧
      outputBase H G M (b*7) head₀+H*chunks G M≤end₀ ∧
      (A₀).out D f (b*7) K M P H G (X*Q)+(X*Q)*(H*chunks G M)=end₀:=by
  have first : base ≤ split₀ := by
    unfold splitAt
    rw [DescentResetStemProject.extent base]
    exact Nat.le_add_right _ _
  have cap:=span_ge (H*chunks G M)
  refine ⟨?_,?_,rfl⟩
  · unfold Layout.hdr Layout.mapping DescentResetStemKey.Columns.stop DescentResetStemKey.Columns.start plan
    dsimp only
    omega
  · change _≤(A₀).stop D f (b*7) K M P H G (X*Q)
    unfold Layout.stop Layout.out Layout.mux
    omega

end
end Hierarchy.DescentResetStemPackedIssue.Mixed.Projected

end OAI
