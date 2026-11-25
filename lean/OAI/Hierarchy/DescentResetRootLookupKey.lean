import OAI.Hierarchy.DescentIssuedRootWidths
import OAI.Hierarchy.DescentPreparedRootPrice

namespace OAI
/-! # Maximum lookup exponent of the physical installed root table -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentPackedWalsh DescentPlainTerminal.Suffix DescentPackedColony DescentSIMDLookup DescentResetGates
open DescentPackedPrivateMenu DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr) (f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "book" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "args" => arityLimit D (2^r) cap n r

theorem issued_lookup (batch : ℕ) : (book).addressBits batch≤(field*(args+1))*batch := by
  apply Finset.sup_le
  intro p _
  have row:=a.issued_arity E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage p
  change ((((book).table p).2.field*((book).table p).1+((book).table p).2.field)*batch)≤_
  rw [row.2,Nat.mul_succ]
  exact Nat.mul_le_mul_right batch (Nat.add_le_add_right (Nat.mul_le_mul_left field row.1) field)

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
