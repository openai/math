import OAI.Hierarchy.DescentRecordedRootBook

namespace OAI
/-! # Common word pitch for all actual reset root menus -/
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
local notation "L" => 2^r
local notation "Book" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "W₀" => DescentRotorWindowArchive.output n L cap
local notation "W₁" u => fieldBits board r Ht (L*(2*cap)) u C packet*
  ((max (Fintype.card (DescentCommonPalette.rotor board).Edge) (2^(Ht+1)))*5)
def arityLimit (D width cap n r : ℕ) :=
  max (DescentIssuedRotorRoles.guardInputs D width cap) (inputCount D width cap n r)

theorem issued_arity (p : RootPage r (2^n)) :
    ((Book).table p).1≤ arityLimit D L cap n r ∧ ((Book).table p).2.field=field := by
  rcases p with ⟨_,(⟨root,j⟩|root)⟩
  · cases j with
    | inl flag=>
      cases flag
      · exact ⟨(Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (le_max_left ..)),rfl⟩
      · refine ⟨?_,rfl⟩
        have room:3≤ DescentIssuedRotorRoles.guardInputs D L cap:=by unfold DescentIssuedRotorRoles.guardInputs;omega
        exact room.trans (le_max_left ..)
    | inr gate=> exact ⟨le_max_left ..,rfl⟩
  · exact ⟨le_max_right ..,rfl⟩

theorem issued_output (p : RootPage r (2^n)) :
    ((Book).table p).2.outputBits≤ max (max W₀ (bit*batches)) (max (W₁ 0) (W₁ layerBits)) := by
  rcases p with ⟨_,(⟨root,j⟩|root)⟩
  · cases j with
    | inl flag=>
      cases flag
      · exact (le_max_left ..).trans (le_max_left ..)
      · exact (le_max_right ..).trans (le_max_right ..)
    | inr gate=> exact (le_max_right ..).trans (le_max_left ..)
  · change (W₁ layerBits) ≤ _
    exact (le_max_right ..).trans (le_max_right ..)

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
