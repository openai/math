import OAI.Computability.VPVNP.PairRefreshSelectedParser

/-! # Uniform capacity for all refresh rows of the actual selected execution -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.SelectedRows

open Compression CompressorRecords DescriptorSpace TraversalRows TraversalRoles ShrinkRoleDirectory
open LocalHistory CursorBounds CursorNetwork Filter

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Every refresh row on every true branch meets the packet and private map
capacity. The threshold is chosen before the coefficient specialization,
selector tape, selected level and output port. -/
theorem eventually_rooms (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    {workspace : ℕ → ℕ} (bounded : PolynomiallyBounded workspace) (hist : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ}
      (split : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
      (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (K : Type*) [CommRing K] (f : B.Entry → K) (hf : B.IsSolution f),
      let Z := pairInput S split hD
      let count := blockCount (u.θ : ℝ) n
      ∀ z : (B.execute f hf count hT Z).Choices,
        let passes := executeLevels B f hf count hT Z z
        Rooms n hist (wordBits b n) (workspace n) (initialPositions b n) count
          ⟨leafLayer (siteOrder Z), .cursor⟩ passes := by
  filter_upwards [PortRefresh.TraversalPlan.eventually_selected_room B u b hb bounded hist] with n cap
  intro base lanes split hD hT K _ f hf Z count z passes x
  let O := x.occurrence
  let tags := selected B f hf count hT Z z
  let row := siteRows passes x.val
  let j : Fin tags.length := row.1.succ
  let id : Fin tags[j].layer.count := row.2
  have parentLayer : j.val = x.val.1.val + 1 := rfl
  have sameId : id.val = (PortRefresh.NewSlots.sites O.state.baseIndex (bitWordFinEquiv O.lanes) O.port).val :=
    O.ordinal.symm
  have rowEnd : tagWords B.recordLimit tags = words B.recordLimit (selectedLayers B f hf count hT Z z) := by
    rw [tagWords, selected_layers]
  have fits := (cap split hD hT K f hf z O.state O.choice passes[x.val.1].selector
    x.val.1 O.selected j parentLayer id O.port).2.2
  rw [← rowEnd, sameId] at fits
  exact fits

end PairSimulation.RefreshHook.SelectedRows

end VPVNP
end Computability
end OAI
