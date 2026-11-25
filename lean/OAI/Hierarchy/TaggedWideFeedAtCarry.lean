import OAI.Hierarchy.TaggedWideCalendarLedgerCore
import OAI.Hierarchy.TaggedWireFeedRebase

namespace OAI
/-! # The carried hardware entry at a presented chronological feed -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open AdaptiveProbe WireTelescope LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
variable {F V : Type} [Field F] [Fintype V] {h d k K edges r : ℕ} {S : PurchaseSampler}
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
    (B : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord K)
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
    (pass : Widths K) (T : Transfer h d k)
local notation "G" => commodityGraph π place
local notation "inWidth" => input (π:=π) (place:=place) pass T
local notation "outWidth" => output B pass T
local notation "remaining" => pass+(G).chordWidths T.held+(G).chordWidths T.kept

/-- The graph and the two parties are those in the actual feed receipt. The
width equalities from that receipt only change the Lean indices of the states. -/
theorem Presents.at_carry {A C : Widths K} (op : SiteMatrix (State A) (State C) F)
    (installed : Presents B inj pad enum pass T op) (site : Fin K) (x : State A site) (y : State C site)
    (network : BitNetwork F (Fintype.card V)) (pin : V→Bool)
    (physical : ∀ (old : inWidth=A) (new : outWidth=C),
      TypedWiring.value network pin=LedgerStep.carry (B.onlySpill inj pad T.spill enum) remaining site
        (LedgerStep.repartition G pass T.old T.active T.held T.kept T.spill T.balanced site
          (cast (congrArg (fun u=>State u site) old.symm) x))
        (cast (congrArg (fun u=>State u site) new.symm) y)) :
    TypedWiring.value network pin=op site x y := by
  obtain ⟨left,right,rfl⟩:=installed
  subst A;subst C
  change TypedWiring.value network pin=FeedTransfer.matrix B inj pad enum pass T site x y
  exact LedgerStep.feed_of_carry G pass T.old T.active T.held T.kept T.spill T.balanced
    (B.onlySpill inj pad T.spill enum) site x y network pin (physical rfl rfl)

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer
end

end OAI
