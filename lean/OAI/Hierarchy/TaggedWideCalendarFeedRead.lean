import OAI.Hierarchy.TaggedWideFeedAtCarry
import OAI.Hierarchy.TaggedWireFeedTransferCongr

namespace OAI
/-! # The carried hardware entry at a presented chronological feed -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open AdaptiveProbe WireTelescope ProtocolRAM.Calendar.CoreRoute LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat
variable {F V : Type} [Field F] [Fintype V] {h d k K edges r : ℕ} {S : PurchaseSampler}
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
    (B : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord K)
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
    (pass : Widths K) (T : Transfer h d k)
local notation "G" => commodityGraph π place
local notation "inWidth" => input (π:=π) (place:=place) pass T
local notation "outWidth" => output B pass T
local notation "remaining" => pass+(G).chordWidths T.held+(G).chordWidths T.kept

/-- Pulling both numeric state words through their width casts leaves the
actual input and output tableaux available at the original path endpoint. -/
theorem Presents.checked_entry (C : Mount (S:=S) π place edges) (o : Orders h d k) (sameRow : B.row=C.row)
    {A A' : Widths K} (op : SiteMatrix (State A) (State A') F)
    (chosen : Presents B inj pad (ProtocolRAMDateSpillRank.spillEnum B o) pass T op)
    (stock : Data h d k→ℕ) (sameStock : stock=T.spill) (rest : Widths K) (sameRest : rest=remaining)
    (s : Fin K) (x : State A s) (y : State A' s)
    (xx : State (rest+(G).chordWidths stock) s) (yy : State (rest+C.actual.chordWidths (routeLoad C.ordinary stock)) s)
    (entry : HEq x xx) (exit : HEq y yy) :
    LedgerStep.carry (C.onlySpill inj pad stock (ProtocolRAMDateSpillRank.spillEnum C o)) rest s xx yy=op s x y := by
  obtain ⟨left,right,rfl⟩:=chosen
  subst A
  subst A'
  dsimp only [WireTelescope.rebase]
  apply checked_carry B C inj pad o pass T sameRow stock sameStock rest sameRest
  · unfold LedgerStep.repartition
    exact (cast_heq ..).trans entry
  · exact exit

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer
end

end OAI
