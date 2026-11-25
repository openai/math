import OAI.Hierarchy.TaggedWideBallotWords
import OAI.Hierarchy.ProbeSignedWantedRelease
import OAI.Hierarchy.ProbeFixedPrintedRole
import OAI.Hierarchy.ProbeFixedPacketAtom

namespace OAI
/-! # Dated ballot fields from the two actual signed strip catalogues -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart PurchaseStage WideCPU
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (h width : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "sig" => (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet
local notation "fs" => v.nativeFormats P h width

def wideBallotSite (siteROM : ℕ) : (a : Attempt)→Fin (v.wideBallotParties h a)→Expr
  | .outer .. => SiteDirectory.partyField siteROM h (2^v.W) SiteNaming.labels (v.payloadPricePorts P h width).column
  | .inner phase trial .. => SiteDirectory.partyField siteROM h (2^v.W) SiteNaming.labels
      (v.purchasedPricePorts P h width phase trial).column

def wideBallotShape : Event→WideCPU.Shape
  | .attempt a=>⟨(fs a).market.rows,v.wideBallotParties h a,sig+2⟩
  | .feed _=>⟨0,0,0⟩

/-- On a feed there are no candidate ballots. A genuine attempted strip reads its
protected selection tag and counters at their original fixed addresses. Its party
lookup uses the real archived payload or purchased geometry. -/
def wideFields (siteROM : ℕ) : (e : Event)→Fields (v.wideBallotShape P h width e)
  | .attempt a=>Ballot.fields (v.menuCodes N)
      (Ballot.code ((fs a).board.reportOut 6) (fs a).market.rows)
      (fs a).board.batch.field (v.wideBallotSite P h width siteROM a)
  | .feed _=>⟨Fin.elim0,Fin.elim0,Fin.elim0⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
