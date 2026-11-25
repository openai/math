import OAI.Hierarchy.TaggedWireMatchingEntry
import OAI.Hierarchy.TaggedWirePartyTrace
import OAI.Hierarchy.TaggedWireReportAction
import OAI.Hierarchy.TaggedWireNativePassMatrix
import OAI.Hierarchy.TaggedWirePlacedBroadcast

namespace OAI
/-! # Each open tagged term as a product of its literal chronological site factors -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope TaggedPrune Tagged ProtocolRAMEmit
open ProtocolRAM.Calendar WireTelescope.CalendarTape
open scoped Classical BigOperators

variable {h d k w R M den : ℕ} {F : Type*} [Field F]

def publicChord (h d k : ℕ) : Chord (siteLast h d k+1) :=
  orderedChord (siteNumber h d k (.inl 0,none)) (siteNumber h d k (.inr (.inr 0),none)) (by simp)

structure Report (p : Equiv.Perm (Tagged.Row h)) (d k w R M den : ℕ) (U : Widths (siteLast h d k+1)) where
  sampler : PurchaseSampler
  edges : ℕ
  occurrences : ℕ
  mount : Mount (S:=sampler) p.symm (siteNumber h d k) edges
  rows : Fin edges→ProtocolRAMEmit.Row
  geometry : Geometry (boardLayout h d k w R) M den rows
  fixed : Fin edges→ℕ
  stock : Commodity (Fin (2^h)) (Stages h d) k→ℕ
  reserved : Columns h d × Fin k→ℕ
  used : Columns h d × Fin k→ℕ
  ledger : mount.actual.chordWidths fixed+(commodityGraph p.symm (siteNumber h d k)).chordWidths stock+
    (catalystGraph (siteNumber h d k)).chordWidths (fun c=>reserved c-used c)=U
  receipt : MatrixReceipt mount fixed stock reserved used geometry
  enum : Fin occurrences≃RouteOccurrence mount.ordinary mount.centers

namespace Report
variable {p : Equiv.Perm (Tagged.Row h)} {U : Widths (siteLast h d k+1)} (Z : Report p d k w R M den U)

def output := installedWidths Z.geometry.links.ends Z.geometry.links.bits
def edgesAt := filledChord Z.mount.actual (publicChord h d k)
def widthAt (e : Fin Z.edges) := (Z.rows e).width

def finish : SiteMatrix (State U) (State Z.output) F :=
  rebase Z.ledger rfl (Z.receipt.matrix (siteNumber h d k).injective (publicChord h d k) Z.enum)

theorem finish_action (x : ∀i,State U i) : (raw F U).coeff x=SiteMatrix.act Z.finish (raw F Z.output).coeff x :=
  rebase_action Z.ledger rfl _ (Z.receipt.action (siteNumber h d k).injective (publicChord h d k) Z.enum) x

def ports (data : ∀e,Fin (2^Z.widthAt e)) (s : Fin (siteLast h d k+1)) : State Z.output s :=
  cast (congrArg (fun V=>State V s) (Z.receipt.reported_width (publicChord h d k))) (readEdges Z.edgesAt Z.widthAt data s)

end Report

namespace PhysicalTerm
variable {X : Type} (p : Equiv.Perm (Tagged.Row h)) (slots : Event→Slot X) (es : List Event)
    (wire : X→Widths (siteLast h d k+1)) (x₀ : X) (initial : exposedWidth p d k w R=wire x₀)
    (next : ∀e x (c : (slots e).choice x),SiteMatrix (State (wire x)) (State (wire ((slots e).next x c))) F)
    (sum : ∀e x v,(raw F (wire x)).coeff v=∑c,SiteMatrix.act (next e x c) (raw F (wire ((slots e).next x c))).coeff v)
    (report : ∀j : Path slots es x₀,Report p d k w R M den (wire (terminal slots es x₀ j)))

abbrev Exposed := (CorrectionProducts.raw (routingMatch (F:=F) p)).group (exposedSite h d k w R)

def entry : SiteMatrix (Exposed (F:=F) (d:=d) (k:=k) (w:=w) (R:=R) p).Leg (State (wire x₀)) F :=
  MatchingEntry.rewidth initial (exposedMatrix p d k w R)

theorem start (v : ∀s,(Exposed (F:=F) (d:=d) (k:=k) (w:=w) (R:=R) p).Leg s) :
    (Exposed (F:=F) (d:=d) (k:=k) (w:=w) (R:=R) p).coeff v=SiteMatrix.act (entry p wire x₀ initial) (raw F (wire x₀)).coeff v := by
  rw [entry,MatchingEntry.rewidth_action]
  exact exposed_action p v

def family : Expansion (Exposed (F:=F) (d:=d) (k:=k) (w:=w) (R:=R) p) (Path slots es x₀) (fun j=>(report j).output) :=
  matrixExpansionFrom slots wire next sum es x₀ _ (entry p wire x₀ initial) (start p wire x₀ initial)
    (fun j=>(report j).finish) (fun j=>(report j).finish_action)

def kernel (j : Path slots es x₀) := SiteMatrix.compose (entry p wire x₀ initial)
  (SiteMatrix.compose (matrix slots wire next es x₀ j) (report j).finish)

/-- One original word per emitted terminal row, and the true input
matching, signed replacement, and wire-copy factors at each physical site. -/
theorem term_words (j : Path slots es x₀)
    (v : ∀s,(Exposed (F:=F) (d:=d) (k:=k) (w:=w) (R:=R) p).Leg s) :
    (family p slots es wire x₀ initial next sum report).part j v =
      ∑a : ∀e,Fin (2^(report j).widthAt e),∏s,kernel p slots es wire x₀ initial next report j s
        (v s) ((report j).ports a s) :=
  reported_words (report j).edgesAt (report j).widthAt ((report j).receipt.reported_width (publicChord h d k))
    (kernel p slots es wire x₀ initial next report j) v

/-- At a single physical site each branch uses the explicit intermediate tape.
The first matrix compares the exposed matching bits, every intermediate term
is the actual local packet or equality, and the last reads the reported slots. -/
theorem site_terms (j : Path slots es x₀) (s : Fin (siteLast h d k+1))
    (v : (Exposed (F:=F) (d:=d) (k:=k) (w:=w) (R:=R) p).Leg s) (a : ∀e,Fin (2^(report j).widthAt e)) :
    kernel p slots es wire x₀ initial next report j s v ((report j).ports a s)=
    ∑z : State (wire x₀) s × PartyStates slots wire s es x₀ j,
      partyWeight slots wire next s es x₀ j (fun y=>(report j).finish s y ((report j).ports a s)) z.1 z.2 *
        entry p wire x₀ initial s v z.1 :=
  party_kernel slots wire next (entry p wire x₀ initial) s es j (report j).finish v ((report j).ports a s)

end PhysicalTerm
end Hierarchy.ProbeStage.CoreBoard

end
end OAI
