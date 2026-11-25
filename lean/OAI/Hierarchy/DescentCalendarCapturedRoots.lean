import OAI.Hierarchy.DescentCalendarCandidateCapture
import OAI.Hierarchy.DescentCalendarOriginalPeers
import OAI.Hierarchy.DescentCalendarPrivatePages

namespace OAI
/-! # Capture the original private root tables on the reached peer-prefix memory -/

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
open DescentPackedZip DescentFallbackPeriod
open scoped Fin.CommRing

/-- An unchanged array of numerical RAM words is an expression read on any
propositionally identical host, group, field and packing chart. -/
private theorem lookup_cast {H₀ H₁ G₀ G₁ a₀ a₁ m₀ m₁ w end_ : ℕ}
    (hH : H₀=H₁) (hG : G₀=G₁) (ha : a₀=a₁) (hm : m₀=m₁)
    (bank : Bank) (memory : Memory w) (cells : Fin H₁→Fin G₁→Cell a₁)
    (safe : bank.Fits w end_) (size : H₁*chunks G₁ m₁≤bank.size) (issued : Reads bank cells m₁ memory) :
    Source (.lookup bank .row) (fun (h : Fin H₀) (g : Fin G₀)=>
      (cells (h.cast hH) (g.cast hG)).cast (congrArg (fun a=>2^a) ha.symm)) m₀ memory :=by
  subst H₁; subst G₁; subst a₁; subst m₁
  exact source_column bank end_ safe memory cells size issued

/-- Cast the old private word width recorded by the real former chart. Its
numerical root pages and the timestamp of their read stay unchanged. -/
def priorAtWidth {b₁ b₂ keys} (equal : b₁=b₂) (previous : PriorPeerWords B H b₁ keys) :
    PriorPeerWords B H b₂ keys := equal ▸ previous

/-- The same cast carries the authenticated stem, actor and original-edge
incidence predicates needed by the reset's candidate evaluator. -/
theorem priorAtWidth_origins {a b keys count : ℕ} (equal : a=b)
    (previous : PriorPeerWords B H a keys) (positive : 0<(Z).unit)
    (panel : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel ht count)
    (observed : PeerOrigins B pad previous positive panel) :
    PeerOrigins B pad (priorAtWidth B equal previous) positive panel :=by
  subst b
  exact observed

private theorem prior_width_reads {w b₁ b₂ keyBits M} (equal : b₁=b₂) (previous : PriorPeerWords B H b₁ keyBits)
    (bank : Bank) (s : Bool) (t : (Z).RootTicket T) (memory : Memory w)
    (got : Reads bank (previous.privatePages s t) M memory) :
    Reads bank ((priorAtWidth B equal previous).privatePages s t) M memory :=by
  subst b₂
  exact got

def chartTicket (t : Root (Q₀).residual (Q₀).ports) : (Z).RootTicket T :=
  cast (congrArg₂ Root (congrArg DescentPrivateMaskDeck.Shape.residual cal.privateDeck)
    (congrArg DescentPrivateMaskDeck.Shape.ports cal.privateDeck)) t

/-- On each acquired host/group lane the measured word is numerically the very
earlier root word. All casts in this equation are chart- or width equalities. -/
theorem chartPages_val {field keys} (width : field=oldWidth) (previous : PriorPeerWords B H field keys)
    (s : Bool) (t : Root (Q₀).residual (Q₀).ports) (h : Fin (pitch₀).hosts) (g : Fin (pitch₀).groups) :
    (chartPages B oldBatch batch calendar I cal (priorAtWidth B width previous) s t h g).val=
      (previous.privatePages s (chartTicket B oldBatch batch calendar cal t) (h.cast cal.oldHosts)
        (g.cast cal.oldGroups)).val :=by
  subst field
  rfl

/-- Both of the private-root premises of capture_menu follow from original
root-catalogue words on exactly the reached preScalar memory. Earlier bank identities
are logical address equalities. The observed cells themselves come from the root program. -/
theorem captured_roots {field keyBits} (previous : PriorPeerWords B H field keyBits) (width : field=oldWidth)
    (catalogue : Bool→(Z).RootTicket T→Bank) (m : Memory bw)
    (shelf_ : ∀s t,I.earlier.pages s t=catalogue s (chartTicket B oldBatch batch calendar cal t))
    (physical : ∀s t,(catalogue s t).Fits bw ((phys₀).peers ((v₀).actorEnd base₀)) ∧
      H*chunks J oldBatch≤(catalogue s t).size)
    (issued : ∀s t,Reads (catalogue s t) (previous.privatePages s t) oldBatch
      ((phys₀).preScalar ((v₀).actorEnd base₀) ((v₀).issuedScene base₀ I.earlier) I.sceneFits m)) :
    (∀s t,(I.earlier.pages s t).Fits bw ((phys₀).peers ((v₀).actorEnd base₀))) ∧
    ∀s t,Source (.lookup (I.earlier.pages s t) .row)
      (chartPages B oldBatch batch calendar I cal (priorAtWidth B width previous) s t)
      (Q₀).oldBatch ((phys₀).preScalar ((v₀).actorEnd base₀) ((v₀).issuedScene base₀ I.earlier) I.sceneFits m) :=by
  constructor
  · intro s t
    rw [shelf_ s t]
    exact (physical _ _).1
  · intro s t
    let t':=(chartTicket B oldBatch batch calendar cal t)
    have field_ : (Q₀).panels=oldWidth*(cap₀*5) :=congrArg DescentPrivateMaskDeck.Shape.panels cal.privateDeck
    have pitch : (Q₀).oldBatch=oldBatch :=congrArg DescentPrivateMaskDeck.Shape.oldBatch cal.privateDeck
    rw [shelf_ s t]
    exact lookup_cast cal.oldHosts cal.oldGroups field_ pitch (catalogue s t') _
      ((priorAtWidth B width previous).privatePages s t') (physical s t').1 (physical s t').2
      (prior_width_reads B width previous _ s t' _ (issued s t'))


open DescentFallbackPeriod.Projected DescentResetGates

local notation "stop₀" => (phys₀).peers ((v₀).actorEnd base₀)
local notation "snapshot" m => (phys₀).preScalar ((v₀).actorEnd base₀) ((v₀).issuedScene base₀ I.earlier) I.sceneFits m

/-- The two physical bounds come from the exact initialized private catalogue.
The per-page reads here are the second conclusion of calendar_original_peers. -/
theorem capture_catalogue {N keys K₁ R hm l tiny rootWidth senderBits metadata : ℕ}
    (rc : Receiver (A).degree (A).cap N (Z).n r (T).commonDepth H (S.groupCount i) K₁ R oldBatch hm l tiny rootWidth ht bw)
    (book : RootBook (Z).n r (A).degree (2^r) (A).cap rootWidth)
    (previous : PriorPeerWords B H
      (CandidateFront.setupFront S ctl.board k tail i D f g oldBatch batch senderBits metadata C ctl.bitsR calendar).privateBits keys)
    (m : Memory bw) (end_ : rc.preparedEnd book≤ stop₀) (space : stop₀<2^bw)
    (alias_ : ∀s t,I.earlier.pages s t=rc.privatePageBank book s (chartTicket B oldBatch batch calendar cal t))
    (issued : ∀s t,Reads (rc.privatePageBank book s t) (previous.privatePages s t) oldBatch (snapshot m)) :
    let width:=calendar_private_width B oldBatch batch senderBits metadata calendar paid
    (∀s t,(I.earlier.pages s t).Fits bw stop₀) ∧
      ∀s t,Source (.lookup (I.earlier.pages s t) .row)
        (chartPages B oldBatch batch calendar I cal (priorAtWidth B width previous) s t) (Q₀).oldBatch (snapshot m) :=by
  intro width
  exact captured_roots B oldBatch batch calendar I cal previous width (rc.privatePageBank book) m alias_
    (fun s t=>rc.privatePage_room book s t _ end_ space) issued

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
