import OAI.Hierarchy.DescentReachedNodeCells
import OAI.Hierarchy.DescentLocalNodeOwners
import OAI.Hierarchy.DescentResetPrimitiveWords

namespace OAI
/-! # Every chosen raw reset role keeps its actual compact local ordinal -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

theorem follow_rank (n : Normalize W) (B : BitDescription W) (order : Local B) (ok : unmixed n)
    (x : NodeOrder.All (B.follow n)) :
    (follow n B order ok x.1 x.2).val=(order ((NodeOrder.followNames n B x).1) ((NodeOrder.followNames n B x).2)).val:=by
  induction n with
  | done=>rfl
  | merge => exact False.elim ok
  | split W q m fit rest ih=>exact ih (B.pieces m q fit) order ok x
  | named W s e rest ih=>exact ih (B.renamed s e) (fun v=>order (s.symm v)) ok x
end
end Hierarchy.DescentLocalArchiveOrder

namespace Hierarchy.DescentResetLocalNodes
open DescentKernelHistory DescentNamedContact DescentResetTrunks DescentRouterBank DescentSixParty Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P H Q Y : Type} [Field F] [Fintype H] [Fintype Q] {n d L : ℕ} {bits : P→ℕ}
  {W : MarkedWorld F n P bits} (B : BitDescription W)
variable (home : W.graph.Site→H) (group : Bool→W.graph.Edge→Q) (flag : H→Bool)
  {w : W.graph.Edge→ℕ} (same : w=W.graph.width) (R : Network d (Bool×Q) (publicWidth group w))
  (legacy sorted : R.Tables F) (key : W.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F)
  (prog : SiteBits (U:=Y) R) (valid : ReadsBits R scalar prog sorted)
variable (who : ∀h,Fibre home h↪ℕ) (prior : ∀v,(B.recipe v).Node↪ℕ)
    (fresh : ∀v,(prog v).Node≃Fin (Fintype.card (prog v).Node))
local notation "pre" => B.installed home group flag same R legacy sorted key scalar prog valid
local notation "order" => installedOrder B home group flag same R legacy sorted key scalar prog valid who prior fresh
local notation "names" => NodeOrder.installedNames B home group flag same R legacy sorted key scalar prog valid

def incomingRank (v : NodeOrder.All B) : ℕ :=
  (oldOrder (fun i : Fibre home (home v.1)=>(B.recipe i.val).Node) (who (home v.1)) (fun i=>prior i.val) ⟨⟨v.1,rfl⟩,v.2⟩).val

def relayRank (e : W.graph.Edge) : ℕ :=(ordinal (relayKey W.graph home key (moved W.graph home e)) ⟨e,rfl⟩).val

omit [Fintype Q] in
theorem installed_rank (x : NodeOrder.All pre) :
    (order x.1 x.2).val=Sum.elim (incomingRank B home who prior)
      (Sum.elim (relayRank (W:=W) home key) (fun a : NodeOrder.Global prog=>(fresh a.1 a.2).val)) (names x):=by
  subst w
  obtain ⟨j,rfl⟩:=(NodeOrder.installedNames B home group flag rfl R legacy sorted key scalar prog valid).symm.surjective x
  rw [Equiv.apply_symm_apply]
  rcases j with ⟨u,a⟩|e|⟨v,a⟩ <;>rfl


omit [Fintype Q] in
theorem installed_site (x : NodeOrder.All pre) :
    DescentResetTrunks.installedNames W home group flag same R legacy x.1=
      Sum.elim (fun j : NodeOrder.All B=>Sum.inl (false,home j.1))
        (Sum.elim (fun e=>Sum.inl (true,moved W.graph home e)) (fun a : NodeOrder.Global prog=>Sum.inr a.1)) (names x):=by
  subst w
  obtain ⟨j,rfl⟩:=(NodeOrder.installedNames B home group flag rfl R legacy sorted key scalar prog valid).symm.surjective x
  rw [Equiv.apply_symm_apply]
  rcases j with ⟨u,a⟩|e|⟨v,a⟩ <;>rfl

end
end Hierarchy.DescentResetLocalNodes

namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) (earlier : Local a.bit)
local notation "split" => BitDescription.granular W b.count (z*G.b) b.fit a.bit
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "m" => b.reset.unit/p
local notation "pre" => (split).batchedReset b.reset b.terminals key m p hp fit (resetMenu b)
local notation "prog" => b.reset.laneRecipe key m p hp fit
local notation "next" => (resetArchive b p hp whole a).bit
local notation "names" => resetOrigin b hp whole a
local notation "oldId" => cap.placement.site cap.vertex cap.valid.coordinates
local notation "who" => (fun t=>(b.reset.homeTicket b.terminals oldId t).trans Fin.valEmbedding)
local notation "prior" => (fun v=>(earlier v).toEmbedding.trans Fin.valEmbedding)
local notation "fresh" => b.reset.laneNodeOrder key m p hp fit
local notation "order" => DescentLocalArchiveOrder.reset b p hp whole a earlier

theorem reached_node_rank (x : NodeOrder.All next) :
    (order x.1 x.2).val=Sum.elim (incomingRank split b.terminals.home who prior)
      (Sum.elim (relayRank (W:=W.granular b.count (z*G.b) b.fit) b.terminals.home key)
        (fun j : NodeOrder.Global prog=>(fresh j.1 j.2).val)) (names x):=by
  let preOrder:=b.reset.physicalLocalOrder split b.terminals key m p hp fit (resetMenu b) oldId prior
  have fixed:=DescentLocalArchiveOrder.follow_rank b.reblock pre preOrder (show unmixed b.reblock from by trivial) x
  let y:=NodeOrder.followNames b.reblock pre x
  have stamped:=installed_rank split b.terminals.home b.reset.placement.input b.terminals.hub
    (funext fun e=>(b.reset.allWidths e).symm) b.reset.bank b.reset.tables (b.reset.orderedBank key)
    key _ prog (b.reset.lane_valid key m p hp fit (resetMenu b)) who prior fresh y
  exact fixed.trans stamped

local notation "rawHome" => b.reset.resetNames b.terminals

def chosenOwner (j : NodeOrder.All a.bit ⊕ ((W.granular b.count (z*G.b) b.fit).graph.Edge ⊕ NodeOrder.Global prog)) :=
  (rawHome).symm (Sum.elim (fun u : NodeOrder.All a.bit=>Sum.inl (false,b.terminals.home u.1))
    (Sum.elim (fun e=>Sum.inl (true,DescentResetTrunks.moved (W.granular b.count (z*G.b) b.fit).graph b.terminals.home e))
      (fun r : NodeOrder.Global prog=>Sum.inr r.1)) j)

/-- Site before normalization, with its original host or the true installed bank actor. -/
theorem reached_node_site (x : NodeOrder.All next) :
    b.reblock.destination (chosenOwner b hp whole a (names x))=x.1:=by
  let y:=NodeOrder.followNames b.reblock pre x
  have stamped:=installed_site split b.terminals.home b.reset.placement.input b.terminals.hub
    (funext fun e=>(b.reset.allWidths e).symm) b.reset.bank b.reset.tables (b.reset.orderedBank key)
    key _ prog (b.reset.lane_valid key m p hp fit (resetMenu b)) y
  have raw:chosenOwner b hp whole a (names x)=y.1:=(rawHome).symm_apply_eq.mpr stamped.symm
  rw [raw]
  exact NodeOrder.followNames_site b.reblock pre x

end
end Hierarchy.DescentPrimitivePalette

end OAI
