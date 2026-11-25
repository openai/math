import OAI.Hierarchy.DescentResetOriginRank
import OAI.Hierarchy.DescentPaidResetRecorded
import OAI.Hierarchy.DescentRecordedResetTokens

namespace OAI
set_option quotPrecheck false

/-! # Funded reset nodes at actual compacted actor coordinates -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

theorem nodeCard_follow (n : Normalize W) (B : BitDescription W) (ok : unmixed n) (u : W.graph.Site) :
    Fintype.card ((B.follow n).recipe (n.destination u)).Node=Fintype.card (B.recipe u).Node:=by
  induction n with
  | done=>rfl
  | merge W V key hub k g rest ih=>exact False.elim ok
  | split W q m fit rest ih=>exact ih (B.pieces m q fit) ok u
  | named W s e rest ih=>
    have h:=ih (B.renamed s e) ok (s u)
    apply h.trans
    change Fintype.card (B.recipe (s.symm (s u))).Node = _
    rw [s.symm_apply_apply]

theorem unmixed_destination_injective (n : Normalize W) (ok : unmixed n) : Function.Injective n.destination:=by
  induction n with
  | done=>exact Function.injective_id
  | merge W V key hub k g rest ih=>exact False.elim ok
  | split W q m fit rest ih=>exact ih ok
  | named W s e rest ih=>exact (ih ok).comp s.injective

theorem unmixed_attach (n : Normalize W) (ok : unmixed n) (pin : P) :
    n.result.graph.attach pin=n.destination (W.graph.attach pin):=by
  induction n with
  | done=>rfl
  | merge W V key hub k g rest ih=>exact False.elim ok
  | split W q m fit rest ih=>exact ih ok
  | named W s e rest ih=>exact ih ok

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

open scoped BigOperators
local notation "pre" => B.installed home group flag same R legacy sorted key scalar prog valid
local notation "loc" => DescentResetTrunks.installedNames W home group flag same R legacy

omit [Fintype Q] in
theorem installed_cards (u : (Bool×H)⊕R.Site) :
    Fintype.card ((pre).recipe ((loc).symm u)).Node=
      (match u with
      | .inl (false,t)=>∑v : Fibre home t,Fintype.card (B.recipe v.val).Node
      | .inl (true,t)=>Fintype.card (Fibre (DescentResetTrunks.moved W.graph home) t)
      | .inr site=>Fintype.card (prog site).Node):=by
  subst w
  rcases u with ⟨_|_,t⟩|site
  · exact (Fintype.card_congr (donorNodes W.graph home group R key B.recipe prog t)).trans
      Fintype.card_sigma
  · rfl
  · rfl
end
end Hierarchy.DescentResetLocalNodes

namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
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
local notation "fresh" => b.reset.laneNodeOrder key m p hp fit
local notation "order" => DescentLocalArchiveOrder.reset b p hp whole a earlier


open scoped BigOperators Classical
open DescentPaidResidentCount.Reset
local notation "rawHome" => b.reset.resetNames b.terminals
local notation "raw" => W.granular b.count (z*G.b) b.fit
local notation "whoAt" a => b.reblock.destination ((rawHome).symm a)

theorem reached_card (u : (Bool×b.reset.Fallback)⊕b.reset.bank.Site) :
    Fintype.card ((next).recipe (whoAt u)).Node=
      (match u with
      | .inl (false,t)=>∑v : Fibre b.terminals.home t,Fintype.card (a.bit.recipe v.val).Node
      | .inl (true,t)=>Fintype.card (Fibre (DescentResetTrunks.moved (raw).graph b.terminals.home) t)
      | .inr site=>Fintype.card (prog site).Node):=by
  rw [show Fintype.card ((next).recipe (whoAt u)).Node=Fintype.card ((pre).recipe ((rawHome).symm u)).Node from
    DescentLocalArchiveOrder.nodeCard_follow b.reblock pre (by trivial) _]
  have counts := DescentResetLocalNodes.installed_cards split b.terminals.home b.reset.placement.input b.terminals.hub
    (funext fun e=>(b.reset.allWidths e).symm) b.reset.bank b.reset.tables (b.reset.orderedBank key)
    key _ prog (b.reset.lane_valid key m p hp fit (resetMenu b)) u
  rcases u with ⟨_|_, t⟩ | site <;> exact counts

theorem payee_bank_card (stored : b.Recorded p) (site : b.reset.bank.Site) :
    payee b stored (.inr site)=Fintype.card ((next).recipe (whoAt (.inr site))).Node:=by
  exact (reached_card b hp whole a (.inr site)).symm

theorem payee_relay_card (stored : b.Recorded p) (t : b.reset.Fallback) :
    payee b stored (.inl (true,t))=Fintype.card ((next).recipe (whoAt (.inl (true,t)))).Node:=by
  rw [reached_card]
  change _=Fintype.card {e : Σe : W.graph.Edge,Fin (b.count e) // b.terminals.home (W.graph.dst e.1)=t}
  exact ((grain_total b.count (fun e : W.graph.Edge => b.terminals.home (W.graph.dst e)) t).trans
    (Finset.sum_congr rfl (fun e _ => congrFun b.count_eq e.val))).symm

theorem payee_le_card [Fintype P] (stored : b.Recorded p) (prior : a.bit.Tokenized cap.placement.records) (u : (Bool×b.reset.Fallback)⊕b.reset.bank.Site) :
    payee b stored u≤Fintype.card ((next).recipe (whoAt u)).Node:=by
  rcases u with ⟨_|_,t⟩|site
  · rw [reached_card]
    apply Finset.sum_le_sum
    intro i _
    rw [prior i.val]
    omega
  · exact (payee_relay_card b hp whole a stored t).le
  · exact (payee_bank_card b hp whole a stored site).le


theorem recipient_records_le [Fintype P] (stored : b.Recorded p) (prior : a.bit.Tokenized cap.placement.records)
    (v : b.reblock.result.graph.Site) : (b.next.placement.records v).length≤Fintype.card ((next).recipe v).Node:=by
  rw [resetArchive_tokenized b stored a prior v]
  omega

theorem born_recipient_records [Fintype P] (stored : b.Recorded p) (prior : a.bit.Tokenized cap.placement.records)
    (u : (Bool×b.reset.Fallback)⊕b.reset.bank.Site) (born : ∀t,u≠.inl (false,t)) :
    (b.next.placement.records (whoAt u)).length=Fintype.card ((next).recipe (whoAt u)).Node:=by
  rw [resetArchive_tokenized b stored a prior (whoAt u)]
  suffices b.reblock.result.exteriorTokens (whoAt u)=0 by rw [this]; rfl
  unfold MarkedWorld.exteriorTokens DescentResetTrunks.bin
  apply Finset.sum_eq_zero
  intro pin _
  apply ite_eq_right
  intro storedAt
  rw [unmixed_attach b.reblock (by trivial)] at storedAt
  have original:=unmixed_destination_injective b.reblock (by trivial) storedAt
  have loc:=congrArg (fun s=>rawHome s) original
  rw [Equiv.apply_symm_apply] at loc
  exact born _ ((loc).symm.trans (b.reset.read_source_pin b.terminals pin))

end
end Hierarchy.DescentPrimitivePalette

end OAI
