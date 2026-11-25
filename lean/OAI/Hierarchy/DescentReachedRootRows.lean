import OAI.Hierarchy.DescentObservedRootRow
import OAI.Hierarchy.DescentFallbackRootSocket

namespace OAI
/-! # Authentic measured rows of the root socket on the reached reset date -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentRelativeContacts DescentSharedBookScan
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Z.Terminals)

def observedRootAddress (t : Z.Fallback) : Fin (DescentFallbackShapeTable.rows (Z.k-T.commonDepth) (2^Z.n)) :=
  shapeCell (shortName T.commonDepth (T.code t)).2
    (Nat.sub_le_sub_right (T.codeLegal t).2.1 _) (Nat.mod_lt _ (Nat.two_pow_pos _))

end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking DescentRelativeContacts
open DescentPackedFallbackTree DescentFallbackItemSelect DescentStageEdgeReceipt
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P V : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃Fin groups×Block k) (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (grp : Fin groups↪ℕ) (vertex : V↪Fin (Fintype.card V)) (padded : Fintype.card V≤H)
local notation "native" => order.trans Fin.valEmbedding
local notation "pad" => vertex.trans (Fin.castLEEmb padded)
variable {zz ww : ℕ} {ct : W.graph.Edge→ℕ} {cut : ∀e,W.graph.width e=ct e*(zz*G.b)}
variable (Z : ResetInput (W.granular ct (zz*G.b) cut) (q*ww) ε h C Ht) (T : Z.Terminals)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site =>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (snap : RootObservation A S ready digits (order.trans Fin.valEmbedding) grp (vertex.trans (Fin.castLEEmb padded)) Z T frm field)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
variable (effective : ℕ) (extent : effective=m)
local notation "L" => 2^(effective-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation:max "cfg" sample:arg => ({sample with
  oldDegree := A.degree
  oldCap := A.cap
  donors := L
  fineBits := k
  fieldBits := field
  residual := r
  maxDepth := Ht} : DescentFallbackOperandBranch.Config)
local notation:max "tkt" t:arg => (Z.fallLabel T t,(T.code t).2.2)
local notation:max "addr" t:arg => Z.observedRootAddress T t
local notation:max "num" t:arg => (T.leaves.window (shortName c (T.code t))).card
local notation:max "whereHost" t:arg => frm.host.symm (T.code t).1
local notation:max "hiAt" t:arg => Z.rootBlock T (.inr t)
local notation "ranks" => DescentSharedBookScan.ranks (a:=r) (Y:=2^Z.n) (D:=A.degree) snap.chart (2^Ht) (Ht+2) snap.memory
local notation:max "item" s:arg t:arg => DescentRouterSlots.Item Z.placement.contact Z.placement.owner s (.inr t)
variable (zEq : zz=A.z) (wireEq : ww=A.wire) (countEq : ct=A.grainCount)
local notation "asOld" => Equiv.sigmaCongrRight (fun a=>finCongr (congrFun countEq a))
local notation:max "oldPos" s:arg e:arg => localAddress A native S ready digits frm.basis («c»:=c) s (asOld e)
local notation:max "row" s:arg e:arg => finProdFinEquiv (((oldPos s e).1.cast (congrArg (fun l=>2^(l-c)) extent.symm)),(oldPos s e).2)
local notation "chron" => DescentOrderedReset.grains W ct order
open DescentNamedContact DescentOrderedReset

include zEq wireEq in
theorem observed_root_row_cast (sample : DescentFallbackOperandBranch.Config) (side : Bool) (t : Z.Fallback)
    (x : (cfg sample).Data Z.n)
    (packet : (cfg sample).packet x=DescentFallbackPeriod.inputs (n:=Z.n) («r»:=r) (field:=field)
      (fun u hi lo=>snap.stencil u hi (lo.cast (congrArg (fun l=>2^(l-c)) extent)))
      snap.peers (fun u hi lo=>snap.marks u hi (lo.cast (congrArg (fun l=>2^(l-c)) extent))) (fun u j=>(ranks u j).val) (pad (whereHost t)) (Z.rootBlock T (.inr t)))
    (hostRead : ((cfg sample).header x 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A vertex (whereHost t)) (vertex (whereHost t)).val)
      (decide (whereHost t∉A.near (whereHost t))))
    (groupWord : ∀e : item side t,((cfg sample).digit x (row side e.val) 0).val=
      compress (groupDomain digits frm.basis fit (whereHost t) (hiAt t)) (A.pos (W.graph.src e.val.1)).1.val)
    (fineWord : ∀e : item side t,((cfg sample).digit x (row side e.val) 1).val=(A.block (W.graph.src e.val.1)).val)
    (indexed : ∀u,originalId W.graph.Site u=(A.site vertex ready.coordinates u).val)
    (sorted : SourceSorted W order)
    (anchor : item side t) (e : Fibre (Z.placement.input side) (Z.placement.input side anchor.val)) :
    let xs:=(cfg sample).rowsAt x side (tkt t) (addr t) (num t)
    ∃ j : ↥(rows Ht [] xs),
      rank xs (rows Ht [] xs) j.val=
        (DescentOrderedWords.before (fibreKey chron (Z.placement.input side) (Z.placement.input side anchor.val)) e).card ∧
      (xs j.val).residual=(oldPos side e.val).1.val ∧
      (xs j.val).signed=(oldPos side e.val).2.val :=by
  subst zz
  subst ww
  subst ct
  subst effective
  exact observed_root_row A S ready digits order grp vertex padded Z T frm snap sample side t x packet
    hostRead groupWord fineWord indexed sorted anchor e

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan
open DescentResetStemCompactOrder DescentPackedTicketChronology DescentPacking DescentStageEdgeReceipt
open DescentFallbackItemSelect DescentNamedContact
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => (Z).placement
local notation "words" => S.resetInputDigits ctl.base ctl.radix i
local notation "m" => S.groupWidth k tail i+k
local notation "c" => (T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-c
local notation "Y" => (2^(Z).n : ℕ)
local notation "native" => input.order.trans Fin.valEmbedding
local notation:max "item" s:arg t:arg => DescentRouterSlots.Item (R).contact (R).owner s (.inr t)
local notation:max "token" t:arg => ((Z).fallLabel T t,((T).code t).2.2)
local notation:max "num" t:arg => ((T).leaves.window (shortName c ((T).code t))).card
local notation:max "who" t:arg => B.frame.host.symm ((T).code t).1
local notation:max "hiAt" t:arg => (Z).rootBlock T (.inr t)
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "widthCast" => congrArg (fun l=>2^(l-c)) B.keyWidth
local notation:max "posOld" s:arg e:arg => localAddress A native S input.valid words B.frame.basis («c»:=c) s (beforeStem B e)
local notation:max "row" s:arg e:arg => finProdFinEquiv (((posOld s e).1.cast (widthCast).symm),(posOld s e).2)
variable {H field query lanes batches nodes args : ℕ}
local notation "cfg" => flatConfig B field query lanes batches batches nodes args
variable (grp : Fin (S.groupCount i)↪ℕ) (padded : Fintype.card input.V≤H)
local notation "pad" => input.vertex.trans (Fin.castLEEmb padded)
variable (snap : GroupStage.RootObservation input.placement S input.valid (S.resetInputDigits ctl.base ctl.radix i) (input.order.trans Fin.valEmbedding) grp (input.vertex.trans (Fin.castLEEmb padded)) B.reset B.terminals B.frame field)
local notation "ranks₀" => ranks (a:=r) («Y»:=Y) (D:=(A).degree) snap.chart (2^Ht) (Ht+2) snap.memory

/-- Populate the installed root-socket rows from the preceding measured packet.
Both the old grain count and the public low-coordinate width are cast back to
their reached values before reading the previous stencil and signed sheets. -/
theorem reached_root_rows (side : Bool) (t : (Z).Fallback) (x : (cfg).Data (Z).n)
    (packet : (cfg).packet x=DescentFallbackPeriod.inputs (n:=(Z).n) («r»:=r) (field:=field)
      (fun u hi lo=>snap.stencil u hi (lo.cast widthCast)) snap.peers
      (fun u hi lo=>snap.marks u hi (lo.cast widthCast)) (fun u j=>(ranks₀ u j).val)
      (pad (who t)) (hiAt t))
    (hostRead : ((cfg).header x 3).val=DescentResetStemWord.hostCode
      (compress (hostDomain A input.vertex (who t)) (input.vertex (who t)).val)
      (decide (who t∉(A).near (who t))))
    (groupWord : ∀e : item side t,((cfg).digit x (row side e.val) 0).val=
      compress (groupDomain words B.frame.basis small (who t) (hiAt t)) ((A).pos (W.graph.src e.val.1)).1.val)
    (fineWord : ∀e : item side t,((cfg).digit x (row side e.val) 1).val=((A).block (W.graph.src e.val.1)).val)
    (indexed : ∀u,originalId W.graph.Site u=((A).site input.vertex input.valid.coordinates u).val)
    (sorted : SourceSorted W input.order) (anchor : item side t) :
    RootRows (field:=field) (query:=query) (lanes:=lanes) (batches:=batches) (nodes:=nodes) (args:=args)
      B side ((R).input side anchor.val)
      ((cfg).rowsAt x side (token t) ((Z).observedRootAddress T t) (num t)) :=by
  constructor
  intro e
  have hit:=GroupStage.observed_root_row_cast A S input.valid words input.order grp input.vertex padded (Z) (T)
    B.frame snap (effective:=(Z).k) (extent:=B.keyWidth) (zEq:=input.grain.symm)
    (wireEq:=input.edges.symm) (countEq:=B.count_eq) (cfg) side t x packet hostRead
    groupWord fineWord indexed sorted anchor e
  obtain ⟨j,countAt,lo,hi⟩ := hit
  refine ⟨j,?_,lo,hi⟩
  rw [B.order_eq]
  exact countAt

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
