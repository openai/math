import OAI.Hierarchy.DescentReachedRelayDigits
import OAI.Hierarchy.DescentCalendarRelaySockets

namespace OAI
/-! The original measured signed row and coordinates determine the fallback relay socket. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open DescentFallbackOperandQuery DescentNextSignedWindow DescentResetWireTags DescentTreePrefixIntervals
open DescentRouterSlots DescentContactTree
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)



local notation "A₁" => B.next.placement
local notation "ord₁" => B.next.order.trans Fin.valEmbedding
local notation "rr" => (Z).k-c
local notation "Y" => (2^(Z).n : ℕ)
local notation:max "Face" u:arg => Roster.Face A₁ ord₁ (blocks B) u



variable {field query lanes batches split nodes args grain : ℕ}
local notation "cfg" => flatConfig B field query lanes batches split nodes args
open DescentPackedRotorMatrix DescentResetPublicOperandBook DescentRotorOperandQueryROM.Shape
local notation:max "cell" s:arg g:arg => DescentChosenRouter.Cells (placement) s g
local notation:max "atEnd" e:arg s:arg => (if s then (blocks B).dst e else (blocks B).src e)
local notation "landing" => localAddress A before S input.valid digitsIn B.frame.basis

local notation "pubCfg" => publicOperandConfig B field query lanes batches split nodes args grain


open DescentOperandStateBanks DescentResetOperandComponents DescentOperandCandidateLookup
open DescentDatedAddressBook.ResetOutput


local notation "End₀" => (old).graph.Edge
local notation:max "land" e:arg => (T).home ((old).graph.dst e)
local notation:max "trunk" e:arg => trunkParent B (land e)
local notation:max "site" e:arg => (blocks B).dst (trunk e)
local notation:max "inputStem" e:arg => stemParent B (true,e)
local notation "total_" => total (cfg).toShape (A).cap


open DescentMeasuredOperandKey DescentRelativeContacts DescentSharedBookScan DescentFallbackItemSelect
open DescentDenseHostOrder DescentPacking
local notation "adjusted" => ({(cfg) with
  oldDegree := (A).degree
  oldCap := (A).cap
  donors := 2^(m-(T).commonDepth)
  fineBits := k
  fieldBits := field
  residual := (Z).k-(T).commonDepth
  maxDepth := height} : DescentFallbackOperandBranch.Config)

/-- The chronological width of the old donor block is the numerical width of the original public socket. -/
theorem relay_socket_config : adjusted=cfg:=by rw [←B.keyWidth];rfl

def relayPhysicalRow (row:(pubCfg).Data (Z).n) : (adjusted).Data (Z).n:=
  (relay_socket_config (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
    (split:=split) (nodes:=nodes) (args:=args) B).symm ▸ (pubCfg).basic row

private theorem relay_choice_cast {a b:DescentFallbackOperandBranch.Config} (eqConfig:a=b) {nn:ℕ}
    (row:b.Data nn) (at_:DescentContacts.Endpoint (2^nn)) (offset:ℕ):
    (select (a.relayItems (eqConfig.symm ▸ row)) (a.relayRows (eqConfig.symm ▸ row) at_) offset).map Fin.val=
      (select (b.relayItems row) (b.relayRows row at_) offset).map Fin.val:=by cases eqConfig;rfl

variable {H newH M : ℕ} (oldFits:Fintype.card input.V≤H) (grp:Fin (S.groupCount i)↪ℕ)
local notation "vertex_" => input.vertex.trans (Fin.castLEEmb oldFits)
variable (snap : GroupStage.RootObservation input.placement S input.valid (S.resetInputDigits ctl.base ctl.radix i)
  (input.order.trans Fin.valEmbedding) grp (input.vertex.trans (Fin.castLEEmb oldFits)) B.reset B.terminals B.frame field)
local notation "ranks_" => DescentSharedBookScan.ranks (a:=rr) («Y»:=2^(Z).n) (D:=(A).degree)
  snap.chart (2^height) (height+2) snap.memory
local notation:max "oldRow" row:arg => relayPhysicalRow B row
local notation:max "lo_" a:arg => (finProdFinEquiv.symm (incomingIndex B a)).1

theorem relay_socket_observed (newFits:Fintype.card B.next.V≤newH) (age:0< i)
    (sorted:SourceSorted W input.order) (e:End₀) (arg:Fin (2*split)) (row:(pubCfg).Data (Z).n)
    (shape:↥(DescentDenseHostOrder.roster (Z).graph rr height))
    (live:((cfg).header ((pubCfg).basic row) 0).val≠0)
    (shapeAt:((cfg).header ((pubCfg).basic row) 2).val=(localRank (Z).graph rr height shape).val)
    (kind:shape.val=.trunk true ((),(shortName (T).commonDepth ((T).code (land e))).2))
    (capAt:((cfg).header ((pubCfg).basic row) 1).val=(A).cap) (sameBatch:batches=split)
    (packet:(adjusted).packet (oldRow row)=DescentFallbackPeriod.inputs (field:=field) snap.stencil snap.peers snap.marks
      (fun u j=>(ranks_ u j).val) (vertex_ (B.frame.host.symm ((T).code (land e)).1))
        ((Z).rootBlock T (.inr (land e))))
    (self:((adjusted).header (oldRow row) 3).val=stemSelfDigit B (originalTrunkRack B)
      (((denseOrder B) (site e).1.2).castLE newFits))
    (coordsRead:∀a:End₀,land a=land e → ∀f:Fin 2,
      ((adjusted).digit (oldRow row) (incomingIndex B a) (f.castLE (by decide))).val=
        (coords B newH M field).value B.frame.basis (f.castLE (by decide)) (site e).2 (lo_ a) (site e).1.1):
    let side:=arg.val<split
    let edge:=if side then trunk e else inputStem e
    let word:=if side then earlierIncoming B e*split+arg.val else arg.val-split
    let mark:=if side then ((T).code (land e)).2.2.isSome else false
    ∃number,∃socket:PublicSocket B (site e) split word mark number,socket.face.val.1=edge ∧
      socket.face.val.2=decide side ∧
      (pubCfg).mixed (Z).graph (earlierIncoming B e) arg.val row=some (number,word,1,mark):=by
  have found:=relay_collects (B:=B) (padded:=oldFits) (grp:=grp) (snap:=snap) (sample:=cfg)
    (field:=field) (x:=oldRow row) (t:=land e) age sorted packet
    (self.trans (relay_self_digit B (land e) newFits))
    (fun a=>(coordsRead a.val a.property 0).trans (relay_donor_digits B (land e) newH M field a.val a.property).1)
    (fun a=>(coordsRead a.val a.property 1).trans (relay_donor_digits B (land e) newH M field a.val a.property).2) e rfl
  let target:=(shortName (T).commonDepth ((T).code (land e))).2
  have pair:=(relay_choice_cast (relay_socket_config B) ((pubCfg).basic row) target (earlierIncoming B e)).symm.trans
    (congrArg (Option.map Fin.val) found)
  cases chosen:select ((cfg).relayItems ((pubCfg).basic row)) ((cfg).relayRows ((pubCfg).basic row) target)
      (earlierIncoming B e) with
  | none => rw [chosen] at pair;contradiction
  | some j =>
    rw [chosen] at pair
    exact reached_relay_request B e arg row shape live shapeAt kind capAt sameBatch j (Option.some.inj pair) chosen

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
