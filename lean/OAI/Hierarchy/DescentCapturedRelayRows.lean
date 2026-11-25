import OAI.Hierarchy.DescentRelaySocketObserved

namespace OAI
/-! # Public signed, identity and coordinate reads at the original relay site -/
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
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "height" => GroupStage.depthBound D n f g

local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "widths_" => funext (fun e=>((Z).allWidths e).symm)

local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding

local notation "rr" => (Z).k-c
local notation "Y" => (2^(Z).n : ℕ)

variable {field query lanes batches split nodes args grain : ℕ}
local notation "cfg" => flatConfig B field query lanes batches split nodes args
open DescentPackedRotorMatrix DescentResetPublicOperandBook DescentRotorOperandQueryROM.Shape

local notation "pubCfg" => publicOperandConfig B field query lanes batches split nodes args grain

open DescentOperandStateBanks DescentResetOperandComponents DescentOperandCandidateLookup
open DescentDatedAddressBook.ResetOutput

local notation "End₀" => (old).graph.Edge
local notation:max "land" e:arg => (T).home ((old).graph.dst e)
local notation:max "trunk" e:arg => trunkParent B (land e)
local notation:max "site" e:arg => (blocks B).dst (trunk e)
local notation:max "inputStem" e:arg => stemParent B (true,e)

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

variable {H newH M : ℕ} (oldFits:Fintype.card input.V≤H) (grp:Fin (S.groupCount i)↪ℕ)
local notation "vertex_" => input.vertex.trans (Fin.castLEEmb oldFits)
variable (snap : GroupStage.RootObservation input.placement S input.valid (S.resetInputDigits ctl.base ctl.radix i)
  (input.order.trans Fin.valEmbedding) grp (input.vertex.trans (Fin.castLEEmb oldFits)) B.reset B.terminals B.frame field)
local notation "ranks_" => DescentSharedBookScan.ranks (a:=rr) («Y»:=2^(Z).n) (D:=(A).degree)
  snap.chart (2^height) (height+2) snap.memory
local notation:max "oldRow" row:arg => relayPhysicalRow B row
local notation:max "lo_" a:arg => (finProdFinEquiv.symm (incomingIndex B a)).1



/-- Original signed donor fields, the saved old self and both preceding coordinate digits. -/
structure RelayRows (newFits:Fintype.card B.next.V≤newH) (e:End₀) (row:(pubCfg).Data (Z).n) : Prop where
  packet : (adjusted).packet (oldRow row)=DescentFallbackPeriod.inputs (field:=field) snap.stencil snap.peers snap.marks
      (fun u j=>(ranks_ u j).val) (vertex_ (B.frame.host.symm ((T).code (land e)).1))
        ((Z).rootBlock T (.inr (land e)))
  self : ((adjusted).header (oldRow row) 3).val=stemSelfDigit B (originalTrunkRack B)
      (((denseOrder B) (site e).1.2).castLE newFits)
  coordsRead : ∀a:End₀,land a=land e → ∀f:Fin 2,
      ((adjusted).digit (oldRow row) (incomingIndex B a) (f.castLE (by decide))).val=
        (coords B newH M field).value B.frame.basis (f.castLE (by decide)) (site e).2 (lo_ a) (site e).1.1

theorem RelayRows.reply (newFits:Fintype.card B.next.V≤newH) (age:0< i) (sorted:SourceSorted W input.order)
    (e:End₀) (arg:Fin (2*split)) (row:(pubCfg).Data (Z).n)
    (seen : RelayRows (M:=M) B oldFits grp snap newFits e row)
    (shape:↥(DescentDenseHostOrder.roster (Z).graph rr height)) (live:((cfg).header ((pubCfg).basic row) 0).val≠0)
    (atShape:((cfg).header ((pubCfg).basic row) 2).val=(localRank (Z).graph rr height shape).val)
    (kind:shape.val=.trunk true ((),(shortName (T).commonDepth ((T).code (land e))).2))
    (capAt:((cfg).header ((pubCfg).basic row) 1).val=input.placement.cap) (same:batches=split) :
    let side:=arg.val<split
    let edge:=if side then trunk e else inputStem e
    let word:=if side then earlierIncoming B e*split+arg.val else arg.val-split
    let mark:=if side then ((T).code (land e)).2.2.isSome else false
    ∃number,∃socket:PublicSocket B (site e) split word mark number,socket.face.val.1=edge ∧
      socket.face.val.2=decide side ∧
      (pubCfg).mixed (Z).graph (earlierIncoming B e) arg.val row=some (number,word,1,mark):=
  relay_socket_observed B oldFits grp snap newFits age sorted e arg row shape live atShape kind capAt same
    seen.packet seen.self seen.coordsRead

/-- The registered row on the numeric group order of the entering stage. -/
def OriginalRelayRows (e:End₀) (row:(pubCfg).Data (Z).n) : Prop :=
  ∃ obs : GroupStage.RootObservation A S input.valid digitsIn before
      (Fin.valEmbedding (n:=S.groupCount i)) (input.vertex.trans (Fin.castLEEmb input.valid.host))
      Z T B.frame field,
    RelayRows (M:=M) B input.valid.host (Fin.valEmbedding (n:=S.groupCount i)) obs B.next.valid.host e row

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
