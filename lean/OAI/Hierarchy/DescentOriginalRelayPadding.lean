import OAI.Hierarchy.DescentReachedRelayPadding
import OAI.Hierarchy.DescentSlotAbsentRange
import OAI.Hierarchy.DescentResetFundedNodeCard

namespace OAI
/-! # Empty rectangular relay nodes on the original selected physical rack -/
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
local notation "widths_" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub widths_ (Z).bank (Z).tables
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

variable {H newH M : ℕ} (oldFits:Fintype.card input.V≤H) (grp:Fin (S.groupCount i)↪ℕ)
local notation "vertex_" => input.vertex.trans (Fin.castLEEmb oldFits)
variable (snap : GroupStage.RootObservation input.placement S input.valid (S.resetInputDigits ctl.base ctl.radix i)
  (input.order.trans Fin.valEmbedding) grp (input.vertex.trans (Fin.castLEEmb oldFits)) B.reset B.terminals B.frame field)
local notation "ranks_" => DescentSharedBookScan.ranks (a:=rr) («Y»:=2^(Z).n) (D:=(A).degree)
  snap.chart (2^height) (height+2) snap.memory
local notation:max "oldRow" row:arg => relayPhysicalRow B row
local notation:max "lo_" a:arg => (finProdFinEquiv.symm (incomingIndex B a)).1





open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentDatedAddressBook
open DescentPaidResidentCount Chronology
variable {p : ℕ} (hp : 0<p) (whole : p∣B.reset.unit) (a₀ : Archive W) (rank₀ : Local a₀.bit)
local notation "new_" => (resetArchive B p hp whole a₀).bit
local notation "number_" => DescentLocalArchiveOrder.reset B p hp whole a₀ rank₀
local notation:max "realRelay" t:arg => B.reblock.destination ((B.reset.resetNames B.terminals).symm (.inl (true,t)))
variable (ports : Chronology.DatePorts) (places : Chronology.DatePorts.RangeRoom ports B.next (resetArchive B p hp whole a₀).bit)
  (x₀ : Fin (2^ports.venue.k)) (slot : Fin ports.nodes) (rh : Fin ports.operandHosts) (rg : Fin ports.venue.groups)
  (inside : rh.val<Fintype.card B.next.V)
local notation "missing" => Chronology.DatePorts.slotAt ports B.next new_ number_ places x₀ slot rh rg=none
local notation:max "atRelay" t:arg => occupies B.next.placement (Equiv.refl _) B.next.vertex ⟨rh.val,inside⟩
  (rg.cast places.groups.symm) (x₀.cast (congrArg (2^·) places.radix.symm)) (realRelay t)

theorem relay_slot_padding (t : (Z).Fallback) (here : atRelay t) (ghost : missing) :
    Fintype.card {e : End₀ // land e=t}≤ slot.val:=by
  have absent:=Chronology.DatePorts.slot_absent_range ports B.next new_ number_ places x₀ slot rh rg inside ghost
  have side:=DescentPrimitivePalette.reached_card B hp whole a₀ (.inl (true,t))
  change Fintype.card ((new_).recipe (realRelay t)).Node =Fintype.card {e : End₀ // land e=t} at side
  by_contra! active
  exact absent ⟨realRelay t,here,by rwa [side]⟩

theorem relay_ghost_span (t : (Z).Fallback) (row : (pubCfg).Data (Z).n)
    (shape : ↥(DescentDenseHostOrder.roster (Z).graph rr height))
    (live : ((cfg).header ((pubCfg).basic row) 0).val≠0)
    (shapeAt : ((cfg).header ((pubCfg).basic row) 2).val=(localRank (Z).graph rr height shape).val)
    (kind : shape.val=.trunk true ((),(shortName (T).commonDepth ((T).code t)).2))
    (packet : (adjusted).packet (oldRow row)=DescentFallbackPeriod.inputs (field:=field)
      snap.stencil snap.peers snap.marks (fun v j=>(ranks_ v j).val)
      (vertex_ (B.frame.host.symm ((T).code t).1)) ((Z).rootBlock T (.inr t)))

    (node : Fin nodes) (arg : Fin args) (bits₁ : ℕ) (digit : Option (Fin 7))
    (whereAt : node.val=slot.val) (here : atRelay t) (ghost : missing) :
    (pubCfg).column B.reset.graph bits₁ digit (finProdFinEquiv (arg,node)) row=0:=by
  have padded:=relay_slot_padding B hp whole a₀ rank₀ ports places x₀ slot rh rg inside t here ghost
  rw [←whereAt] at padded
  have noRow:=relay_ghost B oldFits grp snap t row shape live shapeAt kind packet node.val arg.val padded
  exact public_empty B.reset.graph (pubCfg) arg node row bits₁ noRow digit

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
