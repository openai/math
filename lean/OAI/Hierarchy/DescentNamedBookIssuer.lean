import OAI.Hierarchy.DescentNamedBookAligned
import OAI.Hierarchy.DescentNamedLeafBookRoom
import OAI.Hierarchy.DescentTerminalWeightedBook

namespace OAI
/-! Issuing all six row-plan source banks from real measured geometry before planning. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


local notation "s" => S.firstWidth G.b p
local notation "net" => ((Epochs.finish G hu he r).state c).graph
local notation "E" => Fintype.card (Port P X.width)
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))



open DescentTerminalGraphPositions DescentTerminalCableOrder DescentTerminalLocalPortBook DescentSharedCableNames DescentColonies
open ThreeFlat.Routing
local notation "retained" => S.groupWidth k tail S.length+k
local notation "O" => leafOrder X G S b hp base width
local notation "placement" => b.target.placement
local notation "native" => b.target.order.trans Fin.valEmbedding
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount S.length)) (b.target.vertex.trans Fin.valEmbedding))
local notation "pinRank" v => (densePinEquiv X G S b hp base v).toEmbedding.trans Fin.valEmbedding
local notation "operand" v => leafOperands X G S b hp base v
local notation "calendar" => fun g row => ((S.resetInputDigits base radix S.length).symm (g,row)).val
local notation "scale" => ((placement).z*G.b)/p


open DescentTerminalPaidHeaderEvents DescentTerminalGrainProfiles DescentTerminalPeerChronology DescentTerminalGraphRows
open DescentSortedRoster DescentPhysicalOrder DescentPacking
local notation "H0" => S.hostSize S.length
local notation "hosts" => b.target.vertex.trans (Fin.castLEEmb b.target.valid.host)
local notation "nodeRank" => ((placement).site b.target.vertex b.target.valid.coordinates).trans Fin.valEmbedding
local notation "outs" => leafExternal X G S b hp base width
local notation "ins" => leafOperands X G S b hp base

open DescentSIMDLookup DescentTerminalRecipeRows DescentTerminalPointerDigits ProtocolRAM Calendar Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "V0" => S.groupCount S.length*2^k
local notation "A0" => NativeBranch.localLimit G S
local notation "M0" => V0*A0

variable (rack:Rasters b.target.placement.degree (2^k) b.target.placement.cap)
    (argc short first weightsAt:ℕ)
local notation "machine" => rack.controller H0 first short
local notation "bought" => Book.WeightShelf.banks V0 A0 weightsAt
local notation "table" => fun z=>((Rasters.measure (placement).degree (2^k) (placement).cap (S.groupCount S.length) argc z).directory
  A0 scale (s/p) (2^retained) calendar).extend (show (placement).degree+1≤4 by rw [b.target.branch])

def bookPrinter (w:ℕ) : Procedure w := (Book.WeightShelf.program V0 A0 weightsAt w).seq ((machine).prefix table M0 w 6 le_rfl)

def bookMemory {w:ℕ} (m:Memory w) : Memory w := (machine).memory table M0 (Book.WeightShelf.memory V0 A0 weightsAt m) 6 le_rfl

/-- Live private and public inputs share a weighted six-column schema, including
both original endpoint coordinates and every physical padding state. -/
theorem book_issued {w:ℕ} (elapsed:0<S.length) (room:j≤retained) (whole:p∣s)
    (raw:Fin H0→Fin (placement).degree→Option (Fin H0)) (m:Memory w)
    (original:Rasters.Inputs (p:=p) (bw:=short) (argc:=argc) placement hosts S b.target.valid b.target.order raw rack m)
    (source:∀l,((machine).source l).Fits w weightsAt) (mounted:Book.WeightShelf.finish V0 A0 weightsAt≤first)
    (token:2^short<2^w) (space:(machine).stop<2^w) :
    let action:=bookPrinter X G S b base rack argc short first weightsAt w
    let after:=bookMemory X G S b base rack argc short first weightsAt m
    action.Exec m after (4+10*Book.WeightShelf.words V0 A0+(machine).time 6 le_rfl) ∧
      CheapCode action ∧
      Book.Issued ((machine).parts bought) (fun i=>issue ((O).site i) (leaf_local_room X G S b hp base width i)
        (rowName ((O).site i) (leaf_local_room X G S b hp base width i)) (refName ((O).site i) (leaf_local_room X G S b hp base width i))) after ∧ ∀a,a<weightsAt→after a=m a := by
  let boards:=fun h:Fin H0=>Rasters.measure (placement).degree (2^k) (placement).cap (S.groupCount S.length) argc
    (Gather.values (d:=short) rack.sources m h)
  have seen:=Rasters.observed placement hosts S b.target.valid b.target.order raw rack m original
  exact (machine).weighted_issued table weightsAt m source mounted token space (O).site
    (leaf_local_room X G S b hp base width)
    (fun i=>(book_aligned X G S b hp base width elapsed room whole raw boards seen A0 i).extend (p:=p) (by rw [b.target.branch]))

end
end Hierarchy.DescentSixParty.SeedNamed.Branch
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
