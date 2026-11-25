import OAI.Hierarchy.DescentNamedPublishedExterior
import OAI.Hierarchy.DescentTerminalPaidSourceRows
import OAI.Hierarchy.DescentTerminalPlacedChipInit

namespace OAI
/-! # Both original input streams in the same mounted terminal memory -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open CorrectionFrame
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open DescentTerminalCompiledPrefix DescentTerminalVertexFields DescentTerminalPrimitiveArena
open DescentExteriorShelf DescentTerminalPublicIdentity Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
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



local notation "count" => E*2^(j+rest)
local notation "H" => S.hostSize S.length
local notation "M" => publicLayout X G S b hp base width
local notation "home_" => publicHost X G S b hp base width
local notation "power" => NativeBranch.copy_power S (radix:=radix) base width
variable (shell : DescentTerminalCompiledPrefix.Shape) (positive : 0 < S.hostSize S.length) (rawRows headerRows : ℕ)


local notation "U" => exteriorShape shell E j rest s rawRows headerRows H positive
variable {blocks ν bound wb : ℕ} (V : Home.Format) (I : AddressPlan.Input)
    (channels : MaskAllocation.Channels blocks) (floor privateAt : ℕ)
    (short : ν*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece ≤ bound)
    (literal : DescentTerminalEmitter.Compact.Literals I.sources)
local notation "stage" => AddressPlan.afterMeter V U channels floor
local notation "origin" => AddressPlan.takeOff U I stage
local notation "A" => AddressPlan.rowArena U I stage
local notation "meter_" => AddressPlan.meter V channels floor
local notation "regs" => AddressPlan.registers V U channels floor privateAt
local notation "L" => AddressPlan.layout U I stage regs
local notation "input" => AddressPlan.input V U I channels floor privateAt short literal
local notation "ev" => fun m : Memory wb => Suffix.events U L (meter_).layout ((A).mount (input m))
local notation "plane" => AddressPlan.bodyPlane U I stage

variable {K W qs piece codes : ℕ}
theorem named_source_rows (idAt : ℕ) (m : Memory wb)
    (original : Port ((2^(j+(j+rest))*s)*P) (copiesWidth (2^(j+(j+rest))*s) X.width) → Bool)
    (hidden : Hidden E j rest s→Bool)
    (ok : ∀a,stagesOK (M a) (publicRows X original a) (projected hidden false a) (projected hidden true a))
    (old : AddressPlan.Earlier U I stage (meter_).layout wb) (space : AddressPlan.last V U I channels floor < 2^wb)
    (word : 0<wb) (payload : 2^j*s ≤ wb) (idLow : idAt+pad count ≤ floor)
    (srcLow : I.homes.base+I.homes.size ≤ floor)
    (idRows : ∀u<pad count,m (idAt+u)=(u:Computability.VPVNP.BurstRAM.Word wb))
    (homes : ∀i,I.homes.read m (i.val:Computability.VPVNP.BurstRAM.Word wb)=((home_ i).val:Computability.VPVNP.BurstRAM.Word wb))
    (source : Loaded origin M (publicRows X original) hidden m)
    (chart : I.publicTapes=controls (A).order.sorted idAt count)
    (rect : qs*(W*piece) = 2^j*s) (front empty : ℕ)
    (paid : DescentTerminalPaidBoot.Input K W qs piece rawRows → Bool)
    (pinBank : I.candidate = DescentTerminalPaidBoot.candidate K W qs piece codes rawRows front)
    (under : front+DescentTerminalPaidBoot.total K W qs piece codes rawRows ≤ floor)
    (boot : ∀ u < DescentTerminalPaidBoot.total K W qs piece codes rawRows,
      m (front+u) = DescentTerminalPaidBoot.back paid wb codes u) :
    DescentTerminalEmitter.SourceRows (W:=W) (q:=qs) (piece:=piece)
      (U).terminal (L).emit (ev m) (leafExternal X G S b hp base width) (paid ∘ Sum.inr)
      (packagePins X S.copies s (copyInput X s (power).symm original))
      (DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=qs) (p:=piece)
        codes (L).emit front empty) := by
  apply AddressPlan.paid_sources U I stage (meter_).layout old paid codes front empty (ev m)
    (leafExternal X G S b hp base width) (packagePins X S.copies s (copyInput X s (power).symm original)) pinBank
  · intro u hu
    exact (AddressPlan.events_original V U I channels floor privateAt short literal m old space
      ((Nat.add_lt_add_left hu front).trans_le under)).trans (boot u hu)
  · change (∑ _ : (Σ _:Fin S.copies,Fin E),s*1) ≤ count*(qs*(W*piece))
    rw [rect]
    exact (public_volume X G S (p:=p) (radix:=radix) base width).le
  · intro i
    rw [rect]
    exact published_public X G S b hp base width shell positive rawRows headerRows V I channels floor
      privateAt short literal idAt m original hidden ok old space word payload idLow srcLow idRows homes source chart i

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
