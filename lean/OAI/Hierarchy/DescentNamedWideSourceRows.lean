import OAI.Hierarchy.DescentNamedPaidExterior
import OAI.Hierarchy.DescentWideFullPins
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
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall DescentPackedProfileTape DescentSeedRoot DescentExteriorShelf
variable {α : Type} (rawSize : ℕ) (seed : Select X S.copies rawSize→α)
    (lo clockCap grain : ℕ) (schedule_ : List (Source α))
local notation "front_" => end_ (lo+extent grain schedule_) clockCap grain + 17*DescentExteriorShelf.span j rest s E
local notation "publicBase" => front_+DescentTerminalPaidBoot.total K W qs piece codes rawRows
local notation "extra_" => DescentTerminalPublicIdentity.total K W qs piece codes rawRows count
local notation "Full" => DescentTerminalFullPins.Candidate (α ⊕ Hidden E j rest s) K W qs piece rawRows
variable (all : DescentTerminalFullPins.Candidate (α ⊕ Hidden (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b p)) K W qs piece rawRows → Bool)
local notation "exteriorBits" => all ∘ DescentTerminalFullPins.history ∘ Sum.inr
local notation "terminalBits" => all ∘ DescentTerminalFullPins.chip

/-- The original sixteen-bank tape gives the paid row proposal and the public identity column together. -/
theorem wide_original_source_rows (payloadBits : ℕ) (m : Memory wb)
    (original : Port ((2^(j+(j+rest))*s)*P) (copiesWidth (2^(j+(j+rest))*s) X.width) → Bool)
    (ok : ∀a,stagesOK (M a) (publicRows X original a) (projected exteriorBits false a) (projected exteriorBits true a))
    (old : AddressPlan.Earlier U I stage (meter_).layout wb) (space : AddressPlan.last V U I channels floor < 2^wb)
    (word : 0<wb) (payload : 2^j*s ≤ wb) (low : front_+extra_≤floor)
    (srcLow : I.homes.base+I.homes.size ≤ floor)
    (homes : ∀i,I.homes.read m (i.val:Computability.VPVNP.BurstRAM.Word wb)=((home_ i).val:Computability.VPVNP.BurstRAM.Word wb))
    (source : Loaded origin M (publicRows X original) exteriorBits m)
    (chart : I.publicTapes=DescentTerminalPublicIdentity.controls (A).order.sorted publicBase count)
    (rect : qs*(W*piece) = 2^j*s) (empty : ℕ)
    (pinBank : I.candidate = DescentTerminalPaidBoot.candidate K W qs piece codes rawRows front_)
    (kept : ∀a<extra_,m (front_+a)=DescentTerminalFullPins.wideHeader X S.copies rawSize payloadBits wb seed lo clockCap grain schedule_
      count codes original all (front_+a)) :
    DescentTerminalEmitter.SourceRows (W:=W) (q:=qs) (piece:=piece)
      (U).terminal (L).emit (ev m) (leafExternal X G S b hp base width) (terminalBits ∘ Sum.inr)
      (packagePins X S.copies s (copyInput X s (power).symm original))
      (DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=qs) (p:=piece)
        codes (L).emit front_ empty) := by
  have supplied:=DescentTerminalFullPins.wideRetained_ranges X S.copies rawSize payloadBits wb seed lo clockCap grain schedule_
    count codes original all m kept
  change front_+(DescentTerminalPaidBoot.total K W qs piece codes rawRows+pad count)≤floor at low
  have allLow : publicBase+pad count≤floor:=by omega
  exact named_source_rows X G S b hp base width shell positive rawRows headerRows V I channels floor
    privateAt short literal publicBase m original exteriorBits ok old space word payload allLow srcLow supplied.2 homes
    source chart rect front_ empty terminalBits pinBank (by omega) supplied.1

theorem wide_preflight_source_rows (payloadBits cutoff : ℕ) (prior prim booked ports m : Memory wb)
    (original : Port ((2^(j+(j+rest))*s)*P) (copiesWidth (2^(j+(j+rest))*s) X.width) → Bool)
    (ok : ∀a,stagesOK (M a) (publicRows X original a) (projected exteriorBits false a) (projected exteriorBits true a))
    (old : AddressPlan.Earlier U I stage (meter_).layout wb) (space : AddressPlan.last V U I channels floor < 2^wb)
    (word : 0<wb) (payload : 2^j*s ≤ wb) (low : front_+extra_≤floor)
    (srcLow : I.homes.base+I.homes.size ≤ floor)
    (homes : ∀i,I.homes.read prim (i.val:Computability.VPVNP.BurstRAM.Word wb)=((home_ i).val:Computability.VPVNP.BurstRAM.Word wb))
    (source : Loaded origin M (publicRows X original) exteriorBits m)
    (chart : I.publicTapes=DescentTerminalPublicIdentity.controls (A).order.sorted publicBase count)
    (rect : qs*(W*piece) = 2^j*s) (empty : ℕ)
    (pinBank : I.candidate = DescentTerminalPaidBoot.candidate K W qs piece codes rawRows front_)
    (core : ∀u<extra_,prim (front_+u)=prior (front_+u))
    (bookFrame : ∀a<cutoff,booked a=prim a) (portsFrame : ∀a<cutoff,ports a=booked a)
    (headerLow : front_+extra_≤cutoff) (homeLow : I.homes.base+I.homes.size≤cutoff)
    (lateHeader : ∀u<extra_,m (front_+u)=ports (front_+u))
    (lateHomes : ∀a<I.homes.size,m (I.homes.base+a)=ports (I.homes.base+a))
    (kept : ∀a<extra_,prior (front_+a)=DescentTerminalFullPins.wideHeader X S.copies rawSize payloadBits wb seed lo clockCap grain schedule_
      count codes original all (front_+a)) :
    DescentTerminalEmitter.SourceRows (W:=W) (q:=qs) (piece:=piece)
      (U).terminal (L).emit (ev m) (leafExternal X G S b hp base width) (terminalBits ∘ Sum.inr)
      (packagePins X S.copies s (copyInput X s (power).symm original))
      (DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=qs) (p:=piece)
        codes (L).emit front_ empty) := by
  have keep_ (u : ℕ) (du : u<extra_) := (lateHeader u du).trans
    ((portsFrame _ (by omega)).trans ((bookFrame _ (by omega)).trans ((core u du).trans (kept u du))))
  have data_ (i : Fin count) : I.homes.read m (i.val:Computability.VPVNP.BurstRAM.Word wb)=((home_ i).val:Computability.VPVNP.BurstRAM.Word wb) := by
    rw [←homes i]
    unfold Bank.read
    have index_:=Nat.mod_lt (i.val:Computability.VPVNP.BurstRAM.Word wb).val (show 0<I.homes.size from Nat.two_pow_pos _)
    exact (lateHomes _ index_).trans ((portsFrame _ (by omega)).trans (bookFrame _ (by omega)))
  exact wide_original_source_rows (X:=X) (G:=G) (S:=S) (b:=b) (hp:=hp) (base:=base) (width:=width)
    (shell:=shell) (positive:=positive) (rawRows:=rawRows) (headerRows:=headerRows) (V:=V) (I:=I)
    (channels:=channels) (floor:=floor) (privateAt:=privateAt) (short:=short) (literal:=literal)
    (rawSize:=rawSize) (seed:=seed) (lo:=lo) (clockCap:=clockCap) (grain:=grain) (schedule_:=schedule_)
    (all:=all) (payloadBits:=payloadBits) (m:=m) (original:=original) (ok:=ok) (old:=old) (space:=space)
    (word:=word) (payload:=payload) (low:=low) (srcLow:=srcLow) (homes:=data_) (source:=source)
    (chart:=chart) (rect:=rect) (empty:=empty) (pinBank:=pinBank) (kept:=keep_)

theorem wide_purchased_source_rows (payloadBits cohortEnd : ℕ) (cohort ports m : Memory wb)
    (original : Port ((2^(j+(j+rest))*s)*P) (copiesWidth (2^(j+(j+rest))*s) X.width) → Bool)
    (ok : ∀a,stagesOK (M a) (publicRows X original a) (projected exteriorBits false a) (projected exteriorBits true a))
    (old : AddressPlan.Earlier U I stage (meter_).layout wb) (space : AddressPlan.last V U I channels floor < 2^wb)
    (word : 0<wb) (payload : 2^j*s ≤ wb) (low : front_+extra_≤floor)
    (srcLow : I.homes.base+I.homes.size ≤ floor)
    (homes : ∀i,I.homes.read cohort (i.val:Computability.VPVNP.BurstRAM.Word wb)=((home_ i).val:Computability.VPVNP.BurstRAM.Word wb))
    (source : Loaded origin M (publicRows X original) exteriorBits m)
    (chart : I.publicTapes=DescentTerminalPublicIdentity.controls (A).order.sorted publicBase count)
    (rect : qs*(W*piece) = 2^j*s) (empty : ℕ)
    (pinBank : I.candidate = DescentTerminalPaidBoot.candidate K W qs piece codes rawRows front_)
    (purchase : ∀a<cohortEnd, ports a=cohort a)
    (early : front_+extra_≤cohortEnd) (homeEarly : I.homes.base+I.homes.size≤cohortEnd)
    (late : ∀u<extra_,m (front_+u)=ports (front_+u))
    (homeLate : ∀a<I.homes.size,m (I.homes.base+a)=ports (I.homes.base+a))
    (kept : ∀a<extra_,cohort (front_+a)=DescentTerminalFullPins.wideHeader X S.copies rawSize payloadBits wb seed lo clockCap grain schedule_
      count codes original all (front_+a)) :
    DescentTerminalEmitter.SourceRows (W:=W) (q:=qs) (piece:=piece)
      (U).terminal (L).emit (ev m) (leafExternal X G S b hp base width) (terminalBits ∘ Sum.inr)
      (packagePins X S.copies s (copyInput X s (power).symm original))
      (DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=qs) (p:=piece)
        codes (L).emit front_ empty) := by
  have keep_ (u : ℕ) (hu : u<extra_) := (late u hu).trans ((purchase _ (by omega)).trans (kept u hu))
  have data_ (i : Fin count) : I.homes.read m (i.val:Computability.VPVNP.BurstRAM.Word wb)=((home_ i).val:Computability.VPVNP.BurstRAM.Word wb) := by
    rw [←homes i]
    unfold Bank.read
    have index_:=Nat.mod_lt (i.val:Computability.VPVNP.BurstRAM.Word wb).val (show 0<I.homes.size from Nat.two_pow_pos _)
    exact (homeLate _ index_).trans (purchase _ (by omega))
  exact wide_original_source_rows (X:=X) (G:=G) (S:=S) (b:=b) (hp:=hp) (base:=base) (width:=width)
    (shell:=shell) (positive:=positive) (rawRows:=rawRows) (headerRows:=headerRows) (V:=V) (I:=I)
    (channels:=channels) (floor:=floor) (privateAt:=privateAt) (short:=short) (literal:=literal)
    (rawSize:=rawSize) (seed:=seed) (lo:=lo) (clockCap:=clockCap) (grain:=grain) (schedule_:=schedule_)
    (all:=all) (payloadBits:=payloadBits) (m:=m) (original:=original) (ok:=ok) (old:=old) (space:=space)
    (word:=word) (payload:=payload) (low:=low) (srcLow:=srcLow) (homes:=data_) (source:=source)
    (chart:=chart) (rect:=rect) (empty:=empty) (pinBank:=pinBank) (kept:=keep_)


end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
