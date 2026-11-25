import OAI.Hierarchy.TaggedWideTerminalROM
import OAI.Hierarchy.ProbeFixedWideDated
import OAI.Hierarchy.TaggedWideROMRead
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # The checkout and site ROM read at each processing snapshot -/

noncomputable section
open scoped Classical Fin.CommRing
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard PurchaseFrozen
open Tagged Tagged.WideStack

/-- The low checkout and the installed dated read-only interval still belong
to this same signed native run. -/
structure ProcessingArchive {W : ℕ} (top root stop : ℕ)
    (checked image processing : Memory W) : Prop where
  checkout : PrefixAgreement.Low top processing checked
  rom : ∀i,root ≤ i → i < stop → processing i=image i

theorem ProcessingArchive.frame {W top root stop cut : ℕ} {checked image current next : Memory W}
    (P : ProcessingArchive top root stop checked image current)
    (low : ∀i < cut,next i=current i) (below : top ≤ cut) (endROM : stop ≤ cut) :
    ProcessingArchive top root stop checked image next :=
  ⟨fun i hi=>(low i (hi.trans_le below)).trans (P.checkout i hi),
   fun i lo hi=>(low i (hi.trans_le endROM)).trans (P.rom i lo hi)⟩

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A)
    (ell unitCost : ℕ)
local notation "d" => 2^v.W
local notation "w" => Native.wordBits x.h d Native.copies
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "root" => v.wideInstalledRoot x
local notation "sites" => v.wide_dated_sites x.h x.w ell unitCost
local notation "edges" => v.wide_dated_edges x.h x.w ell unitCost
local notation "board" => (v.widePlacement x.h x.w).catalogue

theorem processing_sites {top : ℕ} (raw checked seen : Memory w)
    (received : ProcessingArchive top root ((dated).romEnd root) checked
      (v.wideTerminalPreimage x dated sites edges raw) seen) :
    HistoryRoles.RoleROM.Mounted ((dated).siteROM root) (SiteDirectory.table x.h d k) seen := by
  intro i
  let j : Fin (dated).siteDirectorySize := i.cast (sites).symm
  let table := fun t : Fin (dated).siteDirectorySize=>SiteDirectory.table x.h d k (t.cast sites)
  let transport := fun t : Fin (dated).rawEdges=>
    decide ((board).transport (v.wideOrder x.h x.w) (t.cast edges))
  have address := (dated).site_mounted root table transport raw j
  have stop : (dated).siteROM root+(dated).siteDirectorySize ≤ (dated).romEnd root := by
    simp only [WideCPU.Dated.romEnd,WideCPU.Dated.maskROM,WideCPU.Dated.controlROMStart,
      WideCPU.Dated.firstROM,WideCPU.endOf]
    omega
  apply (received.rom _ (by change root ≤ root+_+_; omega)
    ((Nat.add_lt_add_left j.isLt _).trans_le stop)).trans
  have site : j.cast sites = i := Fin.ext rfl
  have entry : table j = SiteDirectory.table x.h d k i :=
    congrArg (SiteDirectory.table x.h d k) site
  exact address.trans (congrArg (fun n : ℕ => (n : Word w)) entry)

/-- Each chronological reader initializes its role slot lookup with the same stride ROM. -/
theorem processing_stride {top : ℕ} (raw checked seen : Memory w)
    (received : ProcessingArchive top root ((dated).romEnd root) checked
      (v.wideTerminalPreimage x dated sites edges raw) seen) :
    HistoryRoles.RoleROM.Mounted root (fun i : Fin (dated).sites=>i.val*(dated).roleCount) seen := by
  intro i
  let table := fun t : Fin (dated).siteDirectorySize=>SiteDirectory.table x.h d k (t.cast sites)
  let transport := fun t : Fin (dated).rawEdges=>
    decide ((board).transport (v.wideOrder x.h x.w) (t.cast edges))
  have block : root+(dated).sites ≤ (dated).romEnd root := by
    simp only [WideCPU.Dated.romEnd,WideCPU.Dated.maskROM,WideCPU.Dated.controlROMStart,
      WideCPU.Dated.firstROM,WideCPU.Dated.siteROM,WideCPU.endOf]
    omega
  exact (received.rom _ (Nat.le_add_right ..) ((Nat.add_lt_add_left i.isLt root).trans_le block)).trans
    ((dated).stride_mounted root table transport raw i)

theorem processing_stride_read {top : ℕ} (raw checked seen : Memory w)
    (received : ProcessingArchive top root ((dated).romEnd root) checked
      (v.wideTerminalPreimage x dated sites edges raw) seen)
    (room : (dated).sites ≤ 2^w) (party : Expr) (row : Word w)
    (site : Fin (dated).sites) (found : party.eval seen row=(site.val:Word w)) :
    ((dated).siteStride root).read seen (party.eval seen row)=((site.val*(dated).roleCount:ℕ):Word w) :=
  HistoryRoles.RoleROM.read (v.processing_stride x ell unitCost raw checked seen received)
    party row site room found

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
