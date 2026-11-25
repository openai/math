import OAI.Hierarchy.ProtocolRAMDateSpillProjection
import OAI.Hierarchy.ProbeFixedWideSpillOffsets

namespace OAI
/-! # Measured spill offsets from the original two mounted date sheets -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM DescriptorExpr
open ProbeStage ProbeStage.ReportSockets ProbeStage.CoreBoard ProbeStage.CoreBoard.HistoryRoles WireTelescope NamedAperture Tagged PassiveWindow
open AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM DatedRoleSheets
open scoped Classical Fin.CommRing BigOperators
variable {h W k attempts N native : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
  (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark) (rows : Fin N≃Source S π depth mark)
local notation "sites" => siteLast h (2^W) k+1
local notation "degreeSlots" => stride k S.degree attempts
local notation "ends" => sorted S π depth mark ∘ rows
local notation "port" => named S π depth mark unique rows
variable (n full only bits : ℕ) (s : Fin (siteLast h (2^W) k+1)) (qty whole id : Fin N→ℕ) (m : Memory native)
    (onlyRead : ∀f,roleFact n S π depth mark unique rows only qty id m f)
    (fullRead : ∀f,roleFact n S π depth mark unique rows full whole id m f)
    (table : Bank) (reg : Word native) (site role : Bank) (one : 1<2^native)
    (qtyRoom : ∀i,qty i<2^native) (allRoom : ∀i,whole i<2^native)
    (wordRoom : (siteLast h (2^W) k+1)*(stride k S.degree attempts)≤2^native)
    (bankRoom : (siteLast h (2^W) k+1)*(stride k S.degree attempts)≤2^bits)
    (atSite : table.read m (site.read m reg)=((s.val*(stride k S.degree attempts):ℕ):Word native))
    (idFits : ∀i,id i<2^native) (siteFits : siteLast h (2^W) k+1≤2^native)
local notation "slot" => (fun (amount : Fin N → ℕ) => PacketNeighbor.localSlot ends amount port
  (shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S) (named_coordinate S π depth mark unique rows) s)
local notation "sheetColumns" => (fun (base : ℕ) => SiteControls.columns (D:=degreeSlots) n base sites bits table (Expr.lookup site Expr.row))
include onlyRead fullRead one qtyRoom allRoom wordRoom bankRoom atSite idFits siteFits in
/-- The low section of the full chronological port consists of every positive
spill row on its physical chord, regardless of whether the owner itself spills. -/
theorem mounted_spill_low (a : EndsAt ends whole s) :
    (WideCPU.spillLow (sheetColumns full) (sheetColumns only) (slot whole a)).eval m reg=
      (installedWidths ends qty (byRow ends whole s a).val.1:Word native) := by
  have left:=SiteControls.dated_columns S π depth mark unique rows n only bits s qty id (fun i=>(qtyRoom i).le)
    rfl m onlyRead table (Expr.lookup site .row) reg one qtyRoom wordRoom bankRoom atSite idFits siteFits
  have right:=SiteControls.dated_columns S π depth mark unique rows n full bits s whole id (fun i=>(allRoom i).le)
    rfl m fullRead table (Expr.lookup site .row) reg one allRoom wordRoom bankRoom atSite idFits siteFits
  have on : ((sheetColumns full (slot whole a)).width.eval m reg)≠0 := by
    intro z
    have zero:=congrArg Fin.val z
    have width:=(right.1 a).2.2
    rw [width] at zero
    exact (Nat.ne_of_gt a.property) zero
  exact spillLow_seen ends qty s (slot qty) id m reg (sheetColumns only) (byRow ends whole s a) (sheetColumns full)
    (slot whole a) left on (right.1 a).2.1

include onlyRead fullRead one qtyRoom allRoom wordRoom bankRoom atSite idFits siteFits in
/-- Both chronological components, the original full peer and the sparse spend,
are fetched from the actual dated boards. The saved role bank is the compiler's
even/odd tagged coordinate, and the input query is its original ordinal. -/
theorem mounted_spill_prefix (amountRows : ℕ) (ordinal : Expr) (a : EndsAt ends whole s) (reported : Bool)
    (wideRole : 2*degreeSlots≤2^native) (tag : role.read m reg=((2*(slot whole a).val+reported.toNat:ℕ):Word native))
    (ord : (ordinal.eval m reg).val=id a.val.val.1) (increasing : StrictMono id) :
    (Side.fromSector (D:=degreeSlots) amountRows n sites full only bits table site role ordinal).prefix.eval m reg=
      (prefixAt ends qty a.val.val.1:Word native) := by
  have left:=SiteControls.dated_columns S π depth mark unique rows n only bits s qty id (fun i=>(qtyRoom i).le)
    rfl m onlyRead table (Expr.lookup site .row) reg one qtyRoom wordRoom bankRoom atSite idFits siteFits
  have right:=SiteControls.dated_columns S π depth mark unique rows n full bits s whole id (fun i=>(allRoom i).le)
    rfl m fullRead table (Expr.lookup site .row) reg one allRoom wordRoom bankRoom atSite idFits siteFits
  apply Side.prefix_seen ends qty s (slot qty) id m reg (sheetColumns only) (byRow ends whole s a) _ rfl left increasing
      a.val.val.1 rfl ord
  rw [Side.fromSector_opposite amountRows n sites full only bits table site role ordinal m reg
    (slot whole a) reported wideRole tag]
  exact (right.1 a).2.1

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
end

end OAI
