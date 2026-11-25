import OAI.Hierarchy.TaggedWideSignedEndpointReads
import OAI.Hierarchy.TaggedWideCarriedRoom

namespace OAI
/-! Compiled before/preclip operands from both original role sheets on one native heap. -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.SiteControls
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProbeStage ProbeStage.CoreBoard ProbeStage.ReportSockets ProbeStage.CoreBoard.HistoryRoles WireTelescope NamedAperture Tagged PassiveWindow
open AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM DatedRoleSheets
open scoped Classical Fin.CommRing BigOperators
variable {h W k attempts N native n left right depth rom : ℕ} {S : PurchaseSampler}
  {π : Equiv.Perm (Fin (2^h))} {mark : Marks h W k attempts} {unique : Exclusive mark}
  {rows : Fin N≃Source S π depth mark} {pre mid id : Fin N→ℕ} {m : Memory native}
local notation "sites" => siteLast h (2^W) k+1
local notation "D" => stride k S.degree attempts
local notation "bits" => ProtocolRAMPurchaseSampler.bits (sites*D)
local notation "ends" => sorted S π depth mark ∘ rows
local notation "port" => named S π depth mark unique rows
local notation "raw" block => columns («D»:=D) n block sites bits (RoleROM.bank rom sites) .row
local notation "seat" qty:arg s:arg => PacketNeighbor.localSlot ends qty port (shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S)
  (named_coordinate S π depth mark unique rows) s
variable (oldSheet : ∀f,roleFact n S π depth mark unique rows left pre id m f)
    (newSheet : ∀f,roleFact n S π depth mark unique rows right mid id m f)
    (strides : RoleROM.Mounted rom (fun i : Fin (siteLast h (2^W) k+1)=>i.val*stride k S.degree attempts) m)
    (s : Fin (siteLast h (2^W) k+1)) (cap : ℕ) (rest want offer : Widths (siteLast h (2^W) k+1))
    (preBound : ∀i,pre i≤cap) (midBound : ∀i,mid i≤cap)
    (preShape : installedWidths (sorted S π depth mark ∘ rows) pre=rest+want) (midShape : installedWidths (sorted S π depth mark ∘ rows) mid=rest+offer)
local notation "l" => carried ends pre s preBound (seat pre s) preShape
local notation "r" => carried ends mid s midBound (seat mid s) midShape
local notation "col" => fun b : Bool=>raw (if b then right else left)
local notation "atPort" g => fun p : (portGraph sites).Port s => (g : Widths sites) p.val.1
local notation "reg" => (s.val:Word native)

include oldSheet newSheet strides in
theorem signed_measured_pair (low : Bool→Fin D→Expr)
    (preLow : ∀i,((low false i).eval m reg).val=((l).owner i).elim 0 (atPort want))
    (midLow : ∀i,((low true i).eval m reg).val=((r).owner i).elim 0 (atPort offer))
    (one : 1<2^native) (siteRoom : sites≤2^native) (spanRoom : sites*D≤2^native)
    (sortedIds : StrictMono id) (idFit : ∀i,id i<2^native) (doubleFit : 2*cap<2^native)
    (beforeRoom : ∀p : (portGraph sites).Port s,(rest+want) p.val.1≤cap)
    (middleRoom : ∀p : (portGraph sites).Port s,(rest+offer) p.val.1≤cap) :
    CompiledFields m reg (atPort rest) (atPort want) (atPort offer) l r col low := by
  have small : cap<2^native:=by omega
  have lo:=endpoints_of_sheet oldSheet strides cap s preBound (rest+want) preShape .row reg rfl one
    (fun i=>(preBound i).trans_lt small) siteRoom spanRoom sortedIds idFit small
    (fun p=>(beforeRoom p).trans_lt small) (low false) (atPort want) preLow
  have hi:=endpoints_of_sheet newSheet strides cap s midBound (rest+offer) midShape .row reg rfl one
    (fun i=>(midBound i).trans_lt small) siteRoom spanRoom sortedIds idFit small
    (fun p=>(middleRoom p).trans_lt small) (low true) (atPort offer) midLow
  have L:=carried_top ends pre s preBound (seat pre s) preShape beforeRoom
  have R:=carried_top ends mid s midBound (seat mid s) midShape middleRoom
  apply compile_fields m reg (atPort rest) (atPort want) (atPort offer) l r col low lo.1 hi.1 lo.2 hi.2 siteRoom small
    (fun i=>(L i).trans_lt small) (fun i=>(R i).trans_lt small)
  intro i j b
  have leftTop:=L i
  have rightTop:=R j
  have leftLow:=sheet_low_le l (atPort want) (fun p=>(Nat.le_add_left ..).trans (beforeRoom p)) i
  have rightLow:=sheet_low_le r (atPort offer) (fun p=>(Nat.le_add_left ..).trans (middleRoom p)) j
  change max ((l).base i-((l).view (atPort want) i).low) ((r).base j-((r).view (atPort offer) j).low)+
    (if b then ((r).view (atPort offer) j).low else ((l).view (atPort want) i).low)<2^native
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

end Hierarchy.ProtocolRAM.SiteControls
end

end OAI
