import OAI.Hierarchy.ProbeFixedWideSpillControlFields
import OAI.Hierarchy.TaggedWideSignedEndpointReads
import OAI.Hierarchy.ProtocolRAMDateSpillControlRoom

namespace OAI
/-! # The signed before/preclip control words on the retained physical heap -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard HistoryRoles WideCPU SiteControls WireTelescope.PassMatrix
open LinearAlgebra.SpectralBooks ChordGraph Tagged PassiveWindow
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width ell unitCost bits first rom old start : ℕ)
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "T" => (events v.mesh).length
local notation "g" => v.wideDated h width ell unitCost
local notation "z" => v.wideSpillDates h width ell unitCost bits first
local notation "degreeSlots" => (g).roleCount
local notation "C" => (z).cap
local notation "sh" => (g).siteStride rom
variable (j : Fin (events v.mesh).length) (s : Fin (v.wideDated h width ell unitCost).sites)
local notation "P" => (portGraph (g).sites).Port s
local notation "columnsAt" block => columns (D:=degreeSlots) (g).physical block (g).sites
  (ProtocolRAMPurchaseSampler.bits ((g).sites*degreeSlots)) sh .row

local notation "root" => (z).roleRoot start 2
local notation "beforePage" => (g).roleStart old j.castSucc
local notation "middlePage" => (z).dateRole start j 0
local notation "ballot" => (g).ballotStart root j+1
local notation "col" => fun b : Bool=>columnsAt (if b then middlePage else beforePage)
local notation "cuts" => lowFieldFrom (D:=degreeSlots) (v.widePacketLowStart h width ((events v.mesh).get j))
  (g).sites ballot ((g).ballot j).columns
local notation "fields" => v.wideCorrectedControlFields h width ell unitCost bits first rom old start j false
local notation "base" => v.wideCorrectedControlStart h width ell unitCost bits first start j false

/-- Read one of the five control operands from its native output address.
The two endpoints use the original before and preclip rows respectively.
Each ballot low width is read from the elected signed packet. -/
theorem wide_signed_compiled_output (out prior : Memory W) (pass before after : P→ℕ)
    (l : Parts P (Fin degreeSlots) C fun p=>pass p+before p) (r : Parts P (Fin degreeSlots) C fun p=>pass p+after p)
    (native : ∀c : Fin (fieldCount degreeSlots),out (base+1+(SiteScatter.pos s c).val)=((fields).value (0 : Fin 1) c).eval prior (s.val:Word W))
    (complete : CompiledFields prior (s.val:Word W) pass before after l r col cuts)
    (f : SiteControls.Field degreeSlots) :
    (out (controlAddress g root j s f)).val=expected pass before after l r f := by
  have addr : controlAddress g root j s f=base+1+(SiteScatter.pos s (fieldNumber degreeSlots f)).val := by
    change (g).controlBase root j+1+s.val*(g).controlColumns j+(fieldNumber degreeSlots f).val=
      (g).controlBase root j+1+(SiteScatter.pos s (fieldNumber degreeSlots f)).val
    simp only [SiteScatter.pos,finProdFinEquiv_apply_val]
    change (g).controlBase root j+1+s.val*fieldCount degreeSlots+(fieldNumber degreeSlots f).val=_
    ring
  rw [addr,native (fieldNumber degreeSlots f)]
  change ((compile C col cuts ((fieldNumber degreeSlots).symm (fieldNumber degreeSlots f))).eval prior (s.val:Word W)).val=_
  rw [Equiv.symm_apply_apply]
  exact CompiledFields.project pass before after l r prior _ col cuts complete f

theorem wide_signed_control_fields (out prior : Memory W) (pass before after : P→ℕ)
    (l : Parts P (Fin degreeSlots) C fun p=>pass p+before p) (r : Parts P (Fin degreeSlots) C fun p=>pass p+after p)
    (native : ∀c : Fin (fieldCount degreeSlots),out (base+1+(SiteScatter.pos s c).val)=((fields).value (0 : Fin 1) c).eval prior (s.val:Word W))
    (left : EndpointReads prior (s.val:Word W) l (col false) (cuts false) before)
    (right : EndpointReads prior (s.val:Word W) r (col true) (cuts true) after)
    (leftGeo : ApertureGeometry prior (s.val:Word W) l (col false))
    (rightGeo : ApertureGeometry prior (s.val:Word W) r (col true))
    (siteFit : (g).sites≤2^W) (capFit : C<2^W)
    (upperL : ∀i,l.base i+l.width i<2^W) (upperR : ∀i,r.base i+r.width i<2^W)
    (offsets : ∀i k side,lo (l.view before i) (r.view after k)+
      (if side then (r.view after k).low else (l.view before i).low)<2^W)
    (f : SiteControls.Field degreeSlots) :
    (out (controlAddress g root j s f)).val=expected pass before after l r f := by
  have complete:=SiteControls.compile_fields prior (s.val:Word W) pass before after l r col cuts
    left right leftGeo rightGeo siteFit capFit upperL upperR (fun i k side => by
      have bound := offsets i k (side = true)
      cases side <;> simpa only [Bool.false_eq_true, ite_false, ite_true] using bound)
  exact v.wide_signed_compiled_output h width ell unitCost bits first rom old start j s out prior
    pass before after l r native complete f

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
