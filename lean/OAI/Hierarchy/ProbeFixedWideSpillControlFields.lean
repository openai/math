import OAI.Hierarchy.TaggedWideControlProjection
import OAI.Hierarchy.ProbeFixedWideCorrectedControl
import OAI.Hierarchy.ProtocolRAMDateSpillControlEndpoint
import OAI.Hierarchy.ProtocolRAMDateSpillSectorRead
import OAI.Hierarchy.TaggedWideCalendarSpillAddress

namespace OAI
/-! # All native spill output words at their actual physical issued addresses -/
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
local notation "src" => fun b : Bool=>columnsAt (if b then (g).roleStart old j.succ else (z).preClip old start j)
local notation "sparse" => fun b : Bool=>columnsAt (if b then (z).dateRole start j 2 else (z).dateRole start j 1)
local notation "cuts" => fun b : Bool=>spillLow (src b) (sparse b)
local notation "fields" => v.wideCorrectedControlFields h width ell unitCost bits first rom old start j true
local notation "base" => v.wideCorrectedControlStart h width ell unitCost bits first start j true

theorem wide_spill_control_fields (out prior : Memory W) (pass before after : P→ℕ)
    (l : Parts P (Fin degreeSlots) C fun p=>pass p+before p) (r : Parts P (Fin degreeSlots) C fun p=>pass p+after p)
    (native : ∀c : Fin (fieldCount degreeSlots),out (base+1+(SiteScatter.pos s c).val)=((fields).value (0 : Fin 1) c).eval prior (s.val:Word W))
    (compiled : CompiledFields prior (s.val:Word W) pass before after l r src cuts) (f : SiteControls.Field degreeSlots) :
    (out (controlAddress g ((z).spillControlWork start) j s f)).val=expected pass before after l r f := by
  have atField:=native (fieldNumber degreeSlots f)
  have addr : controlAddress g ((z).spillControlWork start) j s f=base+1+(SiteScatter.pos s (fieldNumber degreeSlots f)).val := by
    refine ((z).spillControlAddress start j s f).trans ?_
    change (z).spillStart start j+1+s.val*(g).controlColumns j+(fieldNumber degreeSlots f).val=
      (z).spillStart start j+1+(SiteScatter.pos s (fieldNumber degreeSlots f)).val
    simp only [SiteScatter.pos,finProdFinEquiv_apply_val]
    change (z).spillStart start j+1+s.val*fieldCount degreeSlots+(fieldNumber degreeSlots f).val=_
    ring
  rw [addr,atField]
  simp only [wideCorrectedControlFields, ↓reduceIte, spillControls, Equiv.symm_apply_apply]
  exact CompiledFields.project pass before after l r prior _ src cuts compiled f

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
