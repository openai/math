import OAI.Hierarchy.ProtocolRAMStripOriginalReads
import OAI.Hierarchy.TaggedWireEarnedSites
import OAI.Hierarchy.TaggedWireEarnedStock

namespace OAI
/-! # The original placement operands fit below the current histogram slab -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe
open StripChart StripDirectory CatalogueRows BoughtSockets CatalystArchive ReportSockets
open scoped Classical Fin.CommRing

namespace CatalogueRows.StripPorts
variable {S : PurchaseSampler} {h d k w cut : ℕ} {C H A B : Type*}
    (p : StripPorts S h d k C H B) (b : Board) (stored : A→Expr)
local notation "R" => ColumnWires.Role C H (A⊕B) k

variable {p b stored}
theorem OriginalFits.read (f : p.OriginalFits b stored w cut) {left right : Memory w}
    (low : PrefixAgreement.Low cut left right) : p.OriginalReads b stored left right := by
  have eq (e : Expr) (fits : e.Fits w cut) (reg : Word w) : e.eval left reg=e.eval right reg :=
    PrefixAgreement.expr e left right cut (PrefixAgreement.inputEnd_of_fits e fits) low reg
  exact ⟨fun r=>eq _ (f.primary r),fun r=>eq _ (f.mate r),fun c=>eq _ (f.column c),fun u=>eq _ (f.stock u)⟩

variable (p b stored)
theorem originalFits_of_primary (axis : Fin k)
    (primary : ∀r:R,(p.primary b r).Fits w cut) (stock : ∀u,(stored u).Fits w cut) :
    p.OriginalFits b stored w cut := by
  refine ⟨primary,?_,fun c=>(primary (.catalyst c axis)).1.2,stock⟩
  intro r
  cases r with
  | catalyst c j=>exact primary (.radius c j true)
  | radius | cross | horizontal | extra=>trivial

end CatalogueRows.StripPorts

namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ) (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "w" => wordBits h (2^v.W) copies
local notation "floor" a => (A).base v.mesh (.attempt a)

def EarnedBefore (a : Attempt) : Prop :=
  match a with
  | .outer phase trial => (v.payloadPricePorts P h width).OriginalFits (P).catalogue
      (v.widePayloadStored P h width phase trial) w (floor a)
  | .inner phase trial tick repairIndex => (v.purchasedPricePorts P h width phase trial).OriginalFits (P).catalogue
      (v.widePurchaseStored P h width phase trial tick repairIndex) w (floor a)

def EarnedReads (a : Attempt) (left right : Memory w) : Prop :=
  match a with
  | .outer phase trial => (v.payloadPricePorts P h width).OriginalReads (P).catalogue
      (v.widePayloadStored P h width phase trial) left right
  | .inner phase trial tick repairIndex => (v.purchasedPricePorts P h width phase trial).OriginalReads (P).catalogue
      (v.widePurchaseStored P h width phase trial tick repairIndex) left right

/-- The original parent shelf precedes an inner ballot even when the later
histogram choices change. The direct, opposite, site-column and inventory
operands all lie strictly below the current slab. -/
theorem wide_earned_before (a : Attempt) (word : (floor a)<2^w) : v.EarnedBefore h width a := by
  let limit:=(A).base v.mesh (.attempt a)
  have first : (A).first≤limit:=Nat.le_add_right ..
  have core:=(v.wideGeometryPrefix h width).2.2.trans ((v.catalyst_initial_le_first P h width).trans first)
  obtain ⟨_,indices,cols,atlas,keys⟩:=v.diagnostic_original h (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
    (WideMemory.R v.sampler h v.W k) 0 (v.wideSources h width).2 limit core word
  have prim:=v.chronological_ports P h width a limit word le_rfl indices cols atlas keys
  let axis : Fin k:=⟨0,v.positive⟩
  cases a with
  | outer phase trial =>
    exact StripPorts.originalFits_of_primary _ _ _ axis prim (v.payload_stored_fits P h width phase trial _)
  | inner phase trial tick repairIndex =>
    exact StripPorts.originalFits_of_primary _ _ _ axis prim
      (fun u=>v.purchased_stored_fits P h width phase trial tick repairIndex _ u word le_rfl keys)

theorem wide_earned_words (a : Attempt) (word : (floor a)<2^w) {left right : Memory w}
    (low : PrefixAgreement.Low (floor a) left right) : v.EarnedReads h width a left right := by
  have physical:=v.wide_earned_before h width a word
  cases a
  · exact StripPorts.OriginalFits.read physical low
  · exact StripPorts.OriginalFits.read physical low

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
