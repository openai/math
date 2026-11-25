import OAI.Hierarchy.TaggedWireEarnedQuantities
import OAI.Hierarchy.TaggedWireElectedSource
import OAI.Hierarchy.TaggedWireEarnedTenderAt
import OAI.Hierarchy.ProbeFixedEarnedCross

namespace OAI
/-! # Reading one fixed elected installation at the checkout of another histogram branch -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Strip
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets PurchaseStage ReportSockets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope ChosenPackets ChosenPackets.RowRouting PacketTurns
open scoped Classical Fin.CommRing

namespace CatalogueRows.EarnedInstall
variable {sam : PurchaseSampler} {h d k n w : ℕ} {A B Ball : Type} [Fintype A] [Fintype B] [Fintype Ball]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "K" => siteLast h d k+1
local notation "name" => (siteNumber h d k).toEmbedding
variable {p : StripPorts sam h d k (TreeColumn n) (Fin n) B} {b : Board} {π : Equiv.Perm (Fin (2^h))}
    {extra : A⊕B→DistinctPair (TreeSite n k)} {place : Ball×TreeSite n k↪Fin (siteLast h d k+1)} {u : Ball}
    {endRow : Fin b.rows→Site h d k×Site h d k} {addr : A → Commodity (Fin (2^h)) (Stages h d) k}
    {m : Memory w} {reg : Word w}
    (g : EarnedInstall p b π extra place u endRow (siteNumber h d k).toEmbedding addr m reg)

include g in
omit [Fintype A] [Fintype B] [Fintype Ball] in
theorem named_at (base cut : ℕ) (out : Memory w) (low : PrefixAgreement.Low cut out m)
    (fit : ∀c,(p.column c).Fits w cut)
    (rom : HistoryRoles.RoleROM.Mounted base (SiteDirectory.table h d k) out)
    (room : SiteDirectory.size h d k≤2^w) (cols : Fintype.card (Columns h d)≤2^w) (x : X) :
    (SiteDirectory.cell base h d x.2 (p.column x.1)).eval out reg=((place (u,x)).val:Word w) := by
  rw [g.mapped x]
  apply SiteDirectory.read out rom x.2 (p.column x.1) reg (g.col x.1) room
  rw [PrefixAgreement.expr _ out m cut (PrefixAgreement.inputEnd_of_fits _ (fit x.1)) low reg]
  apply Fin.ext
  exact (g.placed.1 x.1).trans (Fin.val_cast_of_lt (((Fintype.equivFin _) (g.col x.1)).isLt.trans_le cols)).symm
end CatalogueRows.EarnedInstall

namespace FixedProtocolFormat.ElectedSource
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} {v : FixedProtocolFormat F k p q Q σ Λ}
    {h width : ℕ}
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "W" => wordBits h D copies
local notation "days" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "K" => siteLast h D k+1
local notation "fs" => v.nativeFormats P h width
local notation "b" => (P).catalogue
local notation "sig" => (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet
local notation "name" => (siteNumber h D k).toEmbedding
variable {π : Equiv.Perm (Fin (2^h))} {mark : Marks h v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)}
    {ends : Fin (v.widePlacement h width).catalogue.rows → Site h (2^v.W) k × Site h (2^v.W) k} {m : Memory (wordBits h (2^v.W) copies)} {a : Attempt} {i : ℕ}
    (z : v.ElectedSource h width π mark ends m a i) (at₀ : v.widePacketMenuIndex h a)
    (rt : Fin (v.wideBallotParties h a)) (pad : Chord (siteLast h (2^v.W) k+1)) (siteROM : ℕ)
local notation "fd" => v.wideFields P h width siteROM (.attempt a)
local notation "mass" => (fs a).histMass
local notation "R" => z.routing at₀ rt mass pad
local notation "phys" => installedRows π ends name pad

def operands : Operands (fun j=>((R).install.steps (R).order j).length) := by
  cases z with
  | payload ph tr r i row g stock =>
    exact g.operands ((v.wideFields P h width siteROM (.attempt (.outer ph tr))).site ∘ SiteNaming.labels) (v.widePayloadStored P h width ph tr) (v.widePayloadQty P h width ph tr)
  | purchased ph tr sj ti hp ht u path i row g stock =>
    exact g.operands ((v.wideFields P h width siteROM (.attempt (.inner ph tr sj ti))).site ∘ SiteNaming.labels) (v.widePurchaseStored P h width ph tr sj ti) (v.widePurchaseQty P h width ph tr sj ti)

theorem site_at (j : Fin (v.wideBallotParties h a)) (cut : ℕ) (out : Memory W)
    (low : PrefixAgreement.Low cut out m)
    (fits : match a with
      | .outer ph tr => (v.payloadPricePorts P h width).OriginalFits b (v.widePayloadStored P h width ph tr) W cut
      | .inner ph tr sj ti => (v.purchasedPricePorts P h width ph tr).OriginalFits b (v.widePurchaseStored P h width ph tr sj ti) W cut)
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h D k) out)
    (siteRoom : SiteDirectory.size h D k≤2^W) (cols : Fintype.card (Columns h D)≤2^W) :
    ((fd).site j).eval out (i:Word W)=((z.site j).val:Word W) := by
  cases z with
  | payload ph tr r i row g stock =>
    subst i
    exact g.named_at siteROM cut out low fits.column rom siteRoom cols (SiteNaming.labels.symm j)
  | purchased ph tr sj ti hp ht u path i row g stock =>
    subst i
    exact g.named_at siteROM cut out low fits.column rom siteRoom cols (SiteNaming.labels.symm j)

theorem reads (hist : Histogram (Fin (z.placed at₀ rt).data.terms) mass) (out : Memory W) (cut : ℕ)
    (low : PrefixAgreement.Low cut out m)
    (fits : match a with
      | .outer ph tr => (v.payloadPricePorts P h width).OriginalFits b (v.widePayloadStored P h width ph tr) W cut
      | .inner ph tr sj ti => (v.purchasedPricePorts P h width ph tr).OriginalFits b (v.widePurchaseStored P h width ph tr sj ti) W cut)
    (rom : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h D k) out)
    (siteRoom : SiteDirectory.size h D k≤2^W) (cols : Fintype.card (Columns h D)≤2^W) (room : K≤2^W)
    (codes : 1+v.menuCodes N≤2^W) (lanes : (z.placed at₀ rt).data.terms≤ sig)
    (chosen : (((fd).selected rt).eval out (i:Word W)).val=v.widePacketNumber h a at₀)
    (counted : ∀ t:Fin (z.placed at₀ rt).data.terms,
      ((fd).value rt (⟨t.val,t.isLt.trans_le lanes⟩ : Fin sig).succ.succ).eval out (i:Word W)=((hist.val t).val:Word W)) :
    Reads (Installs.starts (source:=(R).source) (R).order) phys ((R).install.steps (R).order)
      (Installs.numbered (R).order ((R).bits hist)) (z.operands at₀ rt pad siteROM) out (i:Word W) := by
  cases z with
  | payload ph tr r i row g stock =>
    subst i
    apply g.tender_reads_at _ _ _ _ _ pad hist _ _ _ out cut low fits.primary fits.stock room
    · intro x
      change (SiteDirectory.cell siteROM h D (SiteNaming.labels.symm (SiteNaming.labels x)).2
        ((v.payloadPricePorts P h width).column (SiteNaming.labels.symm (SiteNaming.labels x)).1)).eval _ _=_
      rw [Equiv.symm_apply_apply]
      exact g.named_at siteROM cut out low fits.column rom siteRoom cols x
    · exact stock
    · intro j
      exact v.widePayloadQty_read P h width ph tr siteROM at₀ out (r.val:Word W) rt hist
        ((Nat.add_le_add_left (Nat.le_max_left ..) 1).trans codes) lanes
        (by simpa only [widePacketNumber,Nat.add_comm 1] using chosen) counted (treeFirst _ _ j)
  | purchased ph tr sj ti hp ht u path i row g stock =>
    subst i
    apply g.tender_reads_at _ _ _ _ _ pad hist _ _ _ out cut low fits.primary fits.stock room
    · intro x
      change (SiteDirectory.cell siteROM h D (SiteNaming.labels.symm (SiteNaming.labels x)).2
        ((v.purchasedPricePorts P h width ph tr).column (SiteNaming.labels.symm (SiteNaming.labels x)).1)).eval _ _=_
      rw [Equiv.symm_apply_apply]
      exact g.named_at siteROM cut out low fits.column rom siteRoom cols x
    · exact stock
    · intro j
      exact v.widePurchaseQty_read P h width ph tr sj ti siteROM at₀ out ((BoughtLocation.relative path).val:Word W) rt hist
        ((Nat.add_le_add_left (Nat.le_max_right ..) 1).trans codes) lanes
        (by simpa only [widePacketNumber,Nat.add_comm 1] using chosen) counted (treeFirst _ _ j)

end FixedProtocolFormat.ElectedSource
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
