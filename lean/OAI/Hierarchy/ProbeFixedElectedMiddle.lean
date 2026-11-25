import OAI.Hierarchy.TaggedWireElectedOperands
import OAI.Hierarchy.ProbeFixedWidePacketMiddle

namespace OAI
/-! # Intermediate columns of the actually selected native strip -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.PacketTurns.Operands
open ProtocolRAM
variable {n : ℕ} {left right : Fin n → ℕ} (a : Operands left) (b : Operands right)

/-- Middle records access source endpoint and width words, even when the
physical traversal stores its one- and two-hop shapes at different types. -/
theorem middleFields_congr (old : a.oldSite=b.oldSite) (width : a.width=b.width)
    (M : ℕ) (party : Expr) : a.middleFields M party=b.middleFields M party := by
  have sums (i : Fin n) (t : ℕ) : a.middleSum i t=b.middleSum i t := by
    induction t with
    | zero => rfl
    | succ t ih => simp only [middleSum, ih, sameChord, old, width]
  have cells : a.middleColsAt party=b.middleColsAt party := by
    funext f
    rcases f with ⟨i,f⟩ | ⟨⟨i,x⟩,⟨j,y⟩⟩
    · obtain ⟨j,h⟩:=f
      interval_cases j <;> simp only [middleColsAt, atParty, sums, old, width]
    · simp only [middleColsAt, atParty, sameChord, old, width]
  simp only [middleFields, cells]
end Hierarchy.WireTelescope.PacketTurns.Operands
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Strip
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets PurchaseStage ReportSockets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope ChosenPackets ChosenPackets.RowRouting PacketTurns
open scoped Classical Fin.CommRing

namespace CatalogueRows.EarnedInstall
open StripPaths

set_option maxHeartbeats 1200000 in
private theorem numbered_middle {sam : PurchaseSampler} {h d k n K w J : ℕ}
    {A B Ball : Type} [Fintype A] [Fintype B] [Fintype Ball]
    {ports : StripPorts sam h d k (TreeColumn n) (Fin n) B} {board : Board}
    {π : Equiv.Perm (Fin (2^h))} {extra : A⊕B → DistinctPair (TreeSite n k)}
    {place : Ball×TreeSite n k ↪ Fin K} {ball : Ball}
    {ends : Fin board.rows → Site h d k × Site h d k} {name : Site h d k ↪ Fin K}
    {addr : A → Commodity (Fin (2^h)) (Stages h d) k} {m : Memory w} {reg : Word w}
    (installed : EarnedInstall ports board π extra place ball ends name addr m reg)
    (labels : TreeSite n k ≃ Fin J) (site : Fin J → Expr) (stock : A → Expr)
    (qty : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k ⊕ TreeLink n k → Expr)
    (M : ℕ) (party : Fin J) :
    ports.catalogueMiddle extra board (Fintype.card (Commodity (Fin (2^h)) (Stages h d) k))
        (site ∘ labels) stock qty M (labels.symm party) =
      (installed.operands (site ∘ labels) stock qty).middleFields M (site party) := by
  let shift := Fintype.card (Commodity (Fin (2^h)) (Stages h d) k)
  let menu := menuInputs extra (treeFirst _ _) (site ∘ labels)
    (readPrimary stock shift (ports.primary board)) (emitterMate (A:=A) ports board shift)
    (emitterTree (A:=A) ports board shift) qty
  have sameSite : (site ∘ labels) (labels.symm party) = site party :=
    congrArg site (labels.apply_symm_apply party)
  exact (congrArg (menu.middleFields M) sameSite).trans
    (Operands.middleFields_congr menu (installed.operands (site ∘ labels) stock qty)
      rfl rfl M (site party))

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
variable {π : Equiv.Perm (Fin (2^h))}
    {mark : Marks h v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)}
    {ends : Fin (v.widePlacement h width).catalogue.rows → Site h (2^v.W) k × Site h (2^v.W) k}
    {m : Memory (wordBits h (2^v.W) copies)} {a : Attempt} {i : ℕ}
    (z : v.ElectedSource h width π mark ends m a i) (at₀ : v.widePacketMenuIndex h a)
    (rt : Fin (v.wideBallotParties h a)) (pad : Chord (siteLast h (2^v.W) k+1)) (siteROM : ℕ)
local notation "fd" => v.wideFields P h width siteROM (.attempt a)
local notation "mass" => (fs a).histMass
local notation "R" => z.routing at₀ rt mass pad
local notation "phys" => installedRows π ends name pad
attribute [local irreducible] StripPorts.catalogueMiddle CatalogueRows.EarnedInstall.operands
  Operands.middleFields wideBallotSite

set_option maxHeartbeats 1200000 in
theorem middle_column (party : Fin (v.wideBallotParties h a)) :
    v.widePacketMiddle h width a siteROM party =
      (z.operands at₀ rt pad siteROM).middleFields (v.widePacketRoles h) ((fd).site party) := by
  cases z with
  | payload ph tr r i row g stock =>
    exact CatalogueRows.EarnedInstall.numbered_middle g SiteNaming.labels
      (v.wideBallotSite P h width siteROM (.outer ph tr))
      (v.widePayloadStored P h width ph tr) (v.widePayloadQty P h width ph tr)
      (v.widePacketRoles h) party
  | purchased ph tr sj ti hp ht u path i row g stock =>
    exact CatalogueRows.EarnedInstall.numbered_middle g SiteNaming.labels
      (v.wideBallotSite P h width siteROM (.inner ph tr sj ti))
      (v.widePurchaseStored P h width ph tr sj ti) (v.widePurchaseQty P h width ph tr sj ti)
      (v.widePacketRoles h) party


end FixedProtocolFormat.ElectedSource
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
