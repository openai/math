import OAI.Hierarchy.ProbeFixedPrintedOperands
import OAI.Hierarchy.ProbeFixedFailureWords

namespace OAI
/-! # Record and catalogue words used by a paid strip's physical geometry decoder -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory
open CatalogueRows PurchaseStage
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "rowFormats" => v.nativeFormats P z width
local notation "bh" => StripChart.header F (v.nativeBoards P z width)
local notation "g" => v.stamp P z width r banks src tab dst owners

section
variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
local notation "pre" => (guard C ev).apply entry
local notation "post" => postOutput ((C).layout ev) (repair C ev) (prepared C ev entry)

structure PayloadRepairGeometry where
  headBefore : (bh ev).stop≤(g ev).out
  room : P.catalogue.rows<2^W
  order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k
  loaded : CoreLookup.Loaded P.routes.core order post
  codes : ∀f,P.catalogue.core.lengthCode.eval post ((order.symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W)
  fits : ∀f : Edges v.sampler z (2^v.W) k,coreCode v.sampler v.radius f<2^W
  faces : ∀row : Fin (rowFormats ev).market.rows,(rowFormats ev).market.failures.live.eval pre (row.val:Word W)≠0 →
    ∃ global : PayloadStrip.Columns N → Columns z (2^v.W),
      (∀c,(((v.payloadPricePorts P z width).column c).eval post (row.val:Word W)).val=((Fintype.equivFin _) (global c)).val) ∧
      (∀e l,∃f : Edges v.sampler z (2^v.W) k,
        ((v.payloadPricePorts P z width).horizontal e l).eval post (row.val:Word W)=((order.symm f).val:Word W) ∧
        (coreCode v.sampler v.radius f:ℝ)=PayloadStrip.length N e)
end

section
variable (phase trial slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase trial slice inner
local notation "pre" => (guard C ev).apply entry
local notation "post" => postOutput ((C).layout ev) (repair C ev) (prepared C ev entry)

structure PurchasedRepairGeometry where
  headBefore : (bh ev).stop≤(g ev).out
  room : P.catalogue.rows<2^W
  order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k
  loaded : CoreLookup.Loaded P.routes.core order post
  codes : ∀f,P.catalogue.core.lengthCode.eval post ((order.symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W)
  fits : ∀f : Edges v.sampler z (2^v.W) k,coreCode v.sampler v.radius f<2^W
  faces : ∀row : Fin (rowFormats ev).market.rows,(rowFormats ev).market.failures.live.eval pre (row.val:Word W)≠0 →
    ∃ global : ChainStrip.Columns v.depth → Columns z (2^v.W),
      (∀c,(((v.purchasedPricePorts P z width phase trial).column c).eval post (row.val:Word W)).val=((Fintype.equivFin _) (global c)).val) ∧
      (∀e l,∃f : Edges v.sampler z (2^v.W) k,
        ((v.purchasedPricePorts P z width phase trial).horizontal e l).eval post (row.val:Word W)=((order.symm f).val:Word W) ∧
        (coreCode v.sampler v.radius f:ℝ)=ChainStrip.length v.depth e) ∧
      P.catalogue.coreRows≤(((v.purchasedPricePorts P z width phase trial).probe ()).eval post (row.val:Word W)).val
end

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
