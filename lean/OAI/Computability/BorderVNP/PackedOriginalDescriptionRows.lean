import OAI.Computability.BorderVNP.PackedEnrichedOriginalPayload
import OAI.Computability.BorderVNP.PackedDirectoryIncoming

/-! # Row-major original description entries and their final physical payload

A private description has one public row for every pair of a bottom bundle
and an original tile. Euclidean quotient and remainder identify that pair.
Its terminal vertex is the actual retained host of the named execution.
Consequently the full padded description length is paid at this very vertex.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Adaptive PublicCapacity PhysicalEpochs
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

/-- The row-major description numbering of the original bundle/site array. -/
def descriptionOrder {D : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} (bottom : Pack D P bits K)
    (bundles sites entries : ℕ) (count : entries = bundles*sites) (order : Fin sites ≃ bottom.layout.Site) :
    Fin entries ≃ (parallelPacks fun _ : Fin bundles => bottom).layout.Site :=
  (finCongr count).trans (finProdFinEquiv.symm.trans
    (((Equiv.refl (Fin bundles)).prodCongr order).trans (Equiv.sigmaEquivProd (Fin bundles) bottom.layout.Site).symm))

/-- Quotient selects the bottom bundle; remainder selects its actual public
site number. -/
theorem descriptionOrder_coordinates {D : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} (bottom : Pack D P bits K)
    {bundles sites entries : ℕ} (count : entries = bundles*sites) (order : Fin sites ≃ bottom.layout.Site)
    (j : Fin entries) :
    let a := descriptionOrder bottom bundles sites entries count order j
    (a.1.val,(order.symm a.2).val) = (j.val/sites,j.val%sites) := by
  let a : Fin bundles × Fin sites := finProdFinEquiv.symm ((finCongr count) j)
  change (a.1.val,(order.symm (order a.2)).val) = _
  rw [order.symm_apply_apply]
  rfl

universe u
variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)]
    {w : ℕ → ℕ → ℕ} {good : ∀ t, EnrichedOuter.State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} (M : EnrichedOuter.Machine.{_,u} deep good V w) (bottom : Admissible good 0)
    (q : (packHistory bottom M.epoch T).Index)

/-- The physical receiving vertex of every real private description in the
native delivery directory. Distinct rows have distinct retained vertices. -/
noncomputable def originalDescriptionRows (dir : Directory.Layout) (count : dir.entries = (fan S)^T*dir.sites)
    (order : Fin dir.sites ≃ bottom.val.pack.layout.Site) :
    Fin dir.entries ↪ (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout.Site :=
  (descriptionOrder bottom.val.pack ((fan S)^T) dir.sites dir.entries count order).toEmbedding.trans
    (enrichedOuterHosts M bottom q).site

/-- The description-size hypothesis needed by the physical incoming-lane
bound, for the real row-major directory on this selected named history. -/
theorem originalDescriptionRows_payload (dir : Directory.Layout) (count : dir.entries = (fan S)^T*dir.sites)
    (order : Fin dir.sites ≃ bottom.val.pack.layout.Site) (base : RecordData bottom.val.pack.layout)
    (startBound : ∀ v, dir.description ≤ base.payload v) (j : Fin dir.entries) :
    dir.description ≤ (M.historyFields bottom base T q).payload
      (originalDescriptionRows M bottom q dir count order j) := by
  let a := descriptionOrder bottom.val.pack ((fan S)^T) dir.sites dir.entries count order j
  have h := congrArg Prod.snd (enrichedOriginal_fields M bottom base q a.1 a.2)
  exact (startBound a.2).trans h.ge

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
