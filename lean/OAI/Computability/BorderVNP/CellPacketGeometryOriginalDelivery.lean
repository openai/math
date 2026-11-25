import OAI.Computability.BorderVNP.CellPacketGeometryOriginalRoster
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryCells
import OAI.Computability.BorderVNP.PackedOriginalDescriptionRows

/-! # Authentic input-entry addresses for the real cells of the history geometry

Every opaque box occurrence in a real cell has its own original transmission
index. Its destination is the final cell of the retained original host. Both the
injection and this destination equality follow from the selected box roster.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open CellSparse Packet Packing.Inherited FrozenTape SiteWords LiveWords

variable {a C cap d t entries : ℕ} {R B U V E : Type}
variable (S : Schema R B) (L : Schema U V) (entry : Fin entries ↪ Fin a) (known : Fin a → List (List Factor))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
variable (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)

local notation3 "G₀" => directory S L (originalBoxes entry known) sh lh priv rep args x y cells off box

/-- Real cell/opaque-box positions, omitting the extra slot used for inactive history rows. -/
abbrev RealOccurrence {n C entries : ℕ} (G : Directory (Fin n) (Fin entries) (C+1)) :=
  Σ c : Fin C, Fin ((G.cellBoxes c.castSucc).filterMap Sum.getRight?).length

/-- Recover the original input row directly from the stable ordinal of the cell's
opaque box. Distinct positions of all real cells have distinct input rows. -/
noncomputable def originalDelivery : RealOccurrence (G₀) ↪ Fin entries :=
  (Fin.castSuccEmb.sigmaMap (fun c => Function.Embedding.refl
    (Fin (((G₀).cellBoxes c.castSucc).filterMap Sum.getRight?).length))).trans
      ((G₀).deliveryEmbedding (original_once S L entry known sh lh priv rep args x y cells off box))

local notation3 "sendRow" => originalDelivery S L entry known sh lh priv rep args x y cells off box

/-- The delivered row number is the private original name at this exact local
position of the actual native box table. -/
theorem originalDelivery_get (z : RealOccurrence (G₀)) :
    sendRow z = (((G₀).cellBoxes z.1.castSucc).filterMap Sum.getRight?).get z.2 :=
  congrArg Prod.snd ((G₀).originalIndex_get ⟨z.1.castSucc,z.2⟩)

/-- Exactly the original entries hosted by this real cell are selected from its
typed box table, including when its other sites carry arbitrary known boxes. -/
theorem originalDelivery_mem (c : Fin C) (j : Fin entries) :
    j ∈ (((G₀).cellBoxes c.castSucc).filterMap Sum.getRight?) ↔ cells (entry j)=c := by
  rw [cell_boxes S L (originalBoxes entry known) sh lh priv rep args x y cells off box c,List.filterMap_flatMap]
  simp only [List.mem_flatMap,originalBoxes_private,Option.mem_toList,owned,List.mem_filter,
    List.mem_finRange,true_and,decide_eq_true_eq]
  constructor
  · rintro ⟨host,selected,source⟩
    exact ((entry.injective.isPartialInv j host).mp source) ▸ selected
  · intro selected
    exact ⟨entry j,selected,Function.partialInv_left entry.injective j⟩

/-- The opaque transmission row's genuine retained host is in its receiver cell. -/
theorem originalDelivery_receiver (z : RealOccurrence (G₀)) : cells (entry (sendRow z)) = z.1 := by
  rw [originalDelivery_get]
  exact (originalDelivery_mem S L entry known sh lh priv rep args x y cells off box z.1 _).mp (List.get_mem ..)

/-- Every original input entry occurs at one of the real receiving cells. -/
theorem originalDelivery_surjective : Function.Surjective sendRow := by
  intro j
  let c := cells (entry j)
  have mem := (originalDelivery_mem S L entry known sh lh priv rep args x y cells off box c j).mpr rfl
  obtain ⟨n,hn,hj⟩ := List.getElem_of_mem mem
  exact ⟨⟨c,⟨n,hn⟩⟩,(originalDelivery_get S L entry known sh lh priv rep args x y cells off box _).trans hj⟩

end CellPacketGeometry.History

namespace Diagonal.ExternalSew

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Adaptive PublicCapacity PhysicalEpochs
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open CellSparse CellPacketGeometry.History
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {shape : ℕ → Shape}
    {W : ℕ → Type} [∀ t, Fintype (W t)] {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)]
    {w : ℕ → ℕ → ℕ} {good : ∀ t, EnrichedOuter.State S start P bits shape W t → Prop}
    {deep : S.floor+1+S.drop*T ≤ start} (M : EnrichedOuter.Machine.{_,u} deep good V w) (bottom : Admissible good 0)
    (q : (packHistory bottom M.epoch T).Index) (dir : Directory.Layout) (count : dir.entries = (fan S)^T*dir.sites)
    (order : Fin dir.sites ≃ bottom.val.pack.layout.Site)

local notation3 "lastState" => ((packHistory bottom M.epoch T).term q).val
local notation3 "original" => originalDescriptionRows M bottom q dir count order

/-- The specific chronological real-cell injection uses the row-major original
bundle/tile directory and the final sparse site numbering of the named execution.
The receiver and the description-payload charge refer to the same retained vertex. -/
theorem originalDescription_delivery {C cap d t : ℕ} {R B U J E : Type}
    (F : Inherited.FrozenTape.Schema R B) (L : Inherited.FrozenTape.Schema U J)
    (known : Fin (shape T).sites → List (List Factor))
    (sh : ∀ r, (F.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
    (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
    (x : Inherited.FrozenTape.Pins R B d → Bool) (y : Inherited.FrozenTape.Pins U J t → Bool)
    (cells : Fin (shape T).sites → Fin C) (off box : Fin (shape T).sites → ℕ)
    (base : RecordData bottom.val.pack.layout) (room : ∀ v, dir.description ≤ base.payload v) :
    let entry := (original).trans (lastState).rows.site
    let G := directory F L (originalBoxes entry known) sh lh priv rep args x y cells off box
    let rows := originalDelivery F L entry known sh lh priv rep args x y cells off box
    ∀ z : RealOccurrence G, cells ((lastState).rows.site (original (rows z))) = z.1 ∧
      dir.description ≤ (M.historyFields bottom base T q).payload (original (rows z)) := by
  intro entry G rows z
  exact ⟨originalDelivery_receiver F L entry known sh lh priv rep args x y cells off box z,
    originalDescriptionRows_payload M bottom q dir count order base room (rows z)⟩

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
