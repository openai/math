import OAI.Computability.VPVNP.ShrinkFieldBounds
import OAI.Computability.VPVNP.CompressionHistory
import OAI.Computability.VPVNP.PackingPreimages

/-!
# Resident map and field occurrences for shrinking histories

At a new site of §7.2 the four absorbed types contribute shared local
fields. The six-party maps resident there have their own incident demand
and supply words. Each map's degree is bounded by its number of base
copies. These records accompany the old and new actual slots of the
substep in the recursive histories of Theorem 7.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

open NetworkKernel WireTensor MotifGrid MotifBlocks MotifConversion ShrinkMotif
open SurvivingSlots

variable {V H Tag L : Type} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c) (number : P.BundleNumbering) (w : Arc V H Tag L d c → ℕ)
variable {k : Type*} [Field k] {H' : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) H')
variable (sel : ∀ m, P.ShrinkChoice number w B m) (l : Bool) (s : (V × Tag) × L)

/-- Distinct occurrences of the six local matrix entries assigned to a site. -/
abbrev ResidentMap := {z : P.Motif × Fin 6 // P.shrinkPartySite l z.1 z.2 = s}

/-- A matrix argument at party `j` reads the half-word of each incident
demand and supply edge. -/
def readsArgument (j : Fin 6) : Bool ⊕ Bool × Fin 4 → Prop
  | .inl e => demandSource e = j ∨ demandTarget e = j
  | .inr e => supply.src e = j ∨ supply.dst e = j

instance (j : Fin 6) (e : Bool ⊕ Bool × Fin 4) : Decidable (readsArgument j e) := by
  cases e <;> unfold readsArgument <;> infer_instance

/-- Map argument occurrences retain both their resident map and edge label. -/
abbrev ResidentArgument := {z : P.ResidentMap l s × (Bool ⊕ Bool × Fin 4) //
  readsArgument z.1.1.2 z.2}

/-- The locally summed fields and local matrix arguments at each new site.
The bounds assigned to each map are the lengths of the conversion entry
descriptions, before parameter specialization. -/
noncomputable def shrinkSiteRecords : SiteRecords where
  Field := {e : P.Motif × Fin 4 // P.shrinkInternalOwner l e = s} ⊕ P.ResidentArgument l s
  fieldFintype := inferInstance
  width
    | .inl e => P.shrinkSupplyWidths number w B e.1.1 (sel e.1.1) (!l,e.1.2)
    | .inr z => match z.1.2 with
      | .inl e => P.shrinkDemandWidths number w z.1.1.1.1 e
      | .inr e => P.shrinkSupplyWidths number w B z.1.1.1.1 (sel z.1.1.1.1) e
  Map := P.ResidentMap l s
  mapFintype := inferInstance
  degree z := repetitions B (P.shrinkDemandWidths number w z.1.1)

/-- A site has `6dQ` local maps, `4dQ` absorbed fields, and at most ten
argument fields per resident map. -/
theorem shrinkSiteRecords_count_le (hc : 2 ≤ c) :
    (P.shrinkSiteRecords number w B sel l s).count ≤
      1 + 6 * (d * pieceCount d c) + 4 * (d * pieceCount d c) + 6 * (d * pieceCount d c) * 10 := by
  let M := P.ResidentMap l s
  have hM : Fintype.card M = 6 * (d * pieceCount d c) := P.card_shrinkPartySite hc l s
  have hA : Fintype.card (P.ResidentArgument l s) ≤ Fintype.card (M × (Bool ⊕ Bool × Fin 4)) :=
    Fintype.card_subtype_le _
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool, hM] at hA
  change 1 + Fintype.card M +
    Fintype.card ({e : P.Motif × Fin 4 // P.shrinkInternalOwner l e = s} ⊕
      P.ResidentArgument l s) ≤ _
  rw [hM, Fintype.card_sum, P.card_shrinkInternalOwner hc]
  omega

set_option maxHeartbeats 400000 in
-- The two maxima unfold the dependent field and map types of the selected record.
/-- Every local wire word and every individual map degree obey the same
linear envelope, independent of the particular selections and site. -/
theorem shrinkSiteRecords_largest_le (hc : 2 ≤ c) (hd : 0 < d) {W : ℕ} (hw : ∀ a, w a ≤ W) :
    (P.shrinkSiteRecords number w B sel l s).largest ≤ max 1 (fieldFactor B) * (W + 1) := by
  let K := max 1 (fieldFactor B) * (W + 1)
  have hf : fieldFactor B * (W + 1) ≤ K := Nat.mul_le_mul_right _ (le_max_right ..)
  have hW : W ≤ K := (Nat.le_succ W).trans
    (by simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right (W + 1) (le_max_left 1 (fieldFactor B)))
  change max (Finset.univ.sup (P.shrinkSiteRecords number w B sel l s).width)
    (Finset.univ.sup (fun z : P.ResidentMap l s ↦
      repetitions B (P.shrinkDemandWidths number w z.1.1))) ≤ K
  apply max_le <;> apply Finset.sup_le <;> intro z _
  · rcases z with e | z
    · exact ((P.shrinkTerm_bounds hc hd number w hw B e.1.1 (sel e.1.1)).2 (!l,e.1.2)).2.trans hf
    · rcases z with ⟨⟨m,e | e⟩,he⟩
      · exact (P.shrinkDemandWidths_le hc hd number w hw m.1.1 e).trans hW
      · exact ((P.shrinkTerm_bounds hc hd number w hw B m.1.1 (sel m.1.1)).2 e).2.trans hf
  · exact (P.shrinkTerm_bounds hc hd number w hw B z.1.1 (sel z.1.1)).1.trans hf

omit [AddCommGroup H] [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
  [DecidableEq V] [DecidableEq Tag] [DecidableEq L] in
/-- Reassembling the old lane fields and promoting the tag into the new
base both preserve the exact immediate-preimage count. -/
theorem card_reindexed_shrinkPlace [Finite V] [Finite H] [Finite Tag] [Finite L]
    {U : Type}
    (inputSites : Position V H Tag L c ≃ U) (hc : 0 < c) :
    Nat.card {u : U // s = P.shrinkPlace l (inputSites.symm u)} = 2 ^ c * d := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite H
  let := Fintype.ofFinite Tag
  let := Fintype.ofFinite L
  let e := inputSites.symm.subtypeEquiv
    (p := fun u ↦ s = P.shrinkPlace l (inputSites.symm u))
    (q := fun x ↦ P.placement l x = packedSiteEquiv.symm s)
    (fun u ↦ by rw [Equiv.eq_symm_apply]; exact eq_comm)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact P.card_placement hc l _

end Compression.PackingData

end VPVNP
end Computability
end OAI
