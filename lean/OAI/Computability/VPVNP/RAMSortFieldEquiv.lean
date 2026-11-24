import OAI.Computability.VPVNP.RAMSortFieldIndex

/-!
# Identifying distributed sort transcripts with physical send fields

The chronological list of layer checks uses a dependent product of field
assignments. This product indexes exactly the sorting send fields allocated
by the physical layout, once at each cross-site layer and site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

variable {h d : ℕ} {α : Type*}

private def bundle : (ss : List (Stage (h+d))) →
    (∀ s ∈ ss, Sends h d s α) → Fields h d α ss
  | [], _ => PUnit.unit
  | s :: ss, f => (f s (List.mem_cons_self ..),
      bundle ss (fun t ht ↦ f t (List.mem_cons_of_mem _ ht)))

private def lookup : (ss : List (Stage (h+d))) → Fields h d α ss →
    (∀ s ∈ ss, Sends h d s α)
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | s :: ss, fields, t, ht =>
    if he : s = t then he ▸ fields.1
    else lookup ss fields.2 t ((List.mem_cons.mp ht).resolve_left (Ne.symm he))

private theorem lookup_bundle (ss : List (Stage (h+d)))
    (f : ∀ s ∈ ss, Sends h d s α) : lookup ss (bundle ss f) = f := by
  induction ss with
  | nil => funext s hs; exact False.elim (List.not_mem_nil hs)
  | cons s ss ih =>
    funext t ht
    by_cases he : s = t
    · subst t; simp [lookup, bundle]
    · simp only [lookup, bundle, dite_eq_right he]
      rw [ih]

private theorem bundle_lookup (ss : List (Stage (h+d))) (hn : ss.Nodup)
    (fields : Fields h d α ss) : bundle ss (lookup ss fields) = fields := by
  induction ss with
  | nil => cases fields; rfl
  | cons s ss ih =>
    have hs := List.nodup_cons.mp hn
    rcases fields with ⟨f, fs⟩
    apply Prod.ext
    · simp [bundle, lookup]
    · change bundle ss (fun t ht ↦ lookup (s :: ss) (f, fs) t _) = fs
      have he : (fun t ht ↦ lookup (s :: ss) (f, fs) t (List.mem_cons_of_mem s ht)) =
          lookup ss fs := by
        funext t ht
        have hne : s ≠ t := fun e ↦ hs.1 (e ▸ ht)
        simp [lookup, hne]
      rw [he, ih hs.2]

/-- A duplicate-free schedule stores its indexed fields once each. -/
def fieldsOfStages (ss : List (Stage (h+d))) (hn : ss.Nodup) :
    (∀ s ∈ ss, Sends h d s α) ≃ Fields h d α ss where
  toFun := bundle ss
  invFun := lookup ss
  left_inv := lookup_bundle ss
  right_inv := bundle_lookup ss hn

/-- Reindex the sorting fields by their physical layer and source site. -/
private def physicalIndex (h d : ℕ) (α : Type*) :
    (RAMLayout.Layer d → Fin (2 ^ d) → Wires h α) ≃ (∀ s : Stage (h+d), Sends h d s α) where
  toFun fields s hc := fields ((crossStageEquiv h d).symm ⟨s, hc⟩)
  invFun fields l := fields ((crossStageEquiv h d) l).val ((crossStageEquiv h d) l).property
  left_inv fields := by funext l; simp
  right_inv fields := by
    funext s hc
    exact congrArg (fun z : {s : Stage (h+d) // h ≤ s.stride} ↦ fields z.val z.property)
      ((crossStageEquiv h d).apply_symm_apply ⟨s, hc⟩)

private def restrictIndex (ss : List (Stage (h+d))) (hall : ∀ s, s ∈ ss) :
    (∀ s : Stage (h+d), Sends h d s α) ≃ (∀ s ∈ ss, Sends h d s α) where
  toFun f s _ := f s
  invFun f s := f s (hall s)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Bijection with the send blocks allocated in the paper's equation (10.1). -/
def physicalFieldsEquiv (h d : ℕ) (α : Type*) :
    (RAMLayout.Layer d → Fin (2 ^ d) → Wires h α) ≃
      Fields h d α (phases (h+d) (h+d) le_rfl) :=
  (physicalIndex h d α).trans ((restrictIndex _ mem_fullPhases).trans
    (fieldsOfStages _ (phases_nodup le_rfl)))

/-- Every physical sorting send slot is constrained by the local validator.
For any initial record array exactly one physical send assignment passes. -/
theorem existsUnique_physicalFields [LinearOrder α] (h d : ℕ) (x : ℕ → α) :
    ∃! send : RAMLayout.Layer d → Fin (2 ^ d) → Wires h α, ∀ v,
      checks v _ (physicalFieldsEquiv h d α send) (block h v.val x) := by
  let e := physicalFieldsEquiv h d α
  let ss := phases (h+d) (h+d) le_rfl
  refine ⟨e.symm (actual ss x), ?_, ?_⟩
  · change ∀ v, checks v ss (e (e.symm (actual ss x))) (block h v.val x)
    rw [e.apply_symm_apply]
    exact checks_actual ss x
  · intro send hc
    apply e.injective
    rw [e.apply_symm_apply]
    exact fields_eq_actual ss _ x hc

end RAMSort

end VPVNP
end Computability
end OAI
