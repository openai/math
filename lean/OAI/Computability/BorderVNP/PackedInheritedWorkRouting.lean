import OAI.Computability.BorderVNP.PackedInheritedWorkWords

/-! # Routing previous extents and birth words to their permanent site rows

The full old rectangle is reused verbatim. The new part contains one template
per public seed name. Vacant seed slots read a common zero gate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Shortening.StaticRows ParseBatchSort VPVNP.VerifierNetwork BankJoint
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private zero zero_size false_word from OAI.Computability.BorderVNP.PackedBankInstall
open scoped Classical

variable {σ B : Type*} {A : Type} [Fintype σ] [Fintype A] [Fintype B] {s n w : ℕ}

/-- Pad a publicly named source table to its full rectangle. Every missing
row uses the same zero gate, independently of its number of pins. -/
noncomputable def pad (name : A ↪ Fin n) (f : Frame σ (A × B)) : Frame σ (Fin n × B) :=
  (parallelFrame f zero).select fun z =>
    if h : z.1 ∈ Set.range name then .inl (h.choose,z.2) else .inr ()

theorem pad_size (name : A ↪ Fin n) (f : Frame σ (A × B)) : (pad name f).size ≤ f.size+1 := by
  simpa [pad] using Nat.add_le_add_left (zero_size (σ := σ)) f.size

theorem pad_live (name : A ↪ Fin n) (f : Frame σ (A × B)) (x : σ → Bool) (a : A) (j : B) :
    (pad name f).eval x (name a,j) = f.eval x (a,j) := by
  have h : name a ∈ Set.range name := ⟨a,rfl⟩
  simp only [pad,Frame.select_eval,dite_eq_left h,parallelFrame_eval_inl,name.injective h.choose_spec]

theorem pad_hole (name : A ↪ Fin n) (f : Frame σ (A × B)) (x : σ → Bool) (i : Fin n)
    (hi : i ∉ Set.range name) (j : B) : (pad name f).eval x (i,j) = false := by
  simp only [pad,Frame.select_eval,dite_eq_right hi,parallelFrame_eval_inr,zero,Frame.step_eval,StatementCircuit.Expr.eval]

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable (seed : A ↪ Fin n) (old : Frame σ (Fin s × Fin w))
variable (birth : Frame σ ((A × TemplateSite e) × Fin w))

private noncomputable def seeded := pad seed (birth.select fun z : A × TemplateSite e × Fin w => ((z.1,z.2.1),z.2.2))

/-- Concatenate the old extents and the actual birth work in precisely the
same row order as the physical sewn network. -/
noncomputable def route : Frame σ (Fin (siteCapacity e s n) × Fin w) :=
  (parallelFrame old (seeded e seed birth)).select fun z =>
    match finSumFinEquiv.symm z.1 with
    | .inl i => .inl (i,z.2)
    | .inr r =>
      let h := finProdFinEquiv.symm r
      .inr (h.1,(Fintype.equivFin (TemplateSite e)).symm h.2,z.2)

theorem route_size : (route e seed old birth).size ≤ old.size+birth.size+1 := by
  have h := pad_size seed (birth.select fun z : A × TemplateSite e × Fin w => ((z.1,z.2.1),z.2.2))
  simp only [Frame.select_size] at h
  simp only [route,Frame.select_size,parallelFrame_size,seeded]
  omega

theorem route_old (x : σ → Bool) (v : Fin s) (j : Fin w) :
    (route e seed old birth).eval x (finSumFinEquiv (.inl v),j) = old.eval x (v,j) := by
  simp [route]

theorem route_birth (x : σ → Bool) (a : A) (v : TemplateSite e) (j : Fin w) :
    (route e seed old birth).eval x (siteSlot e s (seed a) v,j) = birth.eval x ((a,v),j) := by
  simp only [route,siteSlot,Frame.select_eval,Equiv.symm_apply_apply,parallelFrame_eval_inr,seeded,pad_live]

/-- For any sparse set of old sites, the routed words cover the same live
rows as the physical site names. -/
theorem route_covers {P : Type} {bits : P → ℕ} (p : Pack D P bits K) (siteID : p.layout.Site ↪ Fin s)
    (x : σ → Bool) (prev : p.layout.Site → ℕ) (fresh : A → TemplateSite e → ℕ)
    (hp : Covers siteID prev old x)
    (hf : ∀ a v, value (fun j => birth.eval x ((a,v),j)) = fresh a v) :
    Covers (siteRows e p siteID seed) (Sum.elim prev fun z => fresh z.1 z.2) (route e seed old birth) x := by
  constructor
  · rintro (v | ⟨a,v⟩)
    · change value (fun j => (route e seed old birth).eval x (finSumFinEquiv (.inl (siteID v)),j)) = prev v
      simpa only [route_old] using hp.live v
    · change value (fun j => (route e seed old birth).eval x (siteSlot e s (seed a) v,j)) = fresh a v
      simpa only [route_birth] using hf a v
  · intro i hi
    obtain ⟨u,rfl⟩ := finSumFinEquiv.surjective i
    cases u with
    | inl i =>
      have hv : i ∉ Set.range siteID := by rintro ⟨v,rfl⟩; exact hi ⟨.inl v,rfl⟩
      simpa only [route_old] using hp.hole i hv
    | inr r =>
      obtain ⟨⟨a,k⟩,rfl⟩ := finProdFinEquiv.surjective r
      obtain ⟨v,rfl⟩ := (Fintype.equivFin (TemplateSite e)).surjective k
      have ha : a ∉ Set.range seed := by rintro ⟨b,rfl⟩; exact hi ⟨.inr ⟨b,v⟩,rfl⟩
      simpa only [route,Frame.select_eval,Equiv.symm_apply_apply,parallelFrame_eval_inr,seeded,
        pad_hole _ _ _ _ ha] using false_word (w := w)

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
