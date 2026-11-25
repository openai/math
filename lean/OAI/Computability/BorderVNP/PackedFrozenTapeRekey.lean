import OAI.Computability.BorderVNP.PackedFrozenTapeRows

/-! # Translation of the frozen rows to a successor site directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {R B V T : Type*} {d d' n : ℕ} (S : Schema R B)

/-- An immutable block contributes an ordered sequence of marked records at each real site.
Its row order and relocation fields remain visible before the block is appended. -/
structure Schema.Block (x : Pins R B d → Bool) (key : V → ℕ) (records : V → List (List (Kind × ℕ))) : Prop where
  /-- Every enabled physical row is owned by a real site. -/
  owners : ∀ r ∈ S.rows, x (.inl (r,.inl ())) = true → ∃ v, owner x r = key v
  /-- A stable scan gives every individual record, in the order of its marked fields. -/
  atSite : ∀ v, S.atSite x (key v) = records v

variable {x : Pins R B d → Bool} {key : V → ℕ} {records : V → List (List (Kind × ℕ))}

/-- Keys outside the true site's image have no record, including keys in unused rectangle slots. -/
theorem Schema.Block.fresh (h : S.Block x key records) (a : ℕ) (outside : ∀ v, key v ≠ a) :
    S.atSite x a = [] := by
  rw [Schema.atSite,List.filterMap_eq_nil_iff]
  intro r hr
  by_cases enabled : x (.inl (r,.inl ())) = true
  · obtain ⟨v,hv⟩ := h.owners r hr enabled
    simp [enabled,hv,outside]
  · simp [enabled]

variable [Fintype R] [Fintype B] (old : Fin n ↪ Fin (2^d)) (new : Fin n ↪ Fin (2^d'))

private noncomputable def keys : Frame (Pins R B d) (R × Fin d') :=
  PackedLookup.lookup (layout (Fin n) R) old (fun v => fixed (new v)) (fun r j => .input (.inl (r,.inr j)))

private def rekeyPin : Pins R B d' → Pins R B d ⊕ (R × Fin d')
  | .inl (r,.inl ()) => .inl (.inl (r,.inl ()))
  | .inl (r,.inr j) => .inr (r,j)
  | .inr b => .inl (.inr b)

/-- Translate all physical owner words in one batch. Presence bits and the immutable payload
are forwarded directly, including fields whose stored width differs from the new key width. -/
noncomputable def rekey : Frame (Pins R B d) (Pins R B d') :=
  (keys (R := R) (B := B) old new).withInput.select rekeyPin

/-- Size of the stable site-key translation for a single inherited rectangle. -/
theorem rekey_size : (rekey (R := R) (B := B) old new).size ≤ lookupCost n (Fintype.card R) d d' := by
  have h := queries_size (layout (Fin n) R) (fun u => fixed (σ := Pins R B d) (old u))
    (fun u => fixed (new u)) (fun r j => .input (.inl (r,.inr j)))
    1 le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa only [rekey,Frame.select_size,Frame.withInput_size,keys,PackedLookup.lookup,lookupCost,Fintype.card_fin,
    Nat.mul_one] using h

private theorem owner_rekey (z : Pins R B d → Bool) (r : R) (v : Fin n) (hv : owner z r = (old v).val) :
    owner ((rekey old new).eval z) r = (new v).val := by
  simp only [owner,rekey,Frame.select_eval,rekeyPin,Frame.withInput_eval_inr,keys]
  let request := fun (a : R) (j : Fin d) =>
    (BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.input
      (Sum.inl (a,Sum.inr j)) : VPVNP.VerifierNetwork.Expr (Pins R B d))
  have h := PackedLookup.lookup_value (layout (Fin n) R) old (fun u => fixed (new u)) request z r v hv
  exact h.trans (fixed_value z _)

/-- Translating the owner keys preserves every per-site list and all its record boundaries.
Only true owners are required to have valid old keys. -/
theorem Schema.Block.rekey {sites : V ↪ Fin n} (h : S.Block x (fun v => (old (sites v)).val) records) :
    S.Block ((FrozenTape.rekey old new).eval x) (fun v => (new (sites v)).val) records := by
  constructor
  · intro r hr active
    obtain ⟨v,hv⟩ := h.owners r hr (by simpa [FrozenTape.rekey,rekeyPin] using active)
    exact ⟨v,owner_rekey old new _ r _ hv⟩
  · intro v
    rw [← h.atSite v,Schema.atSite,Schema.atSite]
    apply List.filterMap_congr
    intro r hr
    have active : (FrozenTape.rekey old new).eval x (.inl (r,.inl ())) = x (.inl (r,.inl ())) := by
      simp [FrozenTape.rekey,rekeyPin]
    have read : S.read ((FrozenTape.rekey old new).eval x) r = S.read x r := by
      simp [Schema.read,FrozenTape.rekey,rekeyPin]
    by_cases en : x (.inl (r,.inl ())) = true
    · obtain ⟨u,hu⟩ := h.owners r hr en
      simp only [active,en,true_and,owner_rekey old new _ r _ hu,hu,Fin.val_inj,new.injective.eq_iff,
        old.injective.eq_iff,read]
    · simp [active,en]

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
