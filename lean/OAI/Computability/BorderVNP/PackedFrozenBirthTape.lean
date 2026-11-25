import OAI.Computability.BorderVNP.PackedFrozenBirthOwner

/-! # Exact main birth tape at every physical public owner

The frozen schema is stable across all histograms. Every occupied record of
one seed template is selected, in its original packet order. Every retained
old site is outside the new rectangle and receives no main birth records.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Birth

open Shortening Shortening.StaticRows Crossing BankPacket BankJoint CellSparse ParseBatchSort VPVNP.VerifierNetwork
open private flat_single from OAI.Computability.BorderVNP.PackedFrozenTapeRows
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (first : Fin D × Bool)
    {S : Type} {σ : Type*} [Fintype S] [Fintype σ] {n d w : ℕ} (seed : S ↪ Fin n) (old : ℕ)
    (packet : Frame σ (S × Output e first × Fin w)) (fit : siteCapacity e old n ≤ 2^d) (x : σ → Bool)
    (raw : S → Raw e → ℕ)
    (words : ∀ a z, value (fun j => packet.eval x (a,z,j)) =
      (Packet.fieldList Packet.record (emitted e first (raw a) z.1))[z.2.val]?.getD 0)

local notation3 "out₀" => (frame (d := d) e first seed old packet).eval x
local notation3 "schema₀" => schema e first S w

omit [Fintype S] in
private theorem slot_injective : Function.Injective (fun sv : S × TemplateSite e => (slot e seed old sv).val) := by
  rintro ⟨a,v⟩ ⟨b,t⟩ h
  have hh := Fin.ext h
  change finSumFinEquiv (.inr (finProdFinEquiv (seed a,Fintype.equivFin _ v))) =
    finSumFinEquiv (.inr (finProdFinEquiv (seed b,Fintype.equivFin _ t))) at hh
  have he := finProdFinEquiv.injective (Sum.inr.inj (finSumFinEquiv.injective hh))
  exact Prod.ext (seed.injective (congrArg Prod.fst he)) ((Fintype.equivFin _).injective (congrArg Prod.snd he))

include fit words in
private theorem piece (key : ℕ) (z : S × TemplateSite e) :
    (List.ofFn fun i : Fin (rows e first z.2).length => (⟨z,i⟩ : Row e first S)).filterMap
      (fun r => if out₀ (.inl (r,.inl ())) ∧ owner out₀ r = key then some ((schema₀).read out₀ r) else none) =
      if (slot e seed old z).val = key then (emitted e first (raw z.1) z.2).map marked else [] := by
  let R := rows e first z.2
  let select (i : Fin R.length) : Row e first S := ⟨z,i⟩
  let emit := fun r : RecordCode (Operands e z.2) => marked (r.read (fun i => word e (raw z.1) (pin e z.2 i)))
  have hr (i : Fin R.length) : (schema₀).read out₀ (select i) = emit R[i] :=
    read e first S out₀ raw (fun a t => by simpa only [payload] using words a t) (select i)
  rw [show (List.ofFn select) = (List.finRange R.length).map select from List.ofFn_eq_map,List.filterMap_map]
  by_cases h : (slot e seed old z).val = key
  · rw [ite_eq_left h]
    have hm : (fun i : Fin R.length => if out₀ (.inl (select i,.inl ())) ∧ owner out₀ (select i) = key
        then some ((schema₀).read out₀ (select i)) else none) = fun i => some (emit R[i]) := by
      funext i
      rw [active,owner_value e first seed old packet fit,hr]
      simp [select,h]
    simp only [Function.comp_def]
    rw [hm]
    change (List.finRange R.length).filterMap (some ∘ (fun i => emit R[i])) = _
    rw [List.filterMap_eq_map]
    simp only [List.finRange,List.map_ofFn,Function.comp_def,emitted,List.map_map,emit,R]
    exact List.ofFn_getElem_eq_map R emit
  · rw [ite_eq_right h,List.filterMap_eq_nil_iff]
    intro i _
    simp only [Function.comp_apply,active,owner_value e first seed old packet fit,true_and,select,ite_eq_right h]

include fit words in
/-- Every intrinsic main record appears at its genuine public seed owner, in the exact frozen template order. -/
theorem at_seed (a : S) (v : TemplateSite e) :
    (schema₀).atSite out₀ (siteSlot e old (seed a) v).val = (emitted e first (raw a) v).map marked := by
  let enum := (Fintype.equivFin (S × TemplateSite e)).symm
  let sites := List.ofFn enum
  have hd : sites.Nodup := List.nodup_ofFn.mpr enum.injective
  have hm : (a,v) ∈ sites := List.mem_ofFn.mpr ⟨enum.symm (a,v),enum.apply_symm_apply _⟩
  rw [Schema.atSite]
  change (sites.flatMap _).filterMap _ = _
  rw [List.filterMap_flatMap]
  simp_rw [piece e first seed old packet fit x raw words]
  change (sites.flatMap fun z => if (slot e seed old z).val = (slot e seed old (a,v)).val then
    (emitted e first (raw z.1) z.2).map marked else []) = _
  simp_rw [(slot_injective e seed old).eq_iff]
  simpa only [ite_eq_left hm] using flat_single sites (a,v) (fun z => (emitted e first (raw z.1) z.2).map marked) hd

include fit in
/-- A retained old site receives no rows from the main birth rectangle. -/
theorem at_old {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) (oldSite : p.layout.Site ↪ Fin old)
    (v : p.layout.Site) :
    (schema₀).atSite out₀ (siteRows e p oldSite seed (.inl v)).val = [] := by
  rw [Schema.atSite,List.filterMap_eq_nil_iff]
  intro r _
  have hn : (slot e seed old r.1).val ≠ (siteRows e p oldSite seed (.inl v)).val := by
    intro h
    have he : siteRows e p oldSite seed (.inr ⟨r.1.1,r.1.2⟩) = siteRows e p oldSite seed (.inl v) := Fin.ext h
    have hc := (siteRows e p oldSite seed).injective he
    cases hc
  simp [active,owner_value e first seed old packet fit,hn]

end Packing.Inherited.FrozenTape.Birth

end BorderVNP
end Computability
end OAI
