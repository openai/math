import OAI.Computability.BorderVNP.PackedInheritedBirthAdjust

/-! # One shared executable intrinsic operand frame for every seed

The two live histogram inputs and the virtual endpoint address views supply
the complete immutable site fields. The circuit is chosen before the represented
combining step, works on all accepted branches, and uses no physical constants
from the current contraction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited BankSite BankJoint ParseBatchSort VPVNP.VerifierNetwork Word CellAddressCircuit CellAddressPhysical
open private zero zero_size from OAI.Computability.BorderVNP.PackedBankInstall
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {S : Type} [Fintype S] {n s k u C d h w : ℕ} (seed : S ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields (siteCapacity e s n) (edgeCapacity e k n) u C d h w σ)
variable (counts : Frame σ (S × Option (Fin e.count) × Fin w))

private noncomputable def zeroIDs : Frame σ (Fin (siteCapacity e s n) × Fin w) :=
  (zero (σ := σ)).select (fun _ => ())

variable {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (bin : p.layout.Edge → Option S)
variable (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (oldSite : p.layout.Site ↪ Fin s) (oldEdge : p.layout.Edge ↪ Fin k) (portID : P ↪ Fin u)
variable (cell : (G e p bin perm positive first q).Site → Fin C) (aux : (G e p bin perm positive first q).Site → ℕ)
local notation3 "G₀" => G e p bin perm positive first q
local notation3 "sID" => siteRows e p oldSite seed
local notation3 "eID" => outputRows e p bin perm positive first q oldEdge seed
variable {x : σ → Bool} (rep : Represents (G e p bin perm positive first q) cell aux (siteRows e p oldSite seed)
  (outputRows e p bin perm positive first q oldEdge seed) portID F x)
variable (room : ∀ v, incoming (G e p bin perm positive first q) v < 2^w)

include rep room in
private theorem source_adjust (a : S)
    (hcount : ∀ i, value (fun j => counts.eval x (a,i,j)) = i.elim (blocks p.layout bin perm m a) (q a).val)
    (r : Raw e) :
    let base := rawWord e seed s k counts (Views.frame F) (zeroIDs (s := s) (n := n) e) x a
    (adjust e r).eval base = relativeRaw e p bin perm positive first q a eID portID r := by
  intro base
  have hc (i : Option (Fin e.count)) : base (.inl i) = i.elim (blocks p.layout bin perm m a) (q a).val := hcount i
  rcases r with i | ⟨v,(_ | _ | b)⟩
  · exact hc i
  · rfl
  · rfl
  · cases hr : reference e v b with
    | none => simp [adjust,relativeRaw,hr,WidthExpr.eval]
    | some pair =>
      obtain ⟨z,src⟩ := pair
      have he : base (.inr ⟨v,some (some b)⟩) = newEnd e p bin perm positive first q a eID portID z src := by
        cases src
        · simp only [base,rawWord,hr]
          change value (fun j => (Views.frame F).eval x (.inl (.inl (.inr (edgeSlot e k (seed a) z))),j)) = _
          rw [edgeSlot_actual e p bin perm positive first q oldEdge seed]
          exact Views.dest_value F G₀ cell aux sID eID portID rep room _
        · simp only [base,rawWord,hr]
          change value (fun j => (Views.frame F).eval x (.inl (.inl (.inl (edgeSlot e k (seed a) z))),j)) = _
          rw [edgeSlot_actual e p bin perm positive first q oldEdge seed]
          exact Views.source_value F G₀ cell aux sID eID portID rep room _
      simp only [adjust,hr,WidthExpr.eval,Op.apply,PoolCircuit.scale_eval,hc,he,relativeRaw,Option.elim_some,
        intrinsicWork]

omit rep room in
private theorem relative_fit (a : S) (hcount : ∀ i, value (fun j => counts.eval x (a,i,j)) =
    i.elim (blocks p.layout bin perm m a) (q a).val)
    (fit : ∀ v, intrinsicWork e (blocks p.layout bin perm m a) (q a).val v +
      incoming G₀ (seedSite e p bin perm positive first q a v) < 2^w) (r : Raw e) :
    relativeRaw e p bin perm positive first q a eID portID r < 2^w := by
  rcases r with i | ⟨v,(_ | _ | b)⟩
  · exact (hcount i).symm.trans_lt (value_lt _)
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _
  · cases hr : reference e v b with
    | none => simp [relativeRaw,hr]
    | some pair =>
      obtain ⟨z,src⟩ := pair
      have hv := reference_site e p bin perm positive first q a v b z src hr
      have hf := fit v
      rw [relative_raw_ref e p bin perm positive first q a eID portID v b z src hr]
      apply Nat.lt_of_le_of_lt (Nat.add_le_add_left _ _) hf
      cases src
      · apply (Nat.le_add_right _ _).trans ((wireEnd_le G₀ eID portID _ ⟨.inr (.inr ⟨a,z⟩),.inr rfl⟩).trans_eq _)
        exact congrArg (incoming G₀) hv
      · apply (Nat.le_add_right _ _).trans ((wireEnd_le G₀ eID portID _ ⟨.inr (.inr ⟨a,z⟩),.inl rfl⟩).trans_eq _)
        exact congrArg (incoming G₀) hv

/-- One finite gate list gives all immutable origin, terminal and paid raw fields.
It is chosen before the pack, masks, accepted histogram and address interpretation. -/
theorem exists_relativeRawFrame :
    ∃ f : Frame σ (S × Raw e × Fin w), f.size ≤ counts.size+(Views.frame F).size+3+
      Fintype.card S*(adjustNodes e*(100*(w+1)^2)) ∧
    ∀ {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (bin : p.layout.Edge → Option S)
      (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
      (oldSite : p.layout.Site ↪ Fin s) (oldEdge : p.layout.Edge ↪ Fin k) (portID : P ↪ Fin u),
      let G := (output e p bin perm positive first q).layout
      let site := siteRows e p oldSite seed
      let edge := outputRows e p bin perm positive first q oldEdge seed
      ∀ (cell : G.Site → Fin C) (aux : G.Site → ℕ) (x : σ → Bool), Represents G cell aux site edge portID F x →
        (∀ v, incoming G v < 2^w) → ∀ a,
          (∀ i, value (fun j => counts.eval x (a,i,j)) = i.elim (blocks p.layout bin perm m a) (q a).val) →
          (∀ v, intrinsicWork e (blocks p.layout bin perm m a) (q a).val v +
            incoming G (seedSite e p bin perm positive first q a v) < 2^w) →
          ∀ r, value (fun j => f.eval x (a,r,j)) = relativeRaw e p bin perm positive first q a edge portID r := by
  let ids := zeroIDs (σ := σ) (s := s) (n := n) (w := w) e
  let base := install e seed s k counts (Views.frame F) ids
  obtain ⟨f,hs,hf⟩ := exists_adjustFrame e w base
  refine ⟨f,?_,?_⟩
  · have hi : ids.size ≤ 1 := by
      change ((zero (σ := σ)).select _).size ≤ 1
      rw [Frame.select_size]
      exact zero_size
    have hb := install_size e seed s k counts (Views.frame F) ids
    change base.size ≤ _ at hb
    omega
  · intro P _ bits p bin perm positive first q oldSite oldEdge portID G site edge cell aux x rep room a hcount fit r
    have hr := source_adjust e seed F counts p bin perm positive first q oldSite oldEdge portID cell aux rep room a hcount r
    have he := hf x a r
    dsimp only at hr he
    rw [funext (install_value e seed s k counts (Views.frame F) ids x a)] at he
    rw [hr] at he
    exact he (relative_fit e seed counts p bin perm positive first q oldEdge portID a hcount fit r)

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
