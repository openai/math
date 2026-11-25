import OAI.Computability.BorderVNP.PackedInheritedPaidEmit
import OAI.Computability.BorderVNP.PackedCellCapacity
import OAI.Computability.BorderVNP.ShortenEpochRoundRecords

/-! # Intrinsic seed locations fit in the selected physical tile budget

The incident area of one site is bounded by its tile's expanded records.
The two copied paid banks or padded profile work prefix is bounded by the
same record budget times the frozen seed multiplier. Together they bound
all input addresses of the intrinsic packet compiler.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.StaticRows Shortening.SeedIntervals Shortening.CombiningStep
open Inherited BankSite BankJoint CellAddresses
open scoped Classical
open private localRecords_mono from OAI.Computability.BorderVNP.ShortenEpochRoundRecords

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Intrinsic seed work is covered by the full expanded physical charge. -/
theorem intrinsic_work_le (j : ℕ) (h : Fin e.count → ℕ) (total : ∑ i,h i = j) (v : TemplateSite e) :
    intrinsicWork e j h v ≤ BankCharges.volume e j h v := by
  rcases v with ⟨⟩ | t | ⟨i,v⟩
  · exact (work_profile e j h total (.inl ())).le
  · exact (work_profile e j h total (.inr t)).le
  · rw [PaidSite.raw_work]
    change h i*PaidBox.arity e i v + h i*PaidBox.arity e i v ≤ h i*(1+2*PaidBox.arity e i v)
    ring_nf
    omega

variable [NeZero D] {P S : Type} [Fintype P] [Fintype S] {bits : P → ℕ} (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool)
    (first : Fin D × Bool) (q : Counts e p bin perm)
local notation3 "G₀" => (output e p bin perm positive first q).layout

variable {T : Type*} (tile : (output e p bin perm positive first q).layout.Site → T)
    (prior payload : p.layout.Site → ℕ) (M : ℕ)
    (cap : ∀ t, localRecords (output e p bin perm positive first q).layout true
      (Sum.elim prior (fun _ => 0)) (Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2))
      (fun v => tile v = t) ≤ M)

include cap in
/-- Every virtual-cell incidence bank is bounded by the actual physical tile cap. -/
theorem incoming_le_cap (v : (G₀).Site) : incoming G₀ v ≤ M := by
  let prev : (G₀).Site → ℕ := Sum.elim prior (fun _ => 0)
  let pay : (G₀).Site → ℕ := Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2)
  have h := wireCapacity_le G₀ id v prev pay
  exact h.trans ((localRecords_mono G₀ true prev pay (fun u hu => congrArg tile (show u = v from hu))).trans (cap (tile v)))

include cap in
/-- Full work and physical input slab, including loops, fit the chosen word budget. -/
theorem seed_slab_le (a : S) (v : TemplateSite e) :
    intrinsicWork e (blocks p.layout bin perm m a) (q a).val v +
      incoming G₀ (seedSite e p bin perm positive first q a v) ≤ BankCharges.bound e*M+M := by
  have hw := BankCharges.site_le e p bin perm positive first q tile prior payload M cap a v
  exact Nat.add_le_add ((intrinsic_work_le e _ _ (profileCounts_total e _ q a) v).trans ((Nat.le_add_left _ _).trans hw))
    (incoming_le_cap e p bin perm positive first q tile prior payload M cap _)

variable {ne np : ℕ} (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)

include cap in
/-- Each actual intrinsic location field of the frozen public seed encoder fits that same slab bound. -/
theorem relative_location_le (a : S) (z : Σ v : TemplateSite e, Location e v) :
    relativeRaw e p bin perm positive first q a edgeID portID (.inr z) ≤ BankCharges.bound e*M+M := by
  rcases z with ⟨v,(_ | _ | r)⟩
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · cases hr : reference e v r with
    | none => simp [relativeRaw,hr]
    | some pair =>
      obtain ⟨u,side⟩ := pair
      rw [relative_raw_ref e p bin perm positive first q a edgeID portID v r u side hr]
      have hv := reference_site e p bin perm positive first q a v r u side hr
      apply (Nat.add_le_add_left _ _).trans (seed_slab_le e p bin perm positive first q tile prior payload M cap a v)
      cases side
      · exact (Nat.le_add_right _ _).trans ((wireEnd_le G₀ edgeID portID _ ⟨.inr (.inr ⟨a,u⟩),.inr rfl⟩).trans_eq (congrArg (incoming G₀) hv))
      · exact (Nat.le_add_right _ _).trans ((wireEnd_le G₀ edgeID portID _ ⟨.inr (.inr ⟨a,u⟩),.inl rfl⟩).trans_eq (congrArg (incoming G₀) hv))

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
