import OAI.Computability.BorderVNP.PackedInheritedProfileRoom

/-! # Intrinsic locality of born origin and terminal sites

The full public records at a new profile site use only its finite work and
input area. They produce an empty observation list on acceptance, since these
sites have no paid factors. This establishes the locality invariant needed to
carry these blocks through subsequent interval layers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Crossing.Profile.Cell Inherited BankSite BankJoint BankCircuit BankPacket CellSparse
open scoped Classical

/-- A site with an empty private box directory returns only its record validity bit. -/
theorem observe_empty_boxes (s : Site) (empty : s.boxes = []) (f : ℕ → Bool) :
    s.observe f = if ∀ r ∈ s.rows,r.Valid [] f then some [] else none := by
  have ho : s.directory.occurrences = [] := by
    simp only [Site.directory,Directory.occurrences,empty]
    apply List.flatMap_eq_nil_iff.mpr
    intro r _
    cases r <;> simp
  have hobs : s.directory.observations f = some [] := by simp [Directory.observations,ho]
  simp [Site.observe,empty,hobs]

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm) (a : S)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable {ns ne np : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)
variable (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
local notation3 "G₀" => G e p bin perm positive first q
local notation3 "j₀" => blocks p.layout bin perm m a
local notation3 "v₀" => seedSite e p bin perm positive first q a
local notation3 "work₀" => workAt e p bin perm positive first q
local notation3 "raw₀" => raw e p bin perm positive first q a siteID edgeID portID
local notation3 "orig₀" => originSite e p bin perm positive first q a siteID edgeID portID

/-- The origin's single block remains a local site program on arbitrary bank functions. -/
theorem origin_local : (orig₀).Local := by
  intro f g h
  let x := originWords e raw₀
  have hx : localHeader x = headerWord m (fun i => i.elim j₀ (q a).val) := rfl
  have ho : x none = 0 := profile_start e p bin perm positive first q a siteID (.inl ())
  have hr := origin_congr m j₀ (q a).val x hx [] f g first
    (fun k => by rw [ho,zero_add]; exact h _ (k.isLt.trans_le (Nat.le_add_right (orig₀).work _)))
    (fun t i k => h _ (origin_room e p bin perm positive first q a siteID edgeID portID t i k))
  have ht : (∀ r ∈ (orig₀).rows,r.Valid [] f) ↔ ∀ r ∈ (orig₀).rows,r.Valid [] g := by
    simp only [Site.rows,originSite,List.reverse_cons,List.reverse_nil,List.nil_append,List.flatten_cons,
      List.flatten_nil,List.append_nil]
    exact hr
  rw [observe_empty_boxes _ rfl,observe_empty_boxes _ rfl]
  by_cases hv : ∀ r ∈ (orig₀).rows,r.Valid [] f
  · rw [ite_eq_left hv,ite_eq_left (ht.mp hv)]
  · rw [ite_eq_right hv,ite_eq_right (mt ht.mpr hv)]

variable (binName : S → ℕ)
local notation3 "term₀" => terminalSite e p bin perm positive first q a siteID edgeID portID binName

/-- A new terminal's header, feeders, padding, and all incoming clipped hooks
use only the finite intrinsic bank, for arbitrary choices of its staged input. -/
theorem terminal_local (t : Fin D × Bool) : (term₀ t).Local := by
  intro f g h
  let x := terminalWords e raw₀ t
  have hx : localHeader x = headerWord m (fun i => i.elim j₀ (q a).val) := rfl
  have ho : x none = 0 := profile_start e p bin perm positive first q a siteID (.inr t)
  have hr := terminal_congr m j₀ (q a).val x hx [] f g (profileCounts_total e _ q a)
    (fun k => by rw [ho,zero_add]; exact h _ (k.isLt.trans_le (Nat.le_add_right (term₀ t).work _)))
    (fun i k => h _ (terminal_spoke_room e p bin perm positive first q a siteID edgeID portID binName t i k))
    (fun u i k => h _ (terminal_feeder_room e p bin perm positive first q a siteID edgeID portID binName t u i k))
  have hh : (∀ r ∈ hookRows e p bin perm positive first q a siteID edgeID portID binName t,r.Valid [] f) ↔
      ∀ r ∈ hookRows e p bin perm positive first q a siteID edgeID portID binName t,r.Valid [] g := by
    simp only [hookRows,List.forall_mem_map]
    apply forall_congr'; intro z
    apply imp_congr_right; intro _
    exact hook_local e p bin perm positive first q a siteID edgeID portID binName t z f g h
  have ht : (∀ r ∈ (term₀ t).rows,r.Valid [] f) ↔ ∀ r ∈ (term₀ t).rows,r.Valid [] g := by
    simp only [Site.rows,terminalSite,List.reverse_cons,List.reverse_nil,List.nil_append,List.flatten_cons,
      List.flatten_nil,List.append_nil,List.forall_mem_append]
    exact and_congr hr hh
  rw [observe_empty_boxes _ rfl,observe_empty_boxes _ rfl]
  by_cases hv : ∀ r ∈ (term₀ t).rows,r.Valid [] f
  · rw [ite_eq_left hv,ite_eq_left (ht.mp hv)]
  · rw [ite_eq_right hv,ite_eq_right (mt ht.mpr hv)]

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
