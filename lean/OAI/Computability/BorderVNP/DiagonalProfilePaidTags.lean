import OAI.Computability.BorderVNP.DiagonalSiteTagRead
import OAI.Computability.BorderVNP.PackedInheritedPaidModel

/-! # The paid box reports the selected tagged entries, before evaluating their scalars -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.PaidSite

open Crossing Shortening Shortening.CombiningStep Shortening.SeedIntervals PaidBox Diagonal.CellEntries
open private extendWires extendPorts from OAI.Computability.BorderVNP.PackedInheritedRoundValue
open scoped Classical

set_option maxHeartbeats 1200000
set_option maxRecDepth 5000

variable {D m ne np : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type*} [Fintype P] {bits : P → ℕ}
    {Param Gadget : Type*} (e : PaidIdentity K D m) (src : Pack D P bits (Entry Param Gadget))
    (field : src.layout.Tables K) {A : Type} [Fintype A] (bin : src.layout.Edge → Option A)
    (perm : Fin D → Equiv.Perm A) (positive : src.layout.Edge → Bool) (first : Fin D × Bool)
    (q : ProfileCounts e (blocks src.layout bin perm m)) (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
    (a : A) (i : Fin e.count) (v : (e.net i).Site)

local notation3 "p₀" => (⟨src.layout,field⟩ : Pack D P bits K)
local notation3 "G₀" => (output e p₀ bin perm positive first q).layout
local notation3 "here₀" => PaidPhysical.site e p₀ bin perm positive first q a i v

/-- Every local assignment has exactly one successful staging word and reports exactly
the scalar positions occurring in its tagged product, including repeated positions. -/
theorem tag_read (edgeID : (G₀).Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (z : ∀ c : Incident G₀ here₀, Fin ((G₀).width c.val) → Bool)
    (x : ∀ u : Attached G₀ here₀, Fin (bits u.val) → Bool) :
    Nonempty ((physical e p₀ bin perm positive first q a i v edgeID portID (num ∘ pos)).TagRead (inputWords G₀ edgeID portID here₀ z x) (fun _ => True)
      ((roundTags src bin perm e pos positive first q).table here₀ z x) num) := by
  let wires := extendWires G₀ here₀ z
  let ext := extendPorts G₀ here₀ x
  have hz : (fun c : Incident G₀ here₀ => wires c.val) = z := by
    funext c k
    simp only [wires,extendWires,dite_eq_left c.property]
  have hx : (fun u : Attached G₀ here₀ => ext u.val) = x := by
    funext u k
    simp only [ext,extendPorts,dite_eq_left u.property]
  let selected (j : Fin ((q a).val i)) := pos (selectedEntry e i v (q a).val
    (PaidPhysical.profileWires e p₀ bin perm positive first q a wires) j)
  let words := inputWords G₀ edgeID portID here₀ z x
  let canon := canonicalWork ((q a).val i) (incoming G₀ here₀) e i v
    (starts e p₀ bin perm positive first q a i v edgeID portID) words
  let seen := List.ofFn fun j => (false,some (num (selected j)))
  let tagged : (G₀).Tables (Entry Param Gadget) := (roundTags src bin perm e pos positive first q).table
  have ht := PaidPhysical.tagged_read e src field bin perm positive first q pos a i v wires ext
  change tagged here₀ (fun c : Incident G₀ here₀ => wires c.val) (fun u : Attached G₀ here₀ => ext u.val) = ∏ j, gadget (Param := Param) (selected j) at ht
  rw [hz,hx] at ht
  change Nonempty ((physical e p₀ bin perm positive first q a i v edgeID portID (num ∘ pos)).TagRead words
    (fun _ => True) (tagged here₀ z x) num)
  rw [ht]
  have pass : (∏ j, gadget (Param := Param) (selected j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun _ _ => WithZero.coe_ne_zero
  refine ⟨⟨canon,seen,trivial,?_,fun _ => PaidPhysical.observed_count (Param := Param) selected num⟩⟩
  intro g os _
  have h := physical_work_iff e p₀ bin perm positive first q a i v edgeID portID (num ∘ pos) wires ext g os
  rw [hz,hx] at h
  exact h.trans ⟨fun h => ⟨pass,h⟩,And.right⟩

end Packing.Inherited.PaidSite

end BorderVNP
end Computability
end OAI
