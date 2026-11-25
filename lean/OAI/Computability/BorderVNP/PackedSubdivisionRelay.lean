import OAI.Computability.BorderVNP.PackedHistoryPrivateSites
import OAI.Computability.BorderVNP.PackedInheritedProfileLocal
import OAI.Computability.BorderVNP.PackedBankInheritedValue
import OAI.Computability.BorderVNP.PackedSubdivision

/-! # Intrinsic private program of an inserted subdivision relay

An interior site reads only the two physical words on its predecessor and successor
hops. Its sole sparse record equates their lanes at the intrinsic incidence addresses.
A successful relay has one work assignment and contributes the empty observation list.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Crossing CellSparse
open scoped Classical
open private bits_right from OAI.Computability.BorderVNP.PackedInheritedStaging

variable {D ne np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (routes : N.WireRoutes)
local notation "G" => N.subdivide routes
variable (edgeID : (N.subdivide routes).Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (j : (e : N.Edge) × Fin (routes.interior e))

/-- Incoming hop at an interior subdivision site. -/
def leftHop : Incident G (.inr j) := ⟨⟨j.1,j.2.castSucc⟩,.inr (by simp [Network.subdivide])⟩

/-- Outgoing hop at the same subdivision site. -/
def rightHop : Incident G (.inr j) := ⟨⟨j.1,j.2.succ⟩,.inl (by simp [Network.subdivide])⟩

private noncomputable def first := wireStart G edgeID portID (.inr j) (leftHop N routes j)
private noncomputable def second := wireStart G edgeID portID (.inr j) (rightHop N routes j)

/-- Single compressed equality row for all bits of both adjacent hop words. -/
noncomputable def relayRecord : Record :=
  .equal 1 (N.width j.1) ⟨first N routes edgeID portID j,0,1⟩ ⟨second N routes edgeID portID j,0,1⟩

/-- Relay at birth, with no work or opaque tables and one compressed equality command. -/
noncomputable def relaySite : Site :=
  ⟨0,incoming G (.inr j),[],[[relayRecord N routes edgeID portID j]]⟩

/-- Complete intrinsic lineage of a subdivision relay, prior to any further retention. -/
noncomputable def relayLineage : Site.Lineage (incoming G (.inr j)) :=
  Site.Lineage.start (relaySite N routes edgeID portID j) rfl

/-- One public row, zero private boxes, and zero work slots per inserted site. -/
theorem relay_counts :
    (relayLineage N routes edgeID portID j).program.rows.length = 1 ∧
    (relayLineage N routes edgeID portID j).program.boxes.length = 0 ∧
    (relayLineage N routes edgeID portID j).program.work = 0 := by exact ⟨rfl,rfl,rfl⟩

/-- The finite scalar bank passes exactly when the two addressed hop words agree. -/
theorem relay_valid (bank : ℕ → Bool) :
    (relayRecord N routes edgeID portID j).Valid [] bank ↔
      ∀ k : Fin (N.width j.1),
        bank (wireStart G edgeID portID (.inr j) (leftHop N routes j)+k.val) =
        bank (wireStart G edgeID portID (.inr j) (rightHop N routes j)+k.val) := by
  simp only [relayRecord,Record.Valid,equalValid,Port.atBit,mul_zero,add_zero,mul_one,first,second]
  exact ⟨fun h k => h 0 (by decide) k.val k.isLt,fun h _ _ k hk => h ⟨k,hk⟩⟩

/-- A successful equality check contributes the empty observation. -/
theorem relay_observe (bank : ℕ → Bool) :
    (relaySite N routes edgeID portID j).observe bank =
      if (relayRecord N routes edgeID portID j).Valid [] bank then some [] else none := by
  rw [InheritedProfile.observe_empty_boxes _ rfl]
  simp [relaySite,Site.rows]

/-- Every accessed lane lies inside the intrinsic relay bank. -/
theorem relay_local : (relaySite N routes edgeID portID j).Local := by
  intro f g agree
  have hf := wireEnd_le G edgeID portID (.inr j) (leftHop N routes j)
  have hs := wireEnd_le G edgeID portID (.inr j) (rightHop N routes j)
  change first N routes edgeID portID j + N.width j.1 ≤ incoming G (.inr j) at hf
  change second N routes edgeID portID j + N.width j.1 ≤ incoming G (.inr j) at hs
  have eqn : (relayRecord N routes edgeID portID j).Valid [] f ↔ (relayRecord N routes edgeID portID j).Valid [] g := by
    rw [relay_valid,relay_valid]
    apply forall_congr'
    intro k
    have a : f (first N routes edgeID portID j+k.val) = g (first N routes edgeID portID j+k.val) := by
      apply agree; change _ < 0+incoming G (.inr j); have := k.isLt; omega
    have b : f (second N routes edgeID portID j+k.val) = g (second N routes edgeID portID j+k.val) := by
      apply agree; change _ < 0+incoming G (.inr j); have := k.isLt; omega
    exact (congrArg₂ (·=·) a b).to_iff
  rw [relay_observe,relay_observe,propext eqn]

variable (z : ∀ h : Incident (N.subdivide routes) (.inr j), Fin ((N.subdivide routes).width h.val) → Bool)
variable (x : ∀ p : Attached (N.subdivide routes) (.inr j), Fin (bits p.val) → Bool)

/-- Intrinsic word validity coincides with the old tensor's exact physical equality
factor, with all zero-width cases included. -/
theorem relay_valid_inputs (work : Fin 0 → Bool) :
    (relayRecord N routes edgeID portID j).Valid []
        (Inherited.bits work (inputWords G edgeID portID (.inr j) z x)) ↔
      z (leftHop N routes j) = z (rightHop N routes j) := by
  let input := inputWords G edgeID portID (.inr j) z x
  have reads (h : Incident G (.inr j)) (k : Fin ((N.subdivide routes).width h.val)) :
      Inherited.bits work input (wireStart G edgeID portID (.inr j) h+k.val) = z h k := by
    let ord := sourceOrder G edgeID portID (.inr j) (.inl ⟨h,k⟩)
    rw [←wireOrdinal G edgeID portID (.inr j) h k]
    have a : Inherited.bits work input ord.val = input ord := by simpa only [zero_add] using bits_right work input ord
    exact a.trans (inputWords_wire G edgeID portID (.inr j) z x h k)
  rw [relay_valid]
  constructor
  · intro good
    funext k
    exact (reads (leftHop N routes j) k).symm.trans ((good k).trans (reads (rightHop N routes j) k))
  · intro same k
    exact (reads (leftHop N routes j) k).trans ((congrFun same k).trans (reads (rightHop N routes j) k).symm)

/-- Each successful observation fiber is inhabited precisely for the empty sequence
on equal physical hops. Its work type has exactly one element. -/
theorem relay_fiber_nonempty (obs : List (Bool × Option ℕ)) :
    Nonempty ((relaySite N routes edgeID portID j).Fiber (inputWords G edgeID portID (.inr j) z x) obs) ↔
      z (leftHop N routes j) = z (rightHop N routes j) ∧ obs = [] := by
  constructor
  · rintro ⟨g⟩
    have hg := g.property
    rw [relay_observe] at hg
    split at hg
    · exact ⟨(relay_valid_inputs N routes edgeID portID j z x g.val).mp (by assumption),(Option.some.inj hg).symm⟩
    · contradiction
  · rintro ⟨he,rfl⟩
    refine ⟨⟨fun i => Fin.elim0 i,?_⟩⟩
    rw [relay_observe]
    apply ite_eq_left
    exact (relay_valid_inputs N routes edgeID portID j z x _).mpr he

/-- The native relay table equals the physical subdivision table, for arbitrary
original entries and any weight assigning one to the empty observation. -/
theorem relay_models {R : Type*} [AddCommMonoid R] [One R] (weight : List (Bool × Option ℕ) → R)
    (one : weight [] = 1) (table : N.Tables R) :
    (relaySite N routes edgeID portID j).Models G edgeID portID (.inr j) rfl weight
      (N.subdivideTables routes table) := by
  intro a p
  let input := inputWords G edgeID portID (.inr j) a p
  have term (g : Fin 0 → Bool) : ((relaySite N routes edgeID portID j).observe (Inherited.bits g input)).elim 0 weight =
      if a (leftHop N routes j) = a (rightHop N routes j) then (1 : R) else 0 := by
    rw [relay_observe]
    change (if (relayRecord N routes edgeID portID j).Valid [] (Inherited.bits g (inputWords G edgeID portID (.inr j) a p))
        then some [] else none).elim 0 weight = _
    rw [propext (relay_valid_inputs N routes edgeID portID j a p g)]
    split <;> simp [one]
  change (∑ g : Fin 0 → Bool, ((relaySite N routes edgeID portID j).observe (Inherited.bits g input)).elim 0 weight) = _
  rw [Fintype.sum_unique]
  exact term _

end Packing.Inherited.Subdivision

end BorderVNP
end Computability
end OAI
