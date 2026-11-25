import OAI.Computability.BorderVNP.PackedInheritedProfileObserve
import OAI.Computability.BorderVNP.PackedInheritedFieldWeight

/-! # Summing the intrinsic work at newly born profile sites

The physical wire assignment is independent of the work guess. Exactly its
canonical padded work vector can contribute, with one empty observation list
when the field factor is one. Thus each native site realizes its original
physical origin or terminal table on all incident cable and exterior inputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Crossing.Profile.Cell Inherited BankSite CellSparse
open private bits_left bits_right from OAI.Computability.BorderVNP.PackedInheritedStaging
open scoped Classical

private theorem value_unique {R : Type*} [AddCommMonoid R] (s : Site) (weight : List (Bool × Option ℕ) → R)
    (input : Fin s.incoming → Bool) (target : Fin s.work → Bool) (good : Prop) [Decidable good]
    (h : ∀ g, s.observe (bits g input) = if g = target ∧ good then some [] else none) :
    s.value weight input = if good then weight [] else 0 := by
  unfold Site.value
  simp_rw [h]
  rw [Finset.sum_eq_single target]
  · by_cases hg : good <;> simp [hg]
  · intro x _ hx
    simp [hx]
  · simp

private noncomputable def exterior {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits) (v : N.Site)
    (x : ∀ u : Attached N v, Fin (bits u.val) → Bool) : Ports bits :=
  fun u => if h : N.attach u = v then x ⟨u,h⟩ else fun _ => false

private theorem read_inputs {D ne np : ℕ} {P : Type} {R : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np) (v : N.Site) (aux : N.Site → ℕ)
    (noloop : ∀ z : Incident N v, N.src z.val ≠ N.dst z.val) (g : Fin (aux v) → Bool)
    (z : ∀ c : Incident N v, Fin (N.width c.val) → Bool)
    (x : ∀ u : Attached N v, Fin (bits u.val) → Bool) (table : N.Tables R) :
    let bank := Inherited.bits g (inputWords N edgeID portID v z x)
    N.read table ((cellView N aux bank).wires edgeID portID v) (exterior N v x) v = table v z x := by
  intro bank
  apply congrArg₂ (table v)
  · funext c k
    exact (view_cable N v aux edgeID portID noloop bank c k).trans
      ((bits_right g _ _).trans (inputWords_wire N edgeID portID v z x c k))
  · funext u
    exact dite_eq_left u.property

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
local notation3 "orig₀" => originSite e p bin perm positive first q a siteID edgeID portID
local notation3 "pack₀" => output e p bin perm positive first q

variable {R : Type*} [AddCommMonoid R] (weight : List (Bool × Option ℕ) → R) (ext : Ports bits)

/-- The sum over all origin work vectors contributes one empty observation exactly
when the sewn factor is one. -/
theorem origin_value (input : Fin ((orig₀).incoming) → Bool) :
    let v := v₀ (.inl ())
    let y := (cellView G₀ work₀ (Inherited.bits (fun _ : Fin ((orig₀).work) => false) input)).wires edgeID portID v
    (orig₀).value weight input = if (G₀).read (pack₀).table y ext v = 1 then weight [] else 0 := by
  intro v y
  apply value_unique (target := originWork e p bin perm positive first q a siteID edgeID portID y)
  intro g
  let b := Inherited.bits g input
  have hw : (cellView G₀ work₀ b).wires edgeID portID v = y :=
    view_wires_eq G₀ v work₀ edgeID portID (profile_noLoop e p bin perm positive first q a (.inl ()))
      b _ (fun i => (bits_right g input i).trans (bits_right (fun _ => false) input i).symm)
  have h := origin_observe e p bin perm positive first q a siteID edgeID portID ext b
  dsimp only at h
  rw [hw,show (fun k : Fin ((orig₀).work) => b k.val) = g from funext (bits_left g input)] at h
  exact h

/-- With unit weight on the empty observation, the native origin realizes the true
field-valued site table for every assignment to its incident wires and ports. -/
theorem origin_models (weight : List (Bool × Option ℕ) → K) (hone : weight [] = 1) :
    (orig₀).Models G₀ edgeID portID (v₀ (.inl ())) rfl weight (pack₀).table := by
  intro z x
  let v := v₀ (.inl ())
  let input := inputWords G₀ edgeID portID v z x
  let b := Inherited.bits (fun _ : Fin ((orig₀).work) => false) input
  let y := (cellView G₀ work₀ b).wires edgeID portID v
  let ext := exterior G₀ v x
  have ht := read_inputs G₀ edgeID portID v work₀ (profile_noLoop e p bin perm positive first q a (.inl ()))
    (fun _ => false) z x (pack₀).table
  change (orig₀).value weight input = _
  rw [← ht]
  change (orig₀).value weight input = (G₀).read (pack₀).table y ext v
  have h := origin_value e p bin perm positive first q a siteID edgeID portID weight ext input
  apply h.trans
  change (if (G₀).read (pack₀).table y ext (.inr ⟨a,.inl ()⟩) = 1 then weight [] else 0) = (G₀).read (pack₀).table y ext (.inr ⟨a,.inl ()⟩)
  rw [hone,origin_factor e p bin perm positive first q a y ext]
  split_ifs <;> simp_all

variable (binName : S → ℕ)
local notation3 "term₀" => terminalSite e p bin perm positive first q a siteID edgeID portID binName

/-- The terminal sums exactly one private work assignment for a valid selector,
feeder and gathered word, including empty hooks and zero term multiplicities. -/
theorem terminal_value (t : Fin D × Bool) (input : Fin ((term₀ t).incoming) → Bool) :
    let v := v₀ (.inr (.inl t))
    let y := (cellView G₀ work₀ (Inherited.bits (fun _ : Fin ((term₀ t).work) => false) input)).wires edgeID portID v
    (term₀ t).value weight input = if (G₀).read (pack₀).table y ext v = 1 then weight [] else 0 := by
  intro v y
  apply value_unique (target := terminalWork e p bin perm positive first q a siteID edgeID portID binName t y)
  intro g
  let b := Inherited.bits g input
  have hw : (cellView G₀ work₀ b).wires edgeID portID v = y :=
    view_wires_eq G₀ v work₀ edgeID portID (profile_noLoop e p bin perm positive first q a (.inr t))
      b _ (fun i => (bits_right g input i).trans (bits_right (fun _ => false) input i).symm)
  have h := terminal_observe e p bin perm positive first q a siteID edgeID portID ext b binName t
  dsimp only at h
  rw [hw,show (fun k : Fin ((term₀ t).work) => b k.val) = g from funext (bits_left g input)] at h
  exact h

/-- The native terminal with all actual clipped hook rows realizes its sewn table
in the original field, preserving every physical external and cable assignment. -/
theorem terminal_models (t : Fin D × Bool) (weight : List (Bool × Option ℕ) → K) (hone : weight [] = 1) :
    (term₀ t).Models G₀ edgeID portID (v₀ (.inr (.inl t))) rfl weight (pack₀).table := by
  intro z x
  let v := v₀ (.inr (.inl t))
  let input := inputWords G₀ edgeID portID v z x
  let b := Inherited.bits (fun _ : Fin ((term₀ t).work) => false) input
  let y := (cellView G₀ work₀ b).wires edgeID portID v
  let ext := exterior G₀ v x
  have ht := read_inputs G₀ edgeID portID v work₀ (profile_noLoop e p bin perm positive first q a (.inr t))
    (fun _ => false) z x (pack₀).table
  change (term₀ t).value weight input = _
  rw [← ht]
  change (term₀ t).value weight input = (G₀).read (pack₀).table y ext v
  have h := terminal_value e p bin perm positive first q a siteID edgeID portID weight ext binName t input
  apply h.trans
  change (if (G₀).read (pack₀).table y ext (.inr ⟨a,.inr (.inl t)⟩) = 1 then weight [] else 0) = (G₀).read (pack₀).table y ext (.inr ⟨a,.inr (.inl t)⟩)
  rw [hone,terminal_factor e p bin perm positive first q a y ext t]
  split_ifs <;> simp_all

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
