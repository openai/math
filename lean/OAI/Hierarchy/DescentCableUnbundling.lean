import OAI.Computability.BorderVNP.BitVolume
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace OAI
/-! # Split marked physical cables into parallel cables of a common width

A source table and a destination table use the same row and bit order. Each
unmarked cable remains one cable at its original width. An empty marked cable
has a unique empty word and contributes no new cable.
-/

namespace Hierarchy.DescentCableUnbundling

open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (core : Finset N.Edge) (m : N.Edge → ℕ) (q : ℕ)

abbrev Row := Σ e : {e : N.Edge // e ∈ core}, Fin (m e.val)

abbrev Edge := {e : N.Edge // e ∉ core} ⊕ Row N core m

def original : Edge N core m → N.Edge := Sum.elim Subtype.val (fun t => t.1.val)

abbrev network : Network D P bits where
  Site := N.Site
  Edge := Edge N core m
  finiteSite := N.finiteSite
  finiteEdge := inferInstance
  src e := N.src (original N core m e)
  dst e := N.dst (original N core m e)
  width := Sum.elim (fun e => N.width e.val) (fun _ => q)
  attach := N.attach
  position := N.position
  in_ball := N.in_ball

local notation "Q" => network N core m q

/-- Bit `(i,j)` is the `j`-th bit of the `i`-th new cable. -/
def splitWord {w a b : ℕ} (h : w = a*b) : (Fin w → Bool) ≃ (Fin a → Fin b → Bool) :=
  (Equiv.arrowCongr ((finCongr h).trans finProdFinEquiv.symm) (Equiv.refl Bool)).trans
    (Equiv.curry _ _ _)

variable (fit : ∀ e ∈ core, N.width e = m e*q)

private def splitAssignment (a : N.Assignment) : (Q).Assignment
  | .inl e => a e.val
  | .inr ⟨e,i⟩ => splitWord (fit e.val e.property) (a e.val) i

private def joinAssignment (z : (Q).Assignment) : N.Assignment := fun e =>
  if h : e ∈ core then (splitWord (fit e h)).symm (fun i => z (.inr ⟨⟨e,h⟩,i⟩))
  else z (.inl ⟨e,h⟩)

private theorem join_unmarked (z : (Q).Assignment) (e : N.Edge) (he : e ∉ core) :
    joinAssignment N core m q fit z e = z (.inl ⟨e,he⟩) := by
  unfold joinAssignment
  exact dite_eq_right he

private theorem join_marked (z : (Q).Assignment) (e : N.Edge) (he : e ∈ core) :
    joinAssignment N core m q fit z e = (splitWord (fit e he)).symm (fun i => z (.inr ⟨⟨e,he⟩,i⟩)) := by
  unfold joinAssignment
  exact dite_eq_left he

/-- Restoring a word at each original edge is inverse to splitting all marked words. -/
def assignmentEquiv : N.Assignment ≃ (Q).Assignment where
  toFun := splitAssignment N core m q fit
  invFun := joinAssignment N core m q fit
  left_inv a := by
    funext e
    by_cases h : e ∈ core <;> simp [joinAssignment, splitAssignment, h]
  right_inv z := by
    funext t
    rcases t with ⟨e,he⟩ | ⟨⟨e,he⟩,i⟩
    · exact join_unmarked N core m q fit z e he
    · change splitWord (fit e he) (joinAssignment N core m q fit z e) i = _
      rw [join_marked N core m q fit z e he]
      exact congrFun ((splitWord (fit e he)).apply_symm_apply (fun r => z (.inr ⟨⟨e,he⟩,r⟩))) i

variable {F : Type*} [CommSemiring F]

/-- Every local argument is rebuilt from lanes incident to that same site. -/
def tables (T : N.Tables F) : (Q).Tables F := fun v read pins => T v (fun e =>
  if h : e.val ∈ core then (splitWord (fit e.val h)).symm (fun i =>
    read ⟨.inr ⟨⟨e.val,h⟩,i⟩, e.property⟩)
  else read ⟨.inl ⟨e.val,h⟩, e.property⟩) pins

theorem value_eq (T : N.Tables F) (x : Ports bits) :
    (Q).value (tables N core m q fit T) x = N.value T x := by
  classical
  unfold Network.value
  let f := fun a : N.Assignment => ∏ v, N.read T a x v
  let g := fun z : (Q).Assignment => ∏ v, (Q).read (tables N core m q fit T) z x v
  have h : ∀ a, f a = g (assignmentEquiv N core m q fit a) := by
    intro a
    apply Finset.prod_congr (by ext; simp)
    intro v _
    symm
    unfold Network.read tables
    congr 1
    funext e
    by_cases he : e.val ∈ core <;> simp [assignmentEquiv, splitAssignment, he]
  calc
    _ = ∑ z, g z := Finset.sum_congr (by ext; simp) (fun _ _ => Finset.prod_congr (by ext; simp) (fun _ _ => rfl))
    _ = ∑ a, f a := (Fintype.sum_equiv (assignmentEquiv N core m q fit) f g h).symm
    _ = _ := Finset.sum_congr (by ext; simp) (fun _ _ => Finset.prod_congr (by ext; simp) (fun _ _ => rfl))

/-- Each marked cable is one actual row of an original marked edge. -/
def nextCore : Finset (Q).Edge := Finset.univ.map Function.Embedding.inr

/-- A cable is marked precisely when the original cable at its two endpoints was marked. -/
theorem mem_nextCore (e : (Q).Edge) :
    e ∈ nextCore N core m q ↔ original N core m e ∈ core := by
  rcases e with e | ⟨e,i⟩ <;> simp [nextCore, Finset.mem_map, original, e.property]

theorem uniform (e : (Q).Edge) (he : e ∈ nextCore N core m q) : (Q).width e = q := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp he
  rfl

include fit in
theorem core_width : (∑ e ∈ nextCore N core m q, (Q).width e) = ∑ e ∈ core, N.width e := by
  rw [nextCore, Finset.sum_map]
  change (∑ _t : Row N core m, q) = _
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ e : {e : N.Edge // e ∈ core}, N.width e.val := by
      apply Finset.sum_congr rfl
      intro e _
      simp [fit e.val e.property]
    _ = _ := (Finset.sum_subtype core (fun _ => Iff.rfl) N.width).symm

private theorem unmarked : (nextCore N core m q)ᶜ = Finset.univ.map Function.Embedding.inl := by
  classical
  ext e
  rcases e with e | t <;> simp [nextCore, Finset.mem_map]

theorem tether_width : (∑ e ∈ (nextCore N core m q)ᶜ, (Q).width e) = ∑ e ∈ coreᶜ, N.width e := by
  rw [unmarked, Finset.sum_map]
  change (∑ e : {e : N.Edge // e ∉ core}, N.width e.val) = _
  exact (Finset.sum_subtype coreᶜ (fun _ => Finset.mem_compl) N.width).symm

include fit in
theorem total_width : (∑ e : (Q).Edge, (Q).width e) = ∑ e : N.Edge, N.width e := by
  rw [← Finset.sum_compl_add_sum (nextCore N core m q) (Q).width, tether_width, core_width N core m q fit]
  exact Finset.sum_compl_add_sum core N.width

/-- The physical cable count counts rows, while the total number of carried bits is unchanged. -/
theorem edge_card : Fintype.card (Q).Edge = coreᶜ.card + ∑ e ∈ core, m e := by
  change Fintype.card (Edge N core m) = _
  rw [Fintype.card_sum, Fintype.card_sigma]
  have other : Fintype.card {e : N.Edge // e ∉ core} = coreᶜ.card :=
    Fintype.card_of_subtype coreᶜ (fun _ => Finset.mem_compl)
  rw [other]
  simp only [Fintype.card_fin]
  exact congrArg _ (Finset.sum_subtype core (fun _ => Iff.rfl) m).symm

end
end Hierarchy.DescentCableUnbundling

end OAI
