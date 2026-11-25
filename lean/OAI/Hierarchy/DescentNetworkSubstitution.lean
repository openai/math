import OAI.Computability.BorderVNP.BitVolume
import Mathlib.Tactic

namespace OAI
/-! # Substitution of finite open networks at the sites of an open network

Every old cable connects the gadget port at its source to the gadget port at its destination.
An old loop connects its two oriented ports by one physical cable carrying one shared word.
The original exterior pins keep their names and widths.
-/

namespace Hierarchy.DescentNetworkSubstitution
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section

variable {D d : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)

abbrev Slot (v : N.Site) := {e : N.Edge // N.src e = v} ⊕
  ({e : N.Edge // N.dst e = v} ⊕ {p : P // N.attach p = v})

def slotWidth (v : N.Site) : Slot N v → ℕ
  | .inl e => N.width e.val
  | .inr (.inl e) => N.width e.val
  | .inr (.inr p) => bits p.val

variable (M : (v : N.Site) → Network d (Slot N v) (slotWidth N v))

abbrev Site := Σ v : N.Site, (M v).Site
abbrev Edge := N.Edge ⊕ (Σ v : N.Site, (M v).Edge)

def sourceTap (e : N.Edge) : Site N M := ⟨N.src e, (M _).attach (.inl ⟨e,rfl⟩)⟩
def targetTap (e : N.Edge) : Site N M := ⟨N.dst e, (M _).attach (.inr (.inl ⟨e,rfl⟩))⟩
def pinTap (p : P) : Site N M := ⟨N.attach p, (M _).attach (.inr (.inr ⟨p,rfl⟩))⟩

private theorem sourceTap_at {v : N.Site} (e : {e : N.Edge // N.src e = v}) :
    sourceTap N M e.val = ⟨v, (M v).attach (.inl e)⟩ := by rcases e with ⟨e,rfl⟩; rfl

private theorem targetTap_at {v : N.Site} (e : {e : N.Edge // N.dst e = v}) :
    targetTap N M e.val = ⟨v, (M v).attach (.inr (.inl e))⟩ := by rcases e with ⟨e,rfl⟩; rfl

private theorem pinTap_at {v : N.Site} (p : {p : P // N.attach p = v}) :
    pinTap N M p.val = ⟨v, (M v).attach (.inr (.inr p))⟩ := by rcases p with ⟨p,rfl⟩; rfl

/-- All private gadget cables and each original joining cable are real edges of the substituted network. -/
abbrev network : Network d P bits where
  Site := Site N M
  Edge := Edge N M
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src
    | .inl e => sourceTap N M e
    | .inr ⟨v,e⟩ => ⟨v, (M v).src e⟩
  dst
    | .inl e => targetTap N M e
    | .inr ⟨v,e⟩ => ⟨v, (M v).dst e⟩
  width
    | .inl e => N.width e
    | .inr ⟨v,e⟩ => (M v).width e
  attach := pinTap N M
  position t := (M t.1).position t.2
  in_ball t := (M t.1).in_ball t.2

local notation "Q" => network N M

abbrev Incident (A : Network D P bits) (v : A.Site) := {e : A.Edge // A.src e = v ∨ A.dst e = v}

abbrev Wires (A : Network D P bits) (v : A.Site) := (e : Incident A v) → Fin (A.width e.val) → Bool
abbrev Pins (A : Network D P bits) (v : A.Site) := (p : {p : P // A.attach p = v}) → Fin (bits p.val) → Bool

private def localSlot {v : N.Site} {j : (M v).Site} (wire : Wires Q ⟨v,j⟩) (pin : Pins Q ⟨v,j⟩) :
    (s : Slot N v) → (M v).attach s = j → Fin (slotWidth N v s) → Bool
  | .inl e, h => wire ⟨.inl e.val, Or.inl ((sourceTap_at N M e).trans (congrArg (Sigma.mk v) h))⟩
  | .inr (.inl e), h => wire ⟨.inl e.val, Or.inr ((targetTap_at N M e).trans (congrArg (Sigma.mk v) h))⟩
  | .inr (.inr p), h => pin ⟨p.val, (pinTap_at N M p).trans (congrArg (Sigma.mk v) h)⟩

variable {K : Type*} [CommSemiring K] (T : ∀ v, (M v).Tables K)

/-- A substituted table reads only private cables, joining cables and exterior pins incident to its site. -/
def tables : (Q).Tables K
  | ⟨v,j⟩, wire, pin => T v j (fun e => wire ⟨.inr ⟨v,e.val⟩,
      e.property.imp (congrArg (Sigma.mk v)) (congrArg (Sigma.mk v))⟩)
    (fun s => localSlot N M wire pin s.val s.property)

/-- The old table at a site is the complete local coefficient of its open gadget. -/
def coefficients : N.Tables K := fun v wire pin => (M v).value (T v) (fun
  | .inl e => wire ⟨e.val, Or.inl e.property⟩
  | .inr (.inl e) => wire ⟨e.val, Or.inr e.property⟩
  | .inr (.inr p) => pin p)

def visible (a : N.Assignment) (x : Ports bits) (v : N.Site) : Ports (slotWidth N v)
  | .inl e => a e.val
  | .inr (.inl e) => a e.val
  | .inr (.inr p) => x p.val

/-- Split all joining indices from each gadget's independent internal assignment. -/
def assignmentEquiv : (Q).Assignment ≃ N.Assignment × ((v : N.Site) → (M v).Assignment) where
  toFun a := (fun e => a (.inl e), fun v e => a (.inr ⟨v,e⟩))
  invFun z
    | .inl e => z.1 e
    | .inr ⟨v,e⟩ => z.2 v e
  left_inv a := by funext e; rcases e with e | ⟨v,e⟩ <;> rfl
  right_inv z := by rcases z with ⟨a,b⟩; rfl

omit [CommSemiring K] in
private theorem read_local (a : (Q).Assignment) (x : Ports bits) (v : N.Site) (j : (M v).Site) :
    (Q).read (tables N M T) a x ⟨v,j⟩ = (M v).read (T v) ((assignmentEquiv N M a).2 v)
      (visible N (assignmentEquiv N M a).1 x v) j := by
  apply congrArg (T v j (fun e => a (.inr ⟨v,e.val⟩)))
  funext s
  rcases s with ⟨s,h⟩
  rcases s with e | (e | p) <;> rfl

theorem read_coefficient (a : N.Assignment) (x : Ports bits) (v : N.Site) :
    N.read (coefficients N M T) a x v = (M v).value (T v) (visible N a x v) := by
  unfold Network.read coefficients
  congr 1

/-- For every exterior assignment, evaluating each gadget first gives the full substituted coefficient. -/
theorem value_substitute (x : Ports bits) : (Q).value (tables N M T) x = N.value (coefficients N M T) x := by
  classical
  let weight (a : N.Assignment) (v : N.Site) (b : (M v).Assignment) :=
    ∏ j, (M v).read (T v) b (visible N a x v) j
  have term (c : (Q).Assignment) : (∏ t, (Q).read (tables N M T) c x t) =
      ∏ v, weight (assignmentEquiv N M c).1 v ((assignmentEquiv N M c).2 v) := by
    rw [Fintype.prod_sigma]
    simp only [read_local, weight]
  unfold Network.value
  calc
    _ = ∑ c : (Q).Assignment, ∏ v, weight (assignmentEquiv N M c).1 v ((assignmentEquiv N M c).2 v) :=
      Finset.sum_congr (by ext; simp) fun c _ => term c
    _ = ∑ a : N.Assignment, ∑ b : (v : N.Site) → (M v).Assignment, ∏ v, weight a v (b v) := by
      rw [← Fintype.sum_prod_type', ← (assignmentEquiv N M).sum_comp (fun z => ∏ v, weight z.1 v (z.2 v))]
    _ = _ := by
      apply Finset.sum_congr (by ext; simp)
      intro a _
      rw [← Fintype.prod_sum]
      simp only [read_coefficient, Network.value, weight]

theorem site_count : Fintype.card (Q).Site = ∑ v, Fintype.card (M v).Site := Fintype.card_sigma

theorem edge_count : Fintype.card (Q).Edge = Fintype.card N.Edge + ∑ v, Fintype.card (M v).Edge := by
  change Fintype.card (Edge N M) = _
  rw [Fintype.card_sum, Fintype.card_sigma]

theorem total_width : (∑ e : (Q).Edge, (Q).width e) = (∑ e : N.Edge, N.width e) +
    ∑ v, ∑ e : (M v).Edge, (M v).width e := by
  change (∑ e : Edge N M, (Q).width e) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]

end
end Hierarchy.DescentNetworkSubstitution

end OAI
