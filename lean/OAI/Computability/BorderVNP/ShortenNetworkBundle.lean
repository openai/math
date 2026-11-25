import OAI.Computability.BorderVNP.CrossingProfiles
import OAI.Computability.BorderVNP.ShortenNetworkHistory

/-!
# Inserting a paid crossing at a matched group of cable intervals

At every axis, the chosen old cable intervals contain exactly one terminal
word's worth of bits. Their public order is used at both ends. The wiring below
reads these words at the physical histogram network's terminals, then sews
one hook to each retained old slot. The reversal flag can vary per cable.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing
open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}

/-- A matched group, with a common public order for the bits on both ends of each axis. -/
structure Bundle (N : Network D P bits) (S : Finset N.Edge) (w : ℕ) where
  /-- The canonical crossing direction of a matched interval. -/
  axis : ↥S → Fin D
  /-- Whether the source endpoint hooks to the positive terminal. -/
  positive : ↥S → Bool
  /-- Public concatenation order on all matched interval bits of a direction. -/
  order : ∀ d, (Σ e : {e : ↥S // axis e = d}, Fin (N.width e.val.val)) ≃ Fin w

namespace Bundle

variable {S : Finset N.Edge} {w : ℕ} (b : Bundle N S w)

/-- Canonical terminal to which each old slot is connected. -/
def terminal : N.CutPorts S → Fin D × Bool :=
  Sum.elim (fun e => (b.axis e, b.positive e)) (fun e => (b.axis e, !b.positive e))

private def locatePart (p : Fin D × Bool) (t : Σ e : {e : ↥S // b.axis e = p.1}, Fin (N.width e.val.val)) :
    Σ q : {q : N.CutPorts S // b.terminal q = p}, Fin (N.cutWidths S q.val) := by
  let e := t.1.val
  have hd : b.axis e = p.1 := t.1.property
  by_cases h : b.positive e = p.2
  · exact ⟨⟨.inl e, Prod.ext hd h⟩, t.2⟩
  · have hn : (!b.positive e) = p.2 := by
      cases he : b.positive e <;> cases hp : p.2 <;> simp_all
    exact ⟨⟨.inr e, Prod.ext hd hn⟩, t.2⟩

/-- Locate a particular bit at a canonical terminal among its incident old slots. -/
def locate (p : Fin D × Bool) (k : Fin w) :
    Σ q : {q : N.CutPorts S // b.terminal q = p}, Fin (N.cutWidths S q.val) :=
  b.locatePart p ((b.order p.1).symm k)

/-- Gather old interval words into the ordered words read by the histogram network. -/
def gather (s : Ports (N.cutWidths S)) (p : Fin D × Bool) (k : Fin w) : Bool :=
  let loc := b.locate p k
  s loc.1.val loc.2

/-- Reading the common ordinal at a terminal retrieves the correctly oriented old slot. -/
theorem gather_order (s : Ports (N.cutWidths S)) (e : ↥S) (k : Fin (N.width e.val))
    (side : Bool) :
    b.gather s (b.axis e, side) (b.order (b.axis e) ⟨⟨e, rfl⟩, k⟩) =
      if b.positive e = side then s (.inl e) k else s (.inr e) k := by
  let t : Σ u : {u : ↥S // b.axis u = b.axis e}, Fin (N.width u.val.val) := ⟨⟨e,rfl⟩, k⟩
  let read := fun z : Σ u : {u : ↥S // b.axis u = b.axis e}, Fin (N.width u.val.val) =>
    let loc := b.locatePart (b.axis e, side) z
    s loc.1.val loc.2
  change read ((b.order (b.axis e)).symm ((b.order (b.axis e)) t)) = _
  refine (congrArg read ((b.order (b.axis e)).symm_apply_apply t)).trans ?_
  let readSlot := fun z : Σ q : {q : N.CutPorts S // b.terminal q = (b.axis e, side)},
        Fin (N.cutWidths S q.val) => s z.1.val z.2
  by_cases hs : b.positive e = side
  · rw [ite_eq_left hs]
    have hloc : b.locatePart (b.axis e, side) t = ⟨⟨.inl e, Prod.ext rfl hs⟩, k⟩ := by
      simp [locatePart, t, hs]
    exact congrArg readSlot hloc
  · rw [ite_eq_right hs]
    have hn : (!b.positive e) = side := by cases he : b.positive e <;> cases side <;> simp_all
    have hloc : b.locatePart (b.axis e, side) t = ⟨⟨.inr e, Prod.ext rfl hn⟩, k⟩ := by
      simp [locatePart, t, hs]
    exact congrArg readSlot hloc

/-- Equality of the gathered antipodal words tests exactly the joint equality
on all cut ends, irrespective of the orientation of their intervals. -/
theorem cutEquality_gather {K : Type*} [Field K] (s : Ports (N.cutWidths S)) :
    N.cutEquality S s = antipodalTensor K D w (b.gather s) := by
  have hiff : ((fun e : ↥S => s (.inl e)) = fun e : ↥S => s (.inr e)) ↔
      ∀ i : Fin D, b.gather s (i, false) = b.gather s (i, true) := by
    constructor
    · intro h i
      funext k
      obtain ⟨⟨⟨e, he⟩, t⟩, rfl⟩ := (b.order i).surjective k
      subst i
      have hbit := congrFun (congrFun h e) t
      simp only [gather_order]
      cases b.positive e
      · simpa using hbit
      · simpa using hbit.symm
    · intro h
      funext e k
      have hbit := congrFun (h (b.axis e)) (b.order (b.axis e) ⟨⟨e,rfl⟩, k⟩)
      have eq := (b.gather_order s e k false).symm.trans
        (hbit.trans (b.gather_order s e k true))
      cases he : b.positive e
      · simpa [he] using eq
      · simpa [he] using eq.symm
  unfold Network.cutEquality antipodalTensor
  by_cases h : ∀ i : Fin D, b.gather s (i, false) = b.gather s (i, true)
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h]

/-- Give every selected old slot its own port at the corresponding physical
terminal of the profile network. All its internal edges and tables stay local. -/
def expose (G : Network D (Fin D × Bool) (fun _ => w)) : Network D (N.CutPorts S) (N.cutWidths S) where
  Site := G.Site
  Edge := G.Edge
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := G.src
  dst := G.dst
  width := G.width
  attach := G.attach ∘ b.terminal
  position := G.position
  in_ball := G.in_ball

/-- The terminal table concatenates the words at its attached slots. -/
def exposeTables {K : Type*} (G : Network D (Fin D × Bool) (fun _ => w))
    (table : G.Tables K) : (b.expose G).Tables K := fun v a x =>
  table v a (fun p k =>
    let z := b.locate p.val k
    x ⟨z.1.val, (congrArg G.attach z.1.property).trans p.property⟩ z.2)

/-- Gathering changes only the numbering of the free bits. -/
theorem value_expose {K : Type*} [CommSemiring K] (G : Network D (Fin D × Bool) (fun _ => w))
    (table : G.Tables K) (s : Ports (N.cutWidths S)) :
    (b.expose G).value (b.exposeTables G table) s = G.value table (b.gather s) := rfl

end Bundle

/-- The actual paid identity of Definition 3.1 produces a pack replacement.
Only attained histograms are included, once each. -/
noncomputable def paidReplacement {K : Type*} [Field K] {m j : ℕ} (p : Pack D P bits K)
    (e : PaidIdentity K D m) (first : Fin D × Bool) (S : Finset p.layout.Edge)
    (b : Bundle p.layout S (j*m)) : Replacement p := by
  let H := Finset.univ.image (@Profile.histogram e.count j)
  let index := (Fintype.equivFin ↥H).symm
  exact {
    cables := S
    count := Fintype.card ↥H
    profile := fun i => b.expose (e.profile j (index i).val)
    entry := fun i => b.exposeTables _ (e.profileTables j (index i).val first)
    joint := fun s => by
      rw [b.cutEquality_gather]
      simp only [Bundle.value_expose]
      rw [index.sum_comp (fun h => (e.profile j h.val).value (e.profileTables j h.val first)
        (b.gather s))]
      exact (e.profile_sum j first (b.gather s)).symm.trans (Finset.sum_coe_sort H _).symm }

/-- Every matched group of intervals can be replaced in any pack, with no
algebraic hypothesis beyond the paid crossing identity itself. -/
theorem paidReplacement_sum {K : Type*} [Field K] {m j : ℕ} (p : Pack D P bits K)
    (e : PaidIdentity K D m) (first : Fin D × Bool) (S : Finset p.layout.Edge)
    (b : Bundle p.layout S (j*m)) (x : Ports bits) :
    p.tensor x = ∑ i, ((paidReplacement p e first S b).branch i).tensor x :=
  (paidReplacement p e first S b).sum_branches x

end Shortening

end BorderVNP
end Computability
end OAI
