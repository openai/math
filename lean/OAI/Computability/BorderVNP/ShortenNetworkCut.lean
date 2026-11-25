import OAI.Computability.BorderVNP.ShortenNetworkSew

/-!
# Cutting charged cables and inserting profile networks

A selected cable gives two new slots, one at each of its old endpoint sites.
Imposing equality on the slots recovers the original contraction. Consequently
a sum that realizes the joint wire equality may be inserted even when the
selected cables previously carried selector bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)

/-- Each selected cable has one exposed source slot and one exposed destination slot. -/
abbrev CutPorts (S : Finset N.Edge) := ↥S ⊕ ↥S

/-- Both exposed slots have the original cable's full bit width. -/
abbrev cutWidths (S : Finset N.Edge) : N.CutPorts S → ℕ :=
  Sum.elim (fun e => N.width e.val) (fun e => N.width e.val)

/-- The exterior of the selected cables. It keeps every old site, other
cable, external port, and location. -/
noncomputable def cut (S : Finset N.Edge) :
    Network D (P ⊕ N.CutPorts S) (Sum.elim bits (N.cutWidths S)) where
  Site := N.Site
  Edge := {e : N.Edge // e ∉ S}
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src e := N.src e.val
  dst e := N.dst e.val
  width e := N.width e.val
  attach := Sum.elim N.attach (Sum.elim (fun e => N.src e.val) (fun e => N.dst e.val))
  position := N.position
  in_ball := N.in_ball

variable {R : Type*} [CommSemiring R]

/-- The local tables in the exterior. At a loop, the old table reads one
index; the equality of the two new slots enforces their common value. -/
noncomputable def cutTables (S : Finset N.Edge) (table : N.Tables R) : (N.cut S).Tables R :=
  fun v a x => table v (fun e =>
    if h : e.val ∈ S then
      if hs : N.src e.val = v then x ⟨.inr (.inl ⟨e.val, h⟩), hs⟩
      else x ⟨.inr (.inr ⟨e.val, h⟩), e.property.resolve_left hs⟩
    else a ⟨⟨e.val, h⟩, e.property⟩) (fun p => x ⟨.inl p.val, p.property⟩)

/-- The joint equality tensor on the cut ends, including the empty cut. -/
noncomputable def cutEquality (S : Finset N.Edge) (s : Ports (N.cutWidths S)) : R :=
  if (fun e : ↥S => s (.inl e)) = (fun e : ↥S => s (.inr e)) then 1 else 0

private def doubled (S : Finset N.Edge) (a : ∀ e : ↥S, Fin (N.width e.val) → Bool) :
    Ports (N.cutWidths S) := joinedPorts a a

private theorem sum_cutEquality (S : Finset N.Edge) (f : Ports (N.cutWidths S) → R) :
    (∑ s, f s * N.cutEquality S s) = ∑ a, f (N.doubled S a) := by
  let half := (e : ↥S) → Fin (N.width e.val) → Bool
  let split : Ports (N.cutWidths S) ≃ half × half :=
    Equiv.sumPiEquivProdPi (fun i : N.CutPorts S => Fin (N.cutWidths S i) → Bool)
  calc
    _ = ∑ q, f (split.symm q) * (if q.1 = q.2 then 1 else 0) :=
      Fintype.sum_equiv split _ _ fun s => by
        rw [split.symm_apply_apply]
        have hcond : ((fun e : ↥S => s (.inl e)) = (fun e : ↥S => s (.inr e))) ↔
            (split s).1 = (split s).2 := Iff.rfl
        by_cases h : (split s).1 = (split s).2
        · simp only [cutEquality, ite_eq_left h, ite_eq_left (hcond.mpr h)]
        · simp only [cutEquality, ite_eq_right h, ite_eq_right (fun he => h (hcond.mp he))]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single a]
      · simp
        apply congrArg f
        funext i
        cases i <;> rfl
      · intro b _ hne
        simp [Ne.symm hne]
      · simp

/-- Equality on all selected cable ends contracts to exactly one shared
assignment per cable in the original graph. -/
theorem value_cut (S : Finset N.Edge) (table : N.Tables R) (x : Ports bits) :
    N.value table x =
      ∑ s, (N.cut S).value (N.cutTables S table) (joinedPorts x s) * N.cutEquality S s := by
  rw [N.sum_cutEquality S]
  let split : N.Assignment ≃ (∀ e : ↥S, Fin (N.width e.val) → Bool) × (N.cut S).Assignment :=
    Equiv.piEquivPiSubtypeProd (fun e : N.Edge => e ∈ S) (fun e => Fin (N.width e) → Bool)
  let weight := fun (a : (∀ e : ↥S, Fin (N.width e.val) → Bool) × (N.cut S).Assignment) =>
    ∏ v, (N.cut S).read (N.cutTables S table) a.2 (joinedPorts x (N.doubled S a.1)) v
  calc
    _ = ∑ a, weight a := by
      unfold Network.value
      refine Fintype.sum_equiv split _ weight ?_
      intro a
      apply Finset.prod_congr rfl
      intro v _
      change table v _ _ = table v _ _
      congr 1
      funext e
      by_cases he : e.val ∈ S
      · by_cases hs : N.src e.val = v <;> simp [he, hs, joinedPorts, doubled, split] <;> rfl
      · simp [he, split]; rfl
    _ = _ := Fintype.sum_prod_type weight

/-- Replacing any finite set of cables of a finite pack by a joint profile
identity preserves its full tensor on every old external assignment. -/
theorem value_replace {J : Type*} [Fintype J] (S : Finset N.Edge) (table : N.Tables R)
    (profile : J → Network D (N.CutPorts S) (N.cutWidths S))
    (entry : ∀ j, (profile j).Tables R)
    (identity : ∀ s, N.cutEquality S s = ∑ j, (profile j).value (entry j) s)
    (x : Ports bits) :
    N.value table x = ∑ j, ((N.cut S).sew (profile j)).value
      ((N.cut S).sewTables (profile j) (N.cutTables S table) (entry j)) x := by
  rw [N.value_cut S table]
  simp only [identity, value_sew, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext j
  congr 1
  exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

end Crossing.Network

end BorderVNP
end Computability
end OAI
