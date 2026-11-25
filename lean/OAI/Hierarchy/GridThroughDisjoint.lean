import OAI.Hierarchy.GridThroughRoutes

namespace OAI
/-! # Each elementary rail slot has a unique programmed demand -/

namespace Hierarchy.GridThrough.Program
open GridLens
open scoped Classical
noncomputable section

variable {E k n p : ℕ} {width : Fin k → ℕ} (P : GridThrough.Program (Fin E) n p width)

private abbrev PhysicalDemand := P.Edge ⊕ (Cell k n × Catalyst.Wire width)

/-- Recover the consuming demand and its active half from an elementary
transport slot. The controller distinguishes data touches, catalyst passages,
and ordinary through equalities on the same line. -/
private def slotOwner : Fin E × Segment n → PhysicalDemand P × Bool
  | (e, .inl (.inl ())) => (.inl (.inl (e,false)),false)
  | (e, .inl (.inr (.inl t))) => (.inl (.inr (.inl (e,t))),false)
  | (e, .inl (.inr (.inr ()))) => (.inl (.inl (e,true)),false)
  | (e, .inr (t,b)) =>
    if h : P.touch e = some t then
      (.inl (.inr (.inr (.inr (⟨(e,t),h⟩,b)))),false)
    else if h' : P.Selected e t then
      (.inr (P.railCell e t, Classical.choose h'),b)
    else
      (.inl (.inr (.inr (.inl ⟨(e,t),h,h'⟩))),b)

private theorem slotOwner_pass (c : Cell k n) (w : Catalyst.Wire width) (b : Bool) :
    slotOwner P (P.pass c w, .inr (c (P.direction (P.pass c w)),b)) = (.inr (c,w),b) := by
  let e := P.pass c w
  let t := c (P.direction e)
  have line : P.railCell e t = c := P.pass_line c w
  have untouched : P.touch e ≠ some t := P.pass_untouched c w
  have selected : P.Selected e t := ⟨w, by rw [line]⟩
  have found : P.pass (P.railCell e t) (Classical.choose selected) = e := Classical.choose_spec selected
  let chosen : Catalyst.Wire width := Classical.choose selected
  have lineAt : P.pass c chosen = P.pass (P.railCell e t) chosen :=
    congrArg (fun cell => P.pass cell chosen) line.symm
  have wire : Classical.choose selected = w := P.pass_injective c (lineAt.trans found)
  change slotOwner P (e, .inr (t,b)) = _
  simp only [slotOwner, dite_eq_right untouched, dite_eq_left selected]
  rw [wire, line]

private theorem slotOwner_recovers (a : PhysicalDemand P) (b : Bool) {z : Fin E × Segment n}
    (hit : WireRoute.slot (P.physicalRoute a) b = some z) : slotOwner P z = (a,b) := by
  rcases a with edge | ⟨c,w⟩
  · rcases edge with ⟨e,side⟩ | tail
    · cases side <;> cases b <;> simp [physicalRoute, WireRoute.slot] at hit <;> subst z <;> rfl
    · rcases tail with ⟨e,t⟩ | inner
      · cases b <;> simp [physicalRoute, WireRoute.slot] at hit; subst z; rfl
      · rcases inner with ⟨⟨e,t⟩,ht,hs⟩ | ⟨⟨⟨e,t⟩,ht⟩,side⟩
        · change some ((e,.inr (t,b)) : Fin E × Segment n) = some z at hit
          obtain rfl := Option.some.inj hit
          simp [slotOwner, ht, hs]
        · cases b <;> simp [physicalRoute, WireRoute.slot] at hit
          subst z
          simp [slotOwner, ht]
  · change some ((P.pass c w, .inr (c (P.direction (P.pass c w)),b)) : Fin E × Segment n) = some z at hit
    obtain rfl := Option.some.inj hit
    exact slotOwner_pass P c w b

/-- Two charged legs landing on the same rail slot come from the same
native equality or catalyst wire and have the same leg index. -/
theorem physicalRoute_disjoint {i i' : (P.Edge ⊕ (Cell k n × Catalyst.Wire width)) × Bool}
    {z : Fin E × Segment n} (h : WireRoute.slot (P.physicalRoute i.1) i.2 = some z)
    (h' : WireRoute.slot (P.physicalRoute i'.1) i'.2 = some z) : i = i' :=
  (slotOwner_recovers P i.1 i.2 h).symm.trans (slotOwner_recovers P i'.1 i'.2 h')

end
end Hierarchy.GridThrough.Program

end OAI
