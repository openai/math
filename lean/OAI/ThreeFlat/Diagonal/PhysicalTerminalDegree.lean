import OAI.ThreeFlat.Diagonal.TraceTerminalEdges

namespace OAI
/-! # Terminal port degree of repeats of an issued shrink–refresh block -/

namespace ThreeFlat.Diagonal.PhysicalStage
noncomputable section
variable {F : Type} [Field F]

abbrev Program.finalExponent {s : ℕ} (P : Program F s) : ℕ := P.terminalExponent

private theorem degree_recast {d l l' goal : ℕ} (e : l=l') (A : State d l) (r : Run F (e ▸ A : State d l'))
    (ok : ∀ h,(r.terminalLayer h).degree=goal) :
    ∀ h,((Program.recast e A r).terminalLayer h).degree=goal := by cases e;exact ok

private theorem degree_step {d l D L goal : ℕ} {A : State d l}
    (M : Move F A D L) (next : ∀ i,Run F (M.next i))
    (ok : ∀ i h,((next i).terminalLayer h).degree=goal) :
    ∀ h,((Run.step M next).terminalLayer h).degree=goal :=
  fun h => ok h.1 (Run.tailHistory M next h)

attribute [local irreducible] shrinkBinary refreshBinary Program.recastMove Program.recast

set_option maxHeartbeats 850000 in
theorem Program.run_terminalDegree {s : ℕ} (P : Program F s) (rem : ℕ)
    (A : State (2^s) (P.charge+rem)) : ∀ h,((P.run rem A).terminalLayer h).degree=2^P.finalExponent := by
  induction P with
  | done s=>intro h;rfl
  | shrink s t T small tail ih=>
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let X : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let M := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) X
    let next := fun i => tail.run rem (M.next i)
    exact degree_recast (goal:=2^tail.terminalExponent) e A (.step M next)
      (degree_step M next (fun i => ih (M.next i)))
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih=>
    let e := Nat.add_assoc s tail.charge rem
    let X : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let M := recastMove degree (refreshBinary T X hm hh sym rows zero conn)
    let next := fun i => tail.run rem (M.next i)
    exact degree_recast (goal:=2^tail.terminalExponent) e A (.step M next)
      (degree_step M next (fun i => ih (M.next i)))

namespace Block
variable (B : Block F)

theorem finalExponent_repeat (n : ℕ) : (B.repeat n).finalExponent=B.exponent 0 :=
  B.terminalExponent_repeat n

/-- Every completed shrink–refresh block restores its original port degree,
including after transporting the actual trace lane count. -/
theorem terminalDegree_onLanes {lanes n rem : ℕ} (A : State (2^B.exponent 0) lanes)
    (budget : lanes=(B.repeat n).charge+rem)
    (h : (Program.recast budget A ((B.repeat n).run rem (budget ▸ A))).plan.History) :
    ((Program.recast budget A ((B.repeat n).run rem (budget ▸ A))).terminalLayer h).degree=2^B.exponent 0 := by
  exact degree_recast (goal:=2^B.exponent 0) budget A ((B.repeat n).run rem (budget ▸ A))
    (fun history => ((B.repeat n).run_terminalDegree rem (budget ▸ A) history).trans
      (congrArg (2^·) (B.finalExponent_repeat n))) h

end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
