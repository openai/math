import OAI.ThreeFlat.Diagonal.PhysicalProgramWidthCost
import OAI.ThreeFlat.Diagonal.PhysicalReadHistory

namespace OAI
/-! # A uniform width bound along the actual branches of each physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage

noncomputable section
variable {F : Type} [Field F]

def Run.WidthCeiling : {d l : ℕ} → {A : State d l} → Run F A → ℕ → Prop
  | _, _, A, .done _, n => A.maxWidth+1 ≤ n
  | _, _, A, .step _ next, n => A.maxWidth+1 ≤ n ∧ ∀ i, (next i).WidthCeiling n

theorem Run.widthCeiling_mono {d l : ℕ} {A : State d l} (r : Run F A) {n m : ℕ}
    (hn : n ≤ m) (h : r.WidthCeiling n) : r.WidthCeiling m := by
  induction r with
  | done A => exact Nat.le_trans h hn
  | step R next ih => exact ⟨h.1.trans hn, fun i => ih i (h.2 i)⟩

theorem Run.widthCeiling_step {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ i, Run F (R.next i)) (k t : ℕ) (ht : 0 < t) (hk : R.WidthBound k)
    (h : ∀ i, (next i).WidthCeiling (((R.next i).maxWidth+1)*t)) :
    (Run.step R next).WidthCeiling ((A.maxWidth+1)*((1+k)*t)) := by
  constructor
  · exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) ht)
  · intro i
    apply (next i).widthCeiling_mono _ (h i)
    have h1 : (R.next i).maxWidth+1 ≤ (1+k)*(1+A.maxWidth) := by
      rw [Nat.add_mul,one_mul]
      have := hk i
      omega
    calc
      _ ≤ ((1+k)*(1+A.maxWidth))*t := Nat.mul_le_mul_right t h1
      _ = _ := by ring

private theorem ceiling_recast {d l l' : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) (n : ℕ) :
    (Program.recast e A r).WidthCeiling n ↔ r.WidthCeiling n := by cases e; rfl

private theorem width_recastMove {d l D D' L : ℕ} {A : State d l} (e : D=D')
    (R : Move F A D L) {k : ℕ} (h : R.WidthBound k) : (Program.recastMove e R).WidthBound k := by
  cases e
  exact h

theorem State.maxWidth_cast_lanes {d l l' : ℕ} (e : l=l') (A : State d l) :
    (e ▸ A : State d l').maxWidth = A.maxWidth := by cases e; rfl

theorem Program.run_widthCeiling {s : ℕ} (P : Program F s) (rem : ℕ)
    (A : State (2^s) (P.charge+rem)) :
    (P.run rem A).WidthCeiling ((A.maxWidth+1)*P.widthCost) := by
  induction P with
  | done s => change A.maxWidth+1 ≤ (A.maxWidth+1)*1; simp
  | shrink s t T small tail ih =>
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let R := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    change (Program.recast e A (.step R _)).WidthCeiling ((A.maxWidth+1)*((1+shrinkWidthFactor T s)*tail.widthCost))
    apply (ceiling_recast ..).2
    rw [← show B.maxWidth = A.maxWidth from State.maxWidth_cast_lanes e A]
    apply Run.widthCeiling_step R _ _ _ tail.widthCost_pos (shrinkBinary_width T s _ _ _ _ B)
    exact fun i => ih (R.next i)
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    let e := Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let R := refreshBinary T B hm hh sym rows zero conn
    change (Program.recast e A (.step (Program.recastMove degree R) _)).WidthCeiling
      ((A.maxWidth+1)*((1+refreshWidthFactor T)*tail.widthCost))
    apply (ceiling_recast ..).2
    rw [← show B.maxWidth = A.maxWidth from State.maxWidth_cast_lanes e A]
    apply Run.widthCeiling_step _ _ _ _ tail.widthCost_pos
      (width_recastMove degree R (refreshBinary_width T B hm hh sym rows zero conn))
    exact fun i => ih _

theorem Run.widthCeiling_history {d l : ℕ} {A : State d l} (r : Run F A) {N : ℕ}
    (cap : r.WidthCeiling N) (h : r.plan.History) :
    ∀ w ∈ r.readStages (fun X => X.maxWidth) h, w+1 ≤ N := by
  induction r with
  | done A =>
    intro w hw
    have eq : w = A.maxWidth := List.mem_singleton.mp hw
    subst w
    exact cap
  | step R next ih =>
    intro w hw
    rcases List.mem_cons.mp hw with eq | rest
    · subst w; exact cap.1
    · exact ih h.1 (cap.2 h.1) (Run.tailHistory R next h) w rest

theorem Run.widthCeiling_terminal {d l : ℕ} {A : State d l} (r : Run F A) {N : ℕ}
    (cap : r.WidthCeiling N) (h : r.plan.History) :
    r.readTerminal (fun X => X.maxWidth) h + 1 ≤ N := by
  induction r with
  | done A => exact cap
  | step R next ih => exact ih h.1 (cap.2 h.1) (Run.tailHistory R next h)

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
