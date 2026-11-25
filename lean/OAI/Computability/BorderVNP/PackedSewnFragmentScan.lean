import OAI.Computability.BorderVNP.PackedSewnFragmentPairSpec

/-! # Sparse right-to-left coalescing of adjacent physical intervals

Only the first two slots of a suffix are updated. The whole older suffix
passes through on its existing wires, so each new position charges one
two-fragment circuit regardless of the number of physical lanes it spans.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open VPVNP.VerifierNetwork

variable {w n : ℕ} (p : Frame (Bool × Column w) (Bool × Column w))
local notation3 "Joint" => Pin (n+2) w ⊕ Pin (n+1) w

private def pairInput (z : Bool × Column w) : Joint :=
  if z.1 then .inr (0,z.2) else .inl (0,z.2)

private def deliver (z : Pin (n+2) w) : Joint ⊕ (Bool × Column w) :=
  Fin.cases (.inr (false,z.2))
    (fun i => Fin.cases (.inr (true,z.2)) (fun k => .inl (.inr (k.succ,z.2))) i) z.1

/-- Add one raw fragment at the left of a previously coalesced physical suffix. -/
noncomputable def advance (prior : Frame (Pin (n+1) w) (Pin (n+1) w)) :
    Frame (Pin (n+2) w) (Pin (n+2) w) :=
  let past := prior.subst (Frame.initial (fun z : Pin (n+1) w => (z.1.succ,z.2)))
  let edge := p.subst (Frame.initial (pairInput (n := n)))
  (edge.withInput.select deliver).subst past.withInput

/-- Each physical sparse position charges one pair of interval headers. -/
noncomputable def scan : (n : ℕ) → Frame (Pin n w) (Pin n w)
  | 0 => Frame.initial id
  | 1 => Frame.initial id
  | n+2 => advance p (scan (n+1))

/-- The coalescing pass uses at most one local pair circuit per reserved fragment. -/
theorem scan_size (n : ℕ) : (scan p n).size ≤ n*p.size := by
  induction n with
  | zero => simp [scan]
  | succ n ih =>
    cases n with
    | zero => simp [scan]
    | succ n =>
      calc
        _ = (scan p (n+1)).size+p.size := by simp only [scan,advance,Frame.subst_size,Frame.initial_size,
          Frame.select_size,Frame.withInput_size,Nat.zero_add]
        _ ≤ (n+1)*p.size+p.size := Nat.add_le_add_right ih _
        _ = _ := (Nat.succ_mul (n+1) p.size).symm

/-- Remove the leftmost physical slot by fixed input wiring. -/
def tail (x : Pin (n+1) w → Bool) : Pin n w → Bool := fun z => x (z.1.succ,z.2)

/-- The decoded chronological input splits at the first reserved slot. -/
theorem list_cons (x : Pin (n+1) w → Bool) :
    list x = (read (fun j => x (0,j))).toList ++ list (tail x) := by
  simp only [list,List.finRange_succ,List.filterMap_cons,List.filterMap_map,Function.comp_def]
  cases h : x (0,.inl false) <;> simp [active,read,h,tail,parse] <;> rfl

private def input (x : Pin (n+2) w → Bool) (y : Pin (n+1) w → Bool) : Bool × Column w → Bool :=
  fun z => if z.1 then y (0,z.2) else x (0,z.2)

private theorem advance_bit (prior : Frame (Pin (n+1) w) (Pin (n+1) w)) (x : Pin (n+2) w → Bool) :
    let y := prior.eval (tail x)
    let joined := p.eval (input x y)
    ∀ i : Fin (n+2), ∀ j, (advance p prior).eval x (i,j) =
      Fin.cases (joined (false,j)) (fun k => Fin.cases (joined (true,j)) (fun r => y (r.succ,j)) k) i := by
  intro y joined i j
  let f := prior.subst (Frame.initial (fun z : Pin (n+1) w => (z.1.succ,z.2)))
  have prev (r : Pin (n+1) w) : f.eval x r = y r := by
    have eqn : (Frame.initial (fun z : Pin (n+1) w => (z.1.succ,z.2))).eval x = tail x :=
      funext (Frame.initial_eval _ _)
    exact (Frame.subst_eval ..).trans (congrArg (fun a => prior.eval a r) eqn)
  have dat : (Frame.initial (pairInput (w := w) (n := n))).eval (f.withInput.eval x) = input x y := by
    funext z
    rcases z with ⟨b,j⟩
    cases b <;> simp [pairInput,input,Frame.initial_eval,prev]
  have bit (b : Bool) : (p.subst (Frame.initial (pairInput (n := n)))).eval (f.withInput.eval x) (b,j) =
      joined (b,j) := by rw [Frame.subst_eval,dat]
  rw [advance,Frame.subst_eval]
  change ((p.subst (Frame.initial (pairInput (n := n)))).withInput.select deliver).eval (f.withInput.eval x) (i,j) = _
  induction i using Fin.cases with
  | zero => simpa only [deliver,Fin.cases_zero,Frame.select_eval,Frame.withInput_eval_inr] using bit false
  | succ i =>
    induction i using Fin.cases with
    | zero => simpa only [deliver,Fin.cases_succ,Fin.cases_zero,Frame.select_eval,Frame.withInput_eval_inr] using bit true
    | succ r => simpa only [deliver,Fin.cases_succ,Frame.select_eval,Frame.withInput_eval_inl,Frame.withInput_eval_inr] using prev (r.succ,j)

/-- True sparse rows occupy a prefix of the sorted physical array. -/
def Compact {n w : ℕ} (x : Pin n w → Bool) : Prop :=
  ∀ i j : Fin n, i ≤ j → active x j = true → active x i = true

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
