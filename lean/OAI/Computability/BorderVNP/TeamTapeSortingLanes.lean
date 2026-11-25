import OAI.Computability.BorderVNP.TeamTapeSorting

/-! # Checking two virtual sorting blocks on one processor

The primary block always runs. On processors assigned a second, initially empty block,
an accepting halt of the first checker transfers to the second. A rejection terminates
immediately. The two sets of stacks are disjoint, so both terminal decisions are checked
on the same raw physical assignment, and the two clocks add.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeSorting.Lanes

open VPVNP RAMTape

private def onAccept {K Q : Type} (r : Routine K Q) : Routine K Q where
  entry := r.entry
  code q := match r.code q with
    | .halt true => .goto none
    | op => op

private theorem return_count {K Q : Type} [DecidableEq K] (r : Routine K Q)
    (n m weight : ℕ) (q : Option Q) (s : Stacks K) (hc : r.AllStopsFrom (fun _ _ => False) n q s)
    (c : ℕ → Stacks K → ℕ) (hnext : ∀ t ≥ m, ∀ z, c t z = weight) :
    (onAccept r).countFrom c (n+m) q s = r.countFrom (fun _ _ => 0) n q s * weight := by
  induction n generalizing q s with
  | zero => cases q <;> exact hc.elim
  | succ n ih =>
    cases q with
    | none => exact hc.elim
    | some q =>
      rw [Nat.succ_add, Routine.countFrom, Routine.countFrom]
      simp only [Routine.AllStopsFrom] at hc
      cases op : r.code q with
      | halt b => cases b <;> simp [onAccept, op, hnext _ (Nat.le_add_left ..)]
      | choose l u =>
        simp only [onAccept, op] at hc ⊢
        exact (congrArg₂ (·+·) (ih _ _ hc.1) (ih _ _ hc.2)).trans (Nat.add_mul ..).symm
      | _ => simp only [onAccept, op] at hc ⊢; exact ih _ _ hc

private theorem return_stops {K Q : Type} [DecidableEq K] (r : Routine K Q)
    (n m : ℕ) (q : Option Q) (s : Stacks K) (hc : r.AllStopsFrom (fun _ _ => False) n q s)
    (c : ℕ → Stacks K → Prop) (hnext : ∀ t ≥ m, ∀ z, c t z) :
    (onAccept r).AllStopsFrom c (n+m) q s := by
  induction n generalizing q s with
  | zero => cases q <;> exact hc.elim
  | succ n ih =>
    cases q with
    | none => exact hc.elim
    | some q =>
      rw [Nat.succ_add, Routine.AllStopsFrom]
      simp only [Routine.AllStopsFrom] at hc
      cases op : r.code q with
      | halt b => cases b <;> simp [onAccept, op, hnext _ (Nat.le_add_left ..)]
      | choose l u => simp only [onAccept, op] at hc ⊢; exact ⟨ih _ _ hc.1, ih _ _ hc.2⟩
      | _ => simp only [onAccept, op] at hc ⊢; exact ih _ _ hc

variable {K : Type} [DecidableEq K]

/-- Sequential conjunction of two closed finite checkers on distinct banks, with the
accepting first checker handing off normally to the second. -/
def both (r : FiniteRoutine K) : FiniteRoutine (Bool × K) :=
  ((FiniteRoutine.ofRoutine (onAccept r.body)).onPorts (Prod.mk false)).followedBy
    (r.onPorts (Prod.mk true))

/-- On an owner of two virtual blocks the two observed path counts multiply, and all
branches finish within the sum of the clocks. Counts are uniform over caller continuations. -/
theorem both_spec (r : FiniteRoutine K) (s : Stacks (Bool × K)) (n m a b : ℕ)
    (hfirst : (∀ c, r.body.count c n (s ∘ Prod.mk false) = a) ∧
      (∀ c, r.body.AllStops c n (s ∘ Prod.mk false)))
    (hsecond : ∀ t ≥ m, (∀ c, r.body.count c t (s ∘ Prod.mk true) = b) ∧
      (∀ c, r.body.AllStops c t (s ∘ Prod.mk true))) :
    (∀ c, (both r).body.count c (n+m) s = a*b) ∧ (∀ c, (both r).body.AllStops c (n+m) s) := by
  have inj (flag : Bool) : Function.Injective (Prod.mk flag : K → Bool × K) := fun _ _ h => (Prod.mk.inj h).2
  have rest (z : Stacks K) : installStacks (Prod.mk false) s z ∘ Prod.mk true = s ∘ Prod.mk true := by
    funext k
    exact installStacks_outside _ _ (by simp)
  constructor
  · intro c
    change (((FiniteRoutine.ofRoutine (onAccept r.body)).onPorts (Prod.mk false)).body.followedBy
      (r.onPorts (Prod.mk true)).body).count c (n+m) s = _
    rw [Routine.count_followedBy, FiniteRoutine.count_onPorts _ _ (inj false)]
    exact (return_count r.body n m b _ _ (hfirst.2 _) _ (fun t ht z => by
      rw [FiniteRoutine.count_onPorts _ _ (inj true), rest]
      exact (hsecond t ht).1 _)).trans (congrArg (· * b) (hfirst.1 _))
  · intro c
    change (((FiniteRoutine.ofRoutine (onAccept r.body)).onPorts (Prod.mk false)).body.followedBy
      (r.onPorts (Prod.mk true)).body).AllStops c (n+m) s
    rw [Routine.allStops_followedBy, FiniteRoutine.allStops_onPorts _ _ (inj false)]
    apply return_stops r.body n m _ _ (hfirst.2 _)
    intro t ht z
    rw [FiniteRoutine.allStops_onPorts _ _ (inj true), rest]
    exact (hsecond t ht).2 _

attribute [local instance] TeamTapeSorting.portDecidableEq

/-- In particular the paired read/write checker validates both sorted blocks, including
the extra block at a non-power-of-two team size, in twice the single-block time. -/
theorem pairedSites {d e w : ℕ} (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
    (fields : TeamTapeSorting.Fields d e w) (v₀ v₁ : BurstRAM.Word d)
    (x : ℕ → Option (RAMSerialization.WordRecord w)) (t : ℕ) (ht : siteBudget d e w ≤ t) :
    let s : Stacks (Bool × TeamTapeSorting.Port) := fun p => siteInput hw fields (if p.1 then v₁ else v₀) x p.2
    let ok (v : BurstRAM.Word d) := FormatAt hw hc fields v ∧
      BurstRAM.MemoryAt (memory hw hc fields) v (RAMSort.block (2+e) v.val (wire x))
    (∀ c, (both TeamTapeSorting.program).body.count c (t+t) s =
        @ite ℕ (ok v₀ ∧ ok v₁) (Classical.propDecidable _) 1 0) ∧
      (∀ c, (both TeamTapeSorting.program).body.AllStops c (t+t) s) := by
  classical
  intro s ok
  have h₀ := program_spec hw hc fields v₀ x t ht
  have h₁ (u) (hu : t ≤ u) := program_spec hw hc fields v₁ x u (ht.trans hu)
  obtain ⟨h, stops⟩ := both_spec TeamTapeSorting.program s t t _ _ h₀ h₁
  refine ⟨fun c => (h c).trans ?_, stops⟩
  change (@ite ℕ (ok v₀) (Classical.propDecidable _) 1 0) *
    (@ite ℕ (ok v₁) (Classical.propDecidable _) 1 0) = _
  by_cases h₀ : ok v₀ <;> by_cases h₁ : ok v₁ <;> simp [h₀, h₁]

end TeamTapeSorting.Lanes

end BorderVNP
end Computability
end OAI
