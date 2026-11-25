import OAI.Computability.BorderVNP.TeamTapeInputRouteVerified
import OAI.Computability.BorderVNP.TeamTapeSortingLanes

/-! # Validating the occupied physical sorter banks selected by the router

The saved public presence bit selects the ordinary checker or the conjunction of two
virtual-site checkers. Each canonicality guard has separate scratch; the bank of each
post-pass is wired directly to the router output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputRoute.Verify

open VPVNP BurstRAM RAMTape RAMLayout RAMSerialization TeamTapeSorting

attribute [local instance] TeamTapeSorting.portDecidableEq

/-- Guard scratch for the two virtual blocks alongside the router's actual stacks. -/
abbrev Port := (Bool × Sorter.Port) ⊕ TeamTapeInputRoute.Port

/-- The canonicality guard and sorter on each lane share the physical bank prepared by
the owner, with disjoint scratch. -/
def lanePort (b : Bool) : TeamTapeSorting.Port → Port
  | .inl k => .inl (b,k)
  | .inr k => .inr (.post b k)

private theorem lane_inj (b : Bool) : Function.Injective (lanePort b) := by
  rintro (k | k) (j | j) h <;> simp_all [lanePort]

private def lanePair (p : Bool × TeamTapeSorting.Port) := lanePort p.1 p.2

private theorem pair_inj : Function.Injective lanePair := by
  rintro ⟨b, k | k⟩ ⟨c, j | j⟩ h <;> simp_all [lanePair,lanePort]

private abbrev presence : Port := .inr secondFlag
private def one := TeamTapeSorting.program.onPorts (lanePort false)
private def two := (Lanes.both TeamTapeSorting.program).onPorts lanePair

/-- One closed checker on the primary bank, or two closed checks linked by the accepting
halt of the first. The selector is the actual bit retained by the metadata parser. -/
def terminal : FiniteRoutine Port := .ofRoutine
  (Routine.popCase presence (Routine.halt false) one.body two.body)

private theorem stops_choice {K Q R : Type} [DecidableEq K] (k : K) (low : Routine K Q)
    (high : Routine K R) (b : Bool) (s : Stacks K) (rest : List Bool) (h : s k = b :: rest)
    (c : ℕ → Stacks K → Prop) (t : ℕ) :
    (Routine.popCase k (Routine.halt false) low high).AllStops c (t+1) s ↔
      if b then high.AllStops c t (Function.update s k rest)
      else low.AllStops c t (Function.update s k rest) := by
  let outer := Routine.popCase k (Routine.halt false) low high
  change outer.AllStopsFrom c (t+1) (some outer.entry) s ↔ _
  rw [Routine.AllStopsFrom]
  cases b with
  | false =>
    simpa only [outer,Routine.popCase,h,List.head?_cons,List.tail_cons,Function.comp_apply,
      Option.elim_some,Routine.allStopsFrom_none,Bool.false_eq_true,ite_false] using
      Routine.allStopsFrom_install outer low (Sum.inr ∘ Sum.inr ∘ Sum.inl) none (fun _ => rfl)
        c t (some low.entry) (Function.update s k rest)
  | true =>
    simpa only [outer,Routine.popCase,h,List.head?_cons,List.tail_cons,Function.comp_apply,
      Option.elim_some,Routine.allStopsFrom_none,ite_true] using
      Routine.allStopsFrom_install outer high (Sum.inr ∘ Sum.inr ∘ Sum.inr) none (fun _ => rfl)
        c t (some high.entry) (Function.update s k rest)

variable {d e w : ℕ}

/-- Local message formatting and memory consistency at one virtual block. -/
def valid (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w) (a : Fields d e w)
    (x : ℕ → Option (WordRecord w)) (v : Word d) : Prop :=
  FormatAt hw hc a v ∧ MemoryAt (memory hw hc a) v (RAMSort.block (2+e) v.val (wire x))

/-- The conjunction of the checks on precisely the virtual blocks of the real owner. -/
def ownerValid (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w) (a : Fields d e w)
    (x : ℕ → Option (WordRecord w)) (v : Word d) (other : Option (Word d)) : Prop :=
  valid hw hc a x v ∧ ∀ u, other = some u → valid hw hc a x u

/-- For every clock above the two-site budget the branch selected by the public flag
checks exactly the owner's occupied banks. Every branch halts. -/
theorem terminal_spec (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w) (a : Fields d e w)
    (x : ℕ → Option (WordRecord w)) (v : Word d) (other : Option (Word d))
    (s : Stacks Port) (tail : List Bool) (hflag : s presence = other.isSome :: tail)
    (hfirst : s ∘ lanePort false = siteInput hw a v x)
    (hsecond : ∀ u, other = some u → s ∘ lanePort true = siteInput hw a u x)
    (t : ℕ) (ht : 2*siteBudget d e w+1 ≤ t) :
    (∀ c, terminal.body.count c t s =
      @ite ℕ (ownerValid hw hc a x v other) (Classical.propDecidable _) 1 0) ∧
    ∀ c, terminal.body.AllStops c t s := by
  classical
  let n := t-1
  let next := Function.update s presence tail
  have he : t = n+1 := by dsimp [n]; omega
  have hn : siteBudget d e w ≤ n := by dsimp [n]; omega
  have eq (b : Bool) : next ∘ lanePort b = s ∘ lanePort b := by
    funext k; cases k <;> simp [next,lanePort]
  cases other with
  | none =>
    have hr := program_spec hw hc a v x n hn
    have ec (c) : one.body.count c n next =
        @ite ℕ (valid hw hc a x v) (Classical.propDecidable _) 1 0 := by
      rw [one, FiniteRoutine.count_onPorts _ _ (lane_inj false), eq, hfirst]
      exact hr.1 _
    have es (c) : one.body.AllStops c n next := by
      rw [one, FiniteRoutine.allStops_onPorts _ _ (lane_inj false), eq, hfirst]; exact hr.2 _
    constructor
    · intro c
      change (Routine.popCase presence (Routine.halt false) one.body two.body).count c t s = _
      rw [he, Routine.count_popCase, hflag]
      simpa [ownerValid] using ec c
    · intro c
      rw [he]
      exact (stops_choice presence one.body two.body false s tail hflag c n).mpr (es c)
  | some u =>
    let k := siteBudget d e w
    let m := n-k
    have hm : k ≤ m := by dsimp [m,k,n]; omega
    have hk : n = k+m := by dsimp [m,k]; omega
    let bank := next ∘ lanePair
    have hi₀ : bank ∘ Prod.mk false = siteInput hw a v x := (eq false).trans hfirst
    have hi₁ : bank ∘ Prod.mk true = siteInput hw a u x := (eq true).trans (hsecond u rfl)
    let I (p : Word d) := @ite ℕ (valid hw hc a x p) (Classical.propDecidable _) 1 0
    have first : (∀ c, TeamTapeSorting.program.body.count c k (bank ∘ Prod.mk false) = I v) ∧
        ∀ c, TeamTapeSorting.program.body.AllStops c k (bank ∘ Prod.mk false) := by
      rw [hi₀]; exact program_spec hw hc a v x k le_rfl
    have second : ∀ t ≥ m, (∀ c, TeamTapeSorting.program.body.count c t (bank ∘ Prod.mk true) = I u) ∧
        ∀ c, TeamTapeSorting.program.body.AllStops c t (bank ∘ Prod.mk true) := by
      intro t ht; rw [hi₁]; exact program_spec hw hc a u x t (hm.trans ht)
    have checks := Lanes.both_spec TeamTapeSorting.program bank k m (I v) (I u) first second
    have answer : I v * I u = @ite ℕ (ownerValid hw hc a x v (some u)) (Classical.propDecidable _) 1 0 := by
      by_cases hv : valid hw hc a x v <;> by_cases hu : valid hw hc a x u <;> simp [I,ownerValid,hv,hu]
    have ec (c) : two.body.count c n next = I v * I u := by
      rw [two, FiniteRoutine.count_onPorts _ _ pair_inj, hk]; exact checks.1 _
    have es (c) : two.body.AllStops c n next := by
      rw [two, FiniteRoutine.allStops_onPorts _ _ pair_inj, hk]; exact checks.2 _
    constructor
    · intro c
      change (Routine.popCase presence (Routine.halt false) one.body two.body).count c t s = _
      rw [he,Routine.count_popCase,hflag]
      exact (ec c).trans answer
    · intro c
      rw [he]
      exact (stops_choice presence one.body two.body true s tail hflag c n).mpr (es c)

end TeamTapeInputRoute.Verify

end BorderVNP
end Computability
end OAI
