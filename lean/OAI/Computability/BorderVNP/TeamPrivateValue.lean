import OAI.Computability.BorderVNP.TeamPrivateCompiler
import OAI.Computability.VPVNP.StructuredStackClock

/-!
# Signed path value of the complete private call

For a private routine whose branches stop within a common native clock, the fixed
stack code, including binary input loading and clearing all private stacks, stops
on every branch and returns exactly the native signed path sum. The single stack
clock is linear in the input size and native time for fixed alphabet and tape count.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateValue

open TeamPrivateTape VPVNP.RAMTape

variable {Q Γ : Type} {m g d : ℕ}

/-- All branches, including rejecting ones, reach a native terminal by the given clock. -/
def Stops (P : Table Q d) : ℕ → Q → (Fin d → Track) → Prop
  | 0, _, _ => False
  | f+1, q, t => match P q (heads t) with
    | .halt .. => True
    | .one c => Stops P f c.next (c.apply t)
    | .two l r => Stops P f l.next (l.apply t) ∧ Stops P f r.next (r.apply t)

/-- The ordinary multitape stopping bound for all branches at the native symbol level. -/
def TapeStops (P : TapeTable Q Γ m) (blank : Γ) : ℕ → Q → (Fin m → SymbolTape Γ) → Prop
  | 0, _, _ => False
  | f+1, q, ts => match P q (fun i => (ts i).head) with
    | .halt .. => True
    | .one c => TapeStops P blank f c.next (c.apply blank ts)
    | .two l r => TapeStops P blank f l.next (l.apply blank ts) ∧ TapeStops P blank f r.next (r.apply blank ts)

/-- Translating the finite alphabet into synchronized tracks preserves the native branch
time bound exactly. -/
theorem track_stops_iff (a : Alphabet Γ g) (P : TapeTable Q Γ m) (f : ℕ) (q : Q)
    (ts : Fin m → SymbolTape Γ) :
    Stops (trackTable a P) f q (tracks a ts) ↔ TapeStops P a.blank f q ts := by
  induction f generalizing q ts with
  | zero => rfl
  | succ f ih =>
    have he : (fun i : Fin m => a.read (fun j => heads (tracks a ts) (finProdFinEquiv (i,j)))) =
        (fun i => (ts i).head) := by
      funext i
      simpa only [heads, tracks, Equiv.symm_apply_apply, SymbolTape.track] using a.read_bits (ts i).head
    rw [Stops, TapeStops]
    unfold trackTable
    rw [he]
    cases P q (fun i => (ts i).head) with
    | halt => rfl
    | one c =>
      change Stops (trackTable a P) f c.next ((c.tracks a).apply (tracks a ts)) ↔ _
      rw [tracks_apply, ih]
    | two l r =>
      change Stops (trackTable a P) f l.next ((l.tracks a).apply (tracks a ts)) ∧
        Stops (trackTable a P) f r.next ((r.tracks a).apply (tracks a ts)) ↔ _
      rw [tracks_apply, tracks_apply, ih, ih]

/-- The compiler can spend this many elementary stack steps from a ready control, including
terminal cleanup. There are two private bit stacks per track. -/
def budget (f : ℕ) (t : Fin d → Track) : ℕ := f*(3*d+2) + cells t + 2*d + 3

private def ambient (t : Fin d → Track) : Stacks (Bool ⊕ Port d) :=
  Sum.elim (fun _ => []) (bank t)

variable (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (P : TapeTable Q Γ m) (start : Q)

private theorem install_eq (t u : Fin (m*g) → Track) :
    installStacks Sum.inr (ambient t) (bank u) = ambient u := by
  funext k
  cases k with
  | inl b => rw [installStacks_outside (hl := fun _ => Sum.inr_ne_inl)]; rfl
  | inr p => exact installStacks_at Sum.inr_injective _ _ _

private theorem sweep (c : Command Q (m*g)) (t : Fin (m*g) → Track) :
    StackRuns (TeamPrivateCompiler.code a digit i P start) (2*(m*g)+1)
      (.run (.inl (.sweep c 0 (heads t)))) (ambient t)
      (.run (.inl (.ready c.next (heads (c.apply t))))) (ambient (c.apply t)) := by
  have r := (sweep_run (trackTable a P) c t).lift Sum.inr Sum.inr_injective
    (TeamPrivateCompiler.Control.run ∘ Sum.inl) (ambient t) (target := TeamPrivateCompiler.code a digit i P start) (by
      intro q h
      change TeamPrivateFragment.rows (trackTable a P) Sum.inr TeamPrivateCompiler.Control.run TeamPrivateCompiler.Control.result (.inl q) = _
      cases hc : TeamPrivateTape.code (trackTable a P) q <;> simp_all [TeamPrivateFragment.rows])
  simpa only [install_eq, Function.comp_apply] using r

private theorem cleanup (o : Option Bool) (t : Fin (m*g) → Track) :
    StackRuns (TeamPrivateCompiler.code a digit i P start) (TeamPrivateCleanup.steps (bank t))
      (.run (.inr (o, (TeamPrivateCleanup.all (Port (m*g))).body.entry))) (ambient t)
      (.result o) (fun _ => []) := by
  have r := TeamPrivateCleanup.all_linked (TeamPrivateCompiler.code a digit i P start) Sum.inr Sum.inr_injective
    (fun z => .run (.inr (o,z))) (.result o) (ambient t) (fun _ => rfl)
  have he : installStacks Sum.inr (ambient t) (fun _ => []) = fun _ => [] := by
    funext k; cases k with
    | inl b => rw [installStacks_outside (hl := fun _ => Sum.inr_ne_inl)]; rfl
    | inr p => rw [installStacks_at Sum.inr_injective]
  rwa [he] at r

private theorem prepend_run {K R : Type*} [DecidableEq K] {C : StackCode K R} (neg : R → Bool)
    {n q s r u} (run : StackRuns C n q s r u) {fuel : ℕ} (hn : n ≤ fuel) {v : ℤ}
    (hv : StopsWithin C (fuel-n) r u ∧ TeamStack.paths C neg (fuel-n) r u = v) :
    StopsWithin C fuel q s ∧ TeamStack.paths C neg fuel q s = v := by
  obtain ⟨hs, hw⟩ := hv
  have he : fuel - n + n = fuel := Nat.sub_add_cancel hn
  exact ⟨he ▸ (run.stopsWithin_iff _).mpr hs, he ▸ (signedPaths_runs run _).trans hw⟩

/-- At a ready state, all branches stop and the returned path sum is the signed sum of
the multitape transition table. The cost includes the clearing of terminal workspace. -/
theorem ready_value (f : ℕ) (q : Q) (t : Fin (m*g) → Track)
    (stop : Stops (trackTable a P) f q t) (ticks : ℕ) (ht : budget f t ≤ ticks) :
    StopsWithin (TeamPrivateCompiler.code a digit i P start) ticks (.run (.inl (.ready q (heads t)))) (ambient t) ∧
      TeamStack.paths (TeamPrivateCompiler.code a digit i P start) TeamPrivateCompiler.negative ticks
        (.run (.inl (.ready q (heads t)))) (ambient t) = paths (trackTable a P) f q t := by
  induction f generalizing q t ticks with
  | zero => exact stop.elim
  | succ f ih =>
    let M := TeamPrivateCompiler.code a digit i P start
    have hh : 0 < ticks := by unfold budget at ht; omega
    obtain ⟨ticks, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
    have continuation (c : Command Q (m*g)) (hs : Stops (trackTable a P) f c.next (c.apply t)) :
        StopsWithin M ticks (.run (.inl (.sweep c 0 (heads t)))) (ambient t) ∧
          TeamStack.paths M TeamPrivateCompiler.negative ticks (.run (.inl (.sweep c 0 (heads t))))
            (ambient t) = paths (trackTable a P) f c.next (c.apply t) := by
      have hg := cells_apply_le c t
      have hleft : budget f (c.apply t) + (2*(m*g)+1) ≤ ticks := by
        unfold budget at ht ⊢
        rw [Nat.succ_mul] at ht
        omega
      exact prepend_run _ (sweep a digit i P start c t) (by omega) (ih _ _ hs _ (by omega))
    change StopsWithin M (ticks+1) (.run (.inl (.ready q (heads t)))) (ambient t) ∧
      TeamStack.paths M TeamPrivateCompiler.negative (ticks+1) (.run (.inl (.ready q (heads t))))
        (ambient t) = paths (trackTable a P) (f+1) q t
    cases h : (trackTable a P) q (heads t) with
    | halt accept sign =>
      let o : Option Bool := if accept then some sign else none
      have hrow : M (.run (.inl (.ready q (heads t)))) =
          .goto (.run (.inr (o, (TeamPrivateCleanup.all (Port (m*g))).body.entry))) := by
        simp [M, TeamPrivateCompiler.code, TeamPrivateFragment.rows, TeamPrivateTape.code,
          TeamPrivateTape.negative, h, o]
      simp only [StopsWithin, TeamStack.paths, paths, hrow, h]
      have hfit : TeamPrivateCleanup.steps (bank t) < ticks := by
        unfold budget at ht
        rw [TeamPrivateCleanup.steps, bank_cells, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        omega
      apply prepend_run _ (cleanup a digit i P start o t) hfit.le
      obtain ⟨left, hl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_pos_of_lt hfit).ne'
      rw [hl]
      cases accept <;> cases sign <;>
        simp [o, StopsWithin, TeamStack.paths, TeamPrivateCompiler.code,
          TeamPrivateCompiler.negative, TeamTape.haltWeight]
    | one c =>
      have hrow : M (.run (.inl (.ready q (heads t)))) = .goto (.run (.inl (.sweep c 0 (heads t)))) := by
        simp [M, TeamPrivateCompiler.code, TeamPrivateFragment.rows, TeamPrivateTape.code, h]
      simp only [Stops, h] at stop
      simpa only [StopsWithin, TeamStack.paths, paths, hrow, h] using continuation c stop
    | two l r =>
      have hrow : M (.run (.inl (.ready q (heads t)))) = .choose
          (.run (.inl (.sweep l 0 (heads t)))) (.run (.inl (.sweep r 0 (heads t)))) := by
        simp [M, TeamPrivateCompiler.code, TeamPrivateFragment.rows, TeamPrivateTape.code, h]
      simp only [Stops, h] at stop
      have ⟨sl, vl⟩ := continuation l stop.1
      have ⟨sr, vr⟩ := continuation r stop.2
      simp only [StopsWithin, TeamStack.paths, paths, hrow, h]
      exact ⟨⟨sl, sr⟩, by rw [vl, vr]⟩

/-- On arbitrary binary input the concrete loader, interpreter and cleanup code return
the exact signed path sum of the ordinary finite-alphabet multitape machine. -/
theorem input_value (bs : List Bool) (f : ℕ)
    (stop : TapeStops P a.blank f start (input a.blank digit i bs)) (ticks : ℕ)
    (ht : TeamPrivateInput.steps g bs + budget f (tracks a (input a.blank digit i bs)) ≤ ticks) :
    StopsWithin (TeamPrivateCompiler.code a digit i P start) ticks (.load .start) (TeamPrivateInput.initial bs) ∧
      TeamStack.paths (TeamPrivateCompiler.code a digit i P start) TeamPrivateCompiler.negative ticks
        (.load .start) (TeamPrivateInput.initial bs) = tapePaths P a.blank f start (input a.blank digit i bs) := by
  let entry (bits : Fin (m*g) → Bool) : TeamPrivateCompiler.Control Q m g := .run (.inl (.ready start bits))
  have load := TeamPrivateInput.native_runs a digit i bs (TeamPrivateCompiler.code a digit i P start) .load entry (by
    intro q h
    cases q <;> first | rfl | simp [TeamPrivateInput.code] at h)
  rw [← track_paths]
  apply prepend_run _ load (by omega)
  exact ready_value a digit i P start _ _ _ ((track_stops_iff ..).mpr stop) _ (by omega)

end TeamPrivateValue

end BorderVNP
end Computability
end OAI
