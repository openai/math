import OAI.Computability.BorderVNP.TeamPrivateCleanup
import OAI.Computability.BorderVNP.TeamPrivateRepresentation

/-!
# Linking a private multitape call to the processor validator

The outer finite control designates a continuation for each of the three returned
weights. A native branch uses exactly one bit on its choice tape. Movement of
the bit planes and cleanup of every private work stack are deterministic.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateFragment

open VPVNP.RAMTape TeamPrivateTape

variable {K R : Type} {Q : Type*} {d : ℕ}

/-- A path with its exact list of binary choices. Its natural index counts continuing
transitions, and the result records the sign on the terminal (or zero on rejection). -/
inductive Run (P : Table Q d) : ℕ → Q → (Fin d → Track) → List Bool → Option Bool →
    (Fin d → Track) → Prop
  | stop {q t accept neg} (h : P q (heads t) = .halt accept neg) :
    Run P 0 q t [] (if accept then some neg else none) t
  | one {q t c n bs out u} (h : P q (heads t) = .one c) (rest : Run P n c.next (c.apply t) bs out u) :
    Run P (n+1) q t bs out u
  | two {q t l r n bs out u} (b : Bool) (h : P q (heads t) = .two l r)
    (rest : let c := if b then r else l; Run P n c.next (c.apply t) bs out u) :
    Run P (n+1) q t (b :: bs) out u

/-- Space along a native path grows by at most one cell per track per transition. -/
theorem Run.cells_le {P : Table Q d} {n q t bs out u} (run : Run P n q t bs out u) :
    cells u ≤ cells t + n * d := by
  induction run with
  | stop => simp
  | @one q t c n bs out u _ _ ih =>
    have := cells_apply_le c t
    exact ih.trans (by rw [Nat.succ_mul]; omega)
  | @two q t l r n bs out u b _ _ ih =>
    have := cells_apply_le (if b then r else l) t
    exact ih.trans (by rw [Nat.succ_mul]; omega)

/-- An auxiliary deterministic replay of a stack code on a supplied list of choice bits.
Ordinary instructions preserve the entire list and a binary row consumes its head. -/
def replay (C : StackCode K R) : StackCode K (R × List Bool)
  | (q, bs) => match C q with
    | .choose l r => match bs with
      | [] => .halt false
      | b :: tail => .goto ((if b then r else l), tail)
    | op => op.rename id (fun q' => (q', bs))

/-- Lifting a deterministic stack segment to replay leaves all choice bits untouched. -/
theorem replay_segment [DecidableEq K] {C : StackCode K R} {n q s q' s'}
    (run : StackRuns C n q s q' s') (bs : List Bool) :
    StackRuns (replay C) n (q, bs) s (q', bs) s' := by
  induction run with
  | nil => exact .nil ..
  | cons step _ ih =>
    cases step with
    | push h => exact .cons (.push (by simp [replay, h])) ih
    | @pop k f h => exact .cons (.pop (k := k) (f := fun b => (f b, bs)) (by simp [replay, h, Function.comp_def])) ih
    | goto h => exact .cons (.goto (by simp [replay, h])) ih

/-- Named fragment labels, including separate cleanup controls for the three possible returns. -/
abbrev Label (Q : Type*) (d : ℕ) := State Q d ⊕ (Option Bool × (TeamPrivateCleanup.all (Port d)).State)

/-- Install the private code at caller labels. Every halt first jumps into cleanup and
resumes at the caller's continuation for that sign. -/
noncomputable def rows (P : Table Q d) (ports : Port d → K) (label : Label Q d → R)
    (resume : Option Bool → R) : Label Q d → StackOp K R
  | .inl q => match code P q with
    | .halt accept => .goto (label (.inr (if accept then some (negative P q) else none,
        (TeamPrivateCleanup.all (Port d)).body.entry)))
    | op => op.rename ports (label ∘ Sum.inl)
  | .inr (out, z) => ((TeamPrivateCleanup.all (Port d)).body.code z).rename ports
      (fun next => next.elim (resume out) (fun z' => label (.inr (out, z'))))

/-- Entry label of the installed routine with the prescribed initial scanned symbols. -/
def entry (label : Label Q d → R) (start : Q) (t : Fin d → Track) : R :=
  label (.inl (.ready start (heads t)))

private theorem install_twice (ports : Port d → K) (hp : Function.Injective ports)
    (base : Stacks K) (s u : Stacks (Port d)) :
    installStacks ports (installStacks ports base s) u = installStacks ports base u := by
  funext k
  by_cases hk : ∃ j, ports j = k
  · obtain ⟨j, rfl⟩ := hk; simp [installStacks_at hp]
  · simp [installStacks_outside (hl := not_exists.mp hk)]

private theorem linked_sweep [DecidableEq K] (P : Table Q d) (ports : Port d → K)
    (hp : Function.Injective ports) (label : Label Q d → R) (resume : Option Bool → R)
    (C : StackCode K R) (hr : ∀ z, C (label z) = rows P ports label resume z)
    (base : Stacks K) (c : Command Q d) (t : Fin d → Track) (bits : List Bool) :
    StackRuns (replay C) (2*d+1) (label (.inl (.sweep c 0 (heads t))), bits)
      (installStacks ports base (bank t)) (entry label c.next (c.apply t), bits)
      (installStacks ports base (bank (c.apply t))) := by
  apply replay_segment
  apply (sweep_run P c t).lift ports hp (label ∘ Sum.inl) base
  intro u hu
  rw [Function.comp_apply, hr]
  cases h : code P u <;> simp_all [rows]

/-- Replay of an actual native path enters the specified sign continuation with its exact
choices consumed, all private bit stacks empty, and every caller stack outside the bank
preserved. The exact cost includes clearing all occupied cells and checking each empty port. -/
theorem run_linked [DecidableEq K] {P : Table Q d} {n q t bs out u} (native : Run P n q t bs out u)
    (ports : Port d → K) (hp : Function.Injective ports) (label : Label Q d → R)
    (resume : Option Bool → R) (C : StackCode K R) (hr : ∀ z, C (label z) = rows P ports label resume z)
    (base : Stacks K) (suffix : List Bool) :
    StackRuns (replay C) (n * (2*d+2) + 1 + TeamPrivateCleanup.steps (bank u))
      (entry label q t, bs ++ suffix) (installStacks ports base (bank t))
      (resume out, suffix) (installStacks ports base (fun _ => [])) := by
  induction native with
  | @stop q t accept neg h =>
    let out := if accept then some neg else none
    have hc := TeamPrivateCleanup.all_linked C ports hp (fun z => label (.inr (out,z))) (resume out)
      (installStacks ports base (bank t)) (fun z => hr (.inr (out,z)))
    have hb : installStacks ports base (bank t) ∘ ports = bank t := funext (fun j => installStacks_at hp base (bank t) j)
    rw [hb, install_twice ports hp] at hc
    have he : C (entry label q t) =
        .goto (label (.inr (out, (TeamPrivateCleanup.all (Port d)).body.entry))) := by
      rw [entry, hr]; simp [rows, code, h, negative, out]
    simpa only [Nat.zero_mul, Nat.zero_add, Nat.add_comm 1, List.nil_append] using
      (StackRuns.cons (StackStep.goto (by simp [replay, he])) (replay_segment hc suffix))
  | @one q t c n bs out u h _ ih =>
    have he : C (entry label q t) = .goto (label (.inl (.sweep c 0 (heads t)))) := by
      rw [entry, hr]; simp [rows, code, h]
    have sweep := linked_sweep P ports hp label resume C hr base c t (bs ++ suffix)
    rw [show (n+1)*(2*d+2) + 1 + TeamPrivateCleanup.steps (bank u) =
      ((2*d+1) + (n*(2*d+2)+1+TeamPrivateCleanup.steps (bank u))) + 1 by ring]
    exact .cons (.goto (by simp [replay, he])) (sweep.trans ih)
  | @two q t l r n bs out u b h _ ih =>
    have he : C (entry label q t) = .choose (label (.inl (.sweep l 0 (heads t))))
        (label (.inl (.sweep r 0 (heads t)))) := by rw [entry, hr]; simp [rows, code, h]
    have sweep := linked_sweep P ports hp label resume C hr base (if b then r else l) t (bs ++ suffix)
    rw [show (n+1)*(2*d+2) + 1 + TeamPrivateCleanup.steps (bank u) =
      ((2*d+1) + (n*(2*d+2)+1+TeamPrivateCleanup.steps (bank u))) + 1 by ring]
    exact .cons (.goto (by cases b <;> simp [replay, he])) (sweep.trans ih)

/-- The total elementary time, including cleanup, is linear in the private input space
and native transition bound for fixed track count. -/
theorem run_cost_le {P : Table Q d} {n q t bs out u} (native : Run P n q t bs out u) :
    n * (2*d+2) + 1 + TeamPrivateCleanup.steps (bank u) ≤
      n * (3*d+2) + cells t + 2*d + 2 := by
  have h := native.cells_le
  rw [TeamPrivateCleanup.steps, bank_cells, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  calc
    _ ≤ n*(2*d+2)+1 + (cells t + n*d + d*2 + 1) := by omega
    _ = _ := by ring

end TeamPrivateFragment

end BorderVNP
end Computability
end OAI
