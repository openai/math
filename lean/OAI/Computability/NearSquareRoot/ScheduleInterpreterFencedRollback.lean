import OAI.Computability.NearSquareRoot.ScheduleInterpreterInit
import OAI.Computability.NearSquareRoot.ScheduleInterpreterRollback

/-!
# Preparing immutable restart data and rolling back fenced attempts

During preparation each ordinary write sets both copies of a symbol. A final
stationary transition marks all origins. No snapshot of the initialized tapes
is taken between attempts. The candidate reads and writes one copy during
execution; the rollback rule restores it from the other copy.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.Rollback

open IntegerMultiplication TM Reset

variable {A Q U I : Type}

/-- Encoding used for program setup and for the externally loaded bits. -/
def duplicate (v : A) : Cell A A := ⟨v,v,false,false,false⟩

def duplicateTape (x : Tape A) : Tape (Cell A A) := ⟨x.pos, fun j => duplicate (x.view j)⟩

def preparing (x : Config A U I) : Config (Cell A A) (Option U) I :=
  ⟨some x.pc, fun i => duplicateTape (x.tape i)⟩

def snapshot (x : Config A U I) : I → ℤ → A := fun i => (x.tape i).absolute

def origins (x : Config A U I) : I → ℤ := fun i => (x.tape i).pos

/-- Same tapes that the frontier-tracking interpreter sees at the first
instruction. The finite control is ready for a dispatch to the candidate. -/
def prepared (x : Config A U I) : Config (Cell A A) (Option U) I :=
  ⟨none, (Frontier.config (snapshot x) (origins x) (origins x) (origins x) x).tape⟩

/-- Mirror preparation writes into both finite tracks. On the source program's
halt, stamp the origin and the two singleton frontier marks on every head. -/
def prepareRule (m : Rule A U I) : Rule (Cell A A) (Option U) I
  | none, _ => none
  | some q, h =>
    match m q (fun i => (h i).val) with
    | some (q', ops) => some (some q', fun i => (duplicate (ops i).1, (ops i).2))
    | none => some (none, fun i => ({ h i with origin := true, leftEnd := true, rightEnd := true }, .stay))

private theorem duplicate_apply (x : Tape A) (op : A × Move) :
    (duplicateTape x).apply (duplicate op.1, op.2) = duplicateTape (x.apply op) := by
  unfold duplicateTape Tape.apply
  congr 1
  funext j
  by_cases h : j + op.2.shift = 0 <;> simp [h]

private theorem stamp (x : Tape A) :
    (duplicateTape x).apply (⟨x.view 0, x.view 0, true, true, true⟩, .stay) =
      Frontier.tape x.absolute x.pos x.pos x.pos x := by
  unfold duplicateTape Tape.apply Frontier.tape Tape.absolute
  simp only [Move.shift, Int.add_zero]
  congr 1
  funext j
  by_cases hj : j = 0
  · simp [hj]
  · simp [hj, duplicate]

@[simp] theorem duplicate_loaded (blank : A) (s : List A) :
    duplicateTape (Tape.loaded blank s) = Tape.loaded (duplicate blank) (s.map duplicate) := by
  simp only [Tape.loaded, duplicateTape, Tape.mk.injEq, true_and]
  funext j
  cases j <;> simp [List.getElem?_map, Option.getD_map]

private theorem prepare_step (m : Rule A U I) {x y : Config A U I} (h : advance m x = some y) :
    advance (prepareRule m) (preparing x) = some (preparing y) := by
  unfold advance at h ⊢
  cases hm : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [hm] at h
  | some qr =>
    obtain ⟨q, ops⟩ := qr
    simp [hm] at h
    subst y
    simp [prepareRule, preparing, duplicateTape, duplicate, hm]
    funext i
    exact duplicate_apply (x.tape i) (ops i)

private theorem prepare_final (m : Rule A U I) (x : Config A U I) (halt : advance m x = none) :
    advance (prepareRule m) (preparing x) = some (prepared x) := by
  have hm : m x.pc (fun i => (x.tape i).view 0) = none := by
    simpa [advance] using halt
  simp [advance, prepareRule, preparing, duplicateTape, duplicate, hm, prepared, Frontier.config]
  funext i
  exact stamp (x.tape i)

/-- Duplicating the baseline costs a single additional physical transition
regardless of the preparation trace length or tape size. -/
theorem prepare_trace (m : Rule A U I) {x y : Config A U I} {k : ℕ}
    (h : Trace (advance m) x k y) (halt : advance m y = none) :
    Trace (advance (prepareRule m)) (preparing x) (k+1) (prepared y) := by
  induction h with
  | nil => exact Trace.single (prepare_final m _ halt)
  | cons hs _ ih => simpa [Nat.add_assoc] using Trace.cons (prepare_step m hs) (ih halt)

/-- The first word of a delimiter-separated input fixes both fences on every
work tape, and the original input and the installed work symbols simultaneously
acquire immutable copies. -/
theorem prepare_delimited [DecidableEq A] (sep blank : A) (first tail : List A)
    (hs : sep ∉ first) (hb : blank ∉ first) (hsb : sep ≠ blank) :
    let s := first ++ sep :: tail
    Trace (advance (prepareRule (FenceInit.rule (I := I) sep blank)))
      (preparing (FenceInit.withInput blank s (Tape.loaded (FenceInit.plain blank) []) (.scan true)))
      (4*first.length+7)
      (prepared (FenceInit.withInput blank s ⟨0, FenceInit.fenced blank first.length⟩ .done)) := by
  exact prepare_trace _ (FenceInit.initialize_delimited (I := I) sep blank first tail hs hb hsb) rfl

/-- Each prepared work tape is ready for the guarded candidate with both the
active and the immutable copies of its two fence bits. -/
theorem prepared_work (blank : A) (s : List A) (n : ℕ) (i : I) :
    let w := Fence.markedTape (-(n : ℤ)) n (Tape.loaded blank [])
    (prepared (FenceInit.withInput blank s ⟨0, FenceInit.fenced blank n⟩ .done)).tape (some i) =
      Frontier.tape w.absolute 0 0 0 w := by
  change Frontier.tape ((⟨0, FenceInit.fenced blank n⟩ : Tape (Fence.Symbol A)).absolute) 0 0 0 _ = _
  rw [FenceInit.ready_for_guard]
  rfl

/-- The preparation starts on genuinely loaded tapes in the new alphabet,
and the same marked tape contents are present after every complete rollback. -/
theorem restored_tapes (x : Config A Q I) :
    (restored (Q := Q) id (snapshot x) (origins x)).tape = (prepared x).tape := by
  funext i
  exact (Frontier.tape_eq_reset _ _ _ _ _).symm

theorem prepare_delimited_visited [DecidableEq A] [Fintype I] (sep blank : A)
    (first tail : List A) (hn : 0 < first.length) :
    VisitsAtMost (prepareRule (FenceInit.rule (I := I) sep blank))
      (preparing (FenceInit.withInput blank (first ++ sep :: tail)
        (Tape.loaded (FenceInit.plain blank) []) (.scan true)))
      (4*first.length+7) ((Fintype.card (Option I)*23)*first.length) := by
  apply visitsAtMost_of_linear_fence 11 first.length hn
  intro t ht c run i
  have h := head_excursion run i
  cases i <;> simp only [preparing, FenceInit.withInput, duplicateTape,
    Tape.loaded, zero_sub, zero_add] at h <;> omega

/-- Any physical cutoff of the guarded machine followed by an actual
rollback. All heads return to their own origins with the original symbols,
including fence markers and input. Every rollback prefix stays inside the
original fences. -/
theorem fenced_timeout [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ) (x : Config A Q I)
    (fits : Fence.within lo hi x)
    {t : ℕ} {w : Config (Cell (Fence.Symbol A) (Fence.Symbol A)) (Frontier.Control (Bool × Q) I) I}
    (physical : Trace (advance (Frontier.rule (Fence.guard m)))
      (Frontier.config (snapshot (Fence.marked lo hi false x))
        (origins x) (origins x) (origins x) (Fence.marked lo hi false x)) t w) :
    let baseline := snapshot (Fence.marked lo hi false x)
    let cleanup := restoringRule (Fence.guard m) (id : Fence.Symbol A → Fence.Symbol A)
    ∃ (k : ℕ) (y : Config (Fence.Symbol A) (Bool × Q) I) (u : ℕ),
      Trace (advance (Fence.guard m)) (Fence.marked lo hi false x) k y ∧
      t ≤ 2*k ∧ 2*k ≤ t+1 ∧ t+u ≤ 2*k + 3*(k+1) ∧
      Trace (advance cleanup) (entry w) u (restored id baseline (origins x)) ∧
      advance cleanup (restored id baseline (origins x)) = none ∧
      ∀ {j c}, Trace (advance cleanup) (entry w) j c →
        ∀ i, lo i ≤ (c.tape i).pos ∧ (c.tape i).pos ≤ hi i := by
  let guarded := Fence.marked lo hi false x
  have head (i : I) : (guarded.tape i).pos = origins x i := rfl
  obtain ⟨k, y, u, ht, hk₁, hk₂, hr, hh, hb⟩ :=
    timeout_restore (Fence.guard m) id (snapshot guarded) (origins x) guarded head
      (fun _ _ => rfl) physical
  refine ⟨k, y, u, ht, hk₁, hk₂, hb, hr, hh, ?_⟩
  intro j c cut
  apply timeout_prefix_restore (Fence.guard m) id (snapshot guarded) (origins x) lo hi guarded head
    _ physical cut
  intro j z run
  obtain ⟨v, tag, hv, rfl⟩ := Fence.trace_within m lo hi fits run
  exact hv

/-- The marked attempt itself obeys the same cell count as the source
guard. This applies to every physical prefix, including half-steps. -/
theorem fenced_visits [Fintype I] (m : Rule A Q I) (lo hi : I → ℤ) (x : Config A Q I)
    (fits : Fence.within lo hi x) (t : ℕ) :
    VisitsAtMost (Frontier.rule (Fence.guard m))
      (Frontier.config (snapshot (Fence.marked lo hi false x))
        (origins x) (origins x) (origins x) (Fence.marked lo hi false x)) t
      (∑ i : I, (hi i + 1 - lo i).toNat) := by
  apply visitsAtMost_of_tape_fences lo hi
  intro j _ w run
  obtain ⟨_, _, _, _, _, _, _, _, _, hc⟩ := fenced_timeout m lo hi x fits run
  exact hc (.nil _)

end Uniform.Rollback

end NearSquareRoot
end Computability
end OAI
