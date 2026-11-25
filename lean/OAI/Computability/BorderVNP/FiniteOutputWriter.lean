import OAI.Computability.BorderVNP.FiniteOutput
import OAI.Computability.BorderVNP.TeamSignedControl

/-!
# Writing finite-field values in the literal universal machine

An accepting command enters a fixed output routine. It writes the numbered field code
backwards, moving the head to the left. At the final tick it writes the first cell and
halts with the head on that cell. The routine overwrites the entire output word even
when the work tape initially holds arbitrary data.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldTape

open VPVNP.RAMTape VPVNP.UniversalMachine Turing
open private lookup_signed encodeRow from OAI.Computability.BorderVNP.TeamSignedControl

variable {Q F : Type*} [Fintype Q] [Fintype F] [Field F]

/-- Logical states and the field output writer's descending cell counter. -/
abbrev State (Q F : Type*) [Fintype F] := Q ⊕ (F × Fin (Fintype.card F))

private noncomputable def mark (a : F) (i : ℕ) : Bool :=
  decide (i = (Fintype.equivFin F a).val)

private noncomputable def symbol (a : F) (i : ℕ) : Symbol :=
  if mark a i then 2 else 0

private def lastCell (F : Type*) [Fintype F] [Nonempty F] : Fin (Fintype.card F) :=
  ⟨Fintype.card F - 1, by have := Fintype.card_pos (α := F); omega⟩

private def liftCommand (v : F) (x y : Symbol) : Command Q → Command (State Q F)
  | .halt true => .next (.inr (v, lastCell F)) x 0 y 0
  | .halt false => .halt false
  | .next r a d b e => .next (.inl r) a d b e

private def liftChoices (v : F) (x y : Symbol) : Choices Q → Choices (State Q F)
  | .stop => .stop
  | .one a => .one (liftCommand v x y a)
  | .two a b => .two (liftCommand v x y a) (liftCommand v x y b)

private noncomputable def writerRows (code : Control Q) (weight : Q → F) : Control (State Q F)
  | .inl q, x, y => liftChoices (weight q) x y (code q x y)
  | .inr (v,i), x, _ =>
    if i.val = 0 then .one (.halt true) else
      .one (.next (.inr (v, ⟨i.val - 1, by omega⟩)) x 0 (symbol v i.val) 1)

private noncomputable def finalMark : State Q F → Bool
  | .inl _ => false
  | .inr (v,_) => mark v 0

/-- A literal program for a finite branching control with an arbitrary field weight on each
accepting instruction. Two occupied branch slots always count separately. -/
noncomputable abbrev machine (start : Q) (code : Control Q) (weight : Q → F) : Program :=
  TeamTape.table (.inl start) (writerRows code weight) finalMark

private noncomputable def physical (start : Q) (code : Control Q) (weight : Q → F)
    (ticks : ℕ) (q : State Q F) (t u : Tape Symbol) : F :=
  FPath.paths F (machine start code weight) ticks (running (.inl start) q t u)

private noncomputable def nextValue (start : Q) (code : Control Q) (weight : Q → F)
    (ticks : ℕ) (q : State Q F) (t u : Tape Symbol) : Command (State Q F) → F
  | .halt true => FPath.decodeWord F fun i =>
      decide (((u.write (if finalMark q then 2 else 0)).right₀.nth i.val).val = 2)
  | .halt false => 0
  | .next r a d b e => physical start code weight ticks r (updateTape t a d) (updateTape u b e)

private theorem next_eq (start : Q) (code : Control Q) (weight : Q → F)
    (ticks : ℕ) (q : State Q F) (t u : Tape Symbol) (cmd : Command (State Q F)) :
    FPath.paths F (machine start code weight) ticks
      (advance (running (.inl start) q t u) (TeamTape.signedInstruction (.inl start) (finalMark q) cmd)) =
        nextValue start code weight ticks q t u cmd := by
  cases cmd with
  | next => rfl
  | halt b =>
    cases b <;> cases ticks <;>
      simp [FPath.paths, FPath.output, TeamTape.signedInstruction, nextValue, instruction, advance, updateTape, running]

private theorem physical_step (start : Q) (code : Control Q) (weight : Q → F) (ticks : ℕ)
    (q : State Q F) (t u : Tape Symbol) : physical start code weight (ticks + 1) q t u =
      match writerRows code weight q t.head u.head with
      | .stop => 0
      | .one a => nextValue start code weight ticks q t u a
      | .two a b => nextValue start code weight ticks q t u a + nextValue start code weight ticks q t u b := by
  have h := running_state_ge_two (.inl start) q t u
  have h₁ : (running (.inl start) q t u).state.val ≠ 1 := by omega
  have h₀ : (running (.inl start) q t u).state.val ≠ 0 := by omega
  unfold physical
  rw [FPath.paths.eq_def]
  simp only [h₀, h₁, ite_false, machine, lookup_signed]
  cases writerRows code weight q t.head u.head <;> simp only [encodeRow, next_eq]

omit [Field F] in
private theorem mark_eq_code (v : F) (i : Fin (Fintype.card F)) :
    mark v i.val = FPath.code F v i := by
  simp [mark, FPath.code, Fin.ext_iff]

omit [Field F] in
private theorem bit_symbol (v : F) (k : ℕ) : decide ((symbol v k).val = 2) = mark v k := by
  unfold symbol
  cases mark v k <;> rfl

private theorem written (start : Q) (code : Control Q) (weight : Q → F) (v : F) (i : ℕ)
    (hi : i < Fintype.card F) (t u : Tape Symbol) (ticks : ℕ) (hc : i + 1 ≤ ticks)
    (tail : ∀ k, i+1+k < Fintype.card F → u.right.nth k = symbol v (i+1+k)) :
    physical start code weight ticks (.inr (v, ⟨i, hi⟩)) t u = v := by
  induction i generalizing t u ticks with
  | zero =>
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
    rw [physical_step]
    simp only [writerRows, ite_true, nextValue, finalMark]
    refine Eq.trans ?_ (FPath.decodeWord_code F v)
    congr 1
    funext j
    rw [← mark_eq_code]
    change decide (((u.write (symbol v 0)).right₀.nth j.val).val = 2) = mark v j.val
    rcases j with ⟨k,hk⟩
    cases k with
    | zero => simpa [Tape.right₀, Tape.write] using bit_symbol v 0
    | succ k =>
      have ht : u.right.nth k = symbol v (k+1) := by
        simpa only [Nat.zero_add, Nat.add_comm 1 k] using tail k (by omega)
      simpa only [Tape.right₀, ListBlank.nth_succ, ListBlank.tail_cons, Tape.write, ht] using
        bit_symbol v (k+1)
  | succ i ih =>
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ticks ≠ 0)
    rw [physical_step]
    simp only [writerRows, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one, nextValue, update_stay]
    apply ih _ _ _ _ (by omega)
    intro k hk
    change ((u.write (symbol v (i+1))).move .left).right.nth k = symbol v (i+1+k)
    cases k with
    | zero => simp [Tape.move, Tape.write]
    | succ k =>
      simpa only [Tape.move, Tape.write, ListBlank.nth_succ, ListBlank.tail_cons,
        Nat.add_succ, Nat.succ_add] using tail k (by omega)

/-- Field-valued path sum of the actual universal machine in a named original state. -/
noncomputable def value (start : Q) (code : Control Q) (weight : Q → F) (ticks : ℕ)
    (q : Q) (t u : Tape Symbol) : F := physical start code weight ticks (.inl q) t u

/-- Continuation value of a logical command. A valid accepting halt returns its field weight. -/
noncomputable def after (start : Q) (code : Control Q) (weight : Q → F) (ticks : ℕ)
    (q : Q) (t u : Tape Symbol) : Command Q → F
  | .halt b => if b then weight q else 0
  | .next r a d b e => value start code weight ticks r (updateTape t a d) (updateTape u b e)

private theorem lift_value (start : Q) (code : Control Q) (weight : Q → F) (ticks : ℕ)
    (h : Fintype.card F ≤ ticks) (q : Q) (t u : Tape Symbol) (cmd : Command Q) :
    nextValue start code weight ticks (.inl q) t u (liftCommand (weight q) t.head u.head cmd) =
      after start code weight ticks q t u cmd := by
  cases cmd with
  | next => rfl
  | halt b =>
    cases b with
    | false => rfl
    | true =>
      simp only [liftCommand, nextValue, update_stay, after, ite_true]
      have pos := Fintype.card_pos (α := F)
      exact written start code weight (weight q) _ (lastCell F).isLt t u ticks
        (by dsimp [lastCell]; omega) (fun k hk => by dsimp [lastCell] at hk; omega)

/-- One logical tick has its prescribed weighted continuations as long as the fixed field
output trailer fits the remaining clock. -/
theorem value_step (start : Q) (code : Control Q) (weight : Q → F) (ticks : ℕ) (q : Q)
    (t u : Tape Symbol) (h : Fintype.card F ≤ ticks) :
    value start code weight (ticks+1) q t u =
      match code q t.head u.head with
      | .stop => 0
      | .one a => after start code weight ticks q t u a
      | .two a b => after start code weight ticks q t u a + after start code weight ticks q t u b := by
  unfold value
  rw [physical_step]
  simp only [writerRows]
  cases code q t.head u.head <;> simp only [liftChoices, lift_value start code weight ticks h]

/-- An ordinary deterministic run retains its exact step count and every subsequent path
weight. This includes runs that leave no time to finish an output. -/
theorem runs_value {code : Control Q} {n q t u q' x y} (h : Runs code n q t u q' x y)
    (start : Q) (weight : Q → F) (fuel : ℕ) :
    value start code weight (fuel+n) q t u = value start code weight fuel q' x y := by
  induction h with
  | nil => rfl
  | cons hs _ ih =>
    rw [Nat.add_succ, value, physical_step]
    simp only [writerRows, hs, liftChoices, liftCommand, nextValue]
    exact ih

/-- Executing the prefixed program inside the finite-field processor reads the entire word,
including its own literal transition table. -/
theorem initial_value (start : Q) (code : Control Q) (weight : Q → F) (payload : Word) :
    let raw := programPrefix (machine start code weight) ++ payload
    FPath.U F raw.get = value start code weight (raw.length^100) start
      (Tape.mk₁ (raw.map fun b => if b then 2 else 1)) (Tape.mk₁ []) := by
  intro raw
  rw [FPath.U_eq_paths, List.ofFn_get]
  simp only [raw, decode_programPrefix, Option.elim_some]
  have he := initial_eq_running (Sum.inl start : State Q F) (writerRows code weight) raw
  change FPath.paths F (machine start code weight)
    (raw.length^100) (initial (compile (Sum.inl start) (writerRows code weight)) raw) = _
  rw [he]
  rfl

end FieldTape

end BorderVNP
end Computability
end OAI
