import OAI.Computability.BorderVNP.FinitePrivateCall
import OAI.Computability.BorderVNP.FiniteTeamSelectionReplay

/-! # Exact branch tapes of the physical private compiler

At the same bounded native and physical clocks used for the private value, an
accepting physical tape decodes to the actual bounded track-table execution.
The loader, synchronized track sweeps and cleanup consume no choice bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldSelect

open VPVNP.RAMTape TeamPrivateTape TeamPrivateValue
open private ambient sweep cleanup from OAI.Computability.BorderVNP.TeamPrivateValue

variable {Q Γ : Type} {m g d : ℕ} {F : Type*}

/-- A deterministic segment preserves the entire leaf dictionary when its exact
elementary time is accounted for. -/
theorem leaves_segment {K S : Type} [DecidableEq K] {C : StackCode K S}
    {n q s u out} (r : StackRuns C n q s u out) (w : S → F) (ticks : ℕ) :
    FieldReplay.leaves C w (ticks+n) q s = FieldReplay.leaves C w ticks u out := by
  induction r with
  | nil => rfl
  | cons step _ ih => cases step <;> simp_all [FieldReplay.leaves]

/-- Read a native signed halt on an exact supplied choice string. Rejects and
unread or missing choice bits all have empty observation. -/
def observe (P : Table Q d) (f : ℕ) (q : Q) (t : Fin d → Track) (bs : List Bool) : Option Bool :=
  (TeamPrivateCall.evaluate P f q t bs).bind Prod.fst

private theorem ready_leaf (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (P : TapeTable Q Γ m)
    (start : Q) (w : TeamPrivateCompiler.Control Q m g → F) (f : ℕ) (q : Q) (t : Fin (m*g) → Track)
    (hs : Stops (trackTable a P) f q t) (ticks : ℕ) (ht : budget f t ≤ ticks)
    (bs : List Bool) (v : F) :
    (bs,v) ∈ FieldReplay.leaves (TeamPrivateCompiler.code a digit i P start) w ticks
      (.run (.inl (.ready q (heads t)))) (ambient t) ↔
    ∃ sg, observe (trackTable a P) f q t bs = some sg ∧ w (.result (some sg)) = v := by
  induction f generalizing q t ticks bs with
  | zero => exact hs.elim
  | succ f ih =>
    let M := TeamPrivateCompiler.code a digit i P start
    have hh : 0 < ticks := by unfold budget at ht; omega
    obtain ⟨ticks,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
    have cont (c : Command Q (m*g)) (hs' : Stops (trackTable a P) f c.next (c.apply t)) (bits : List Bool) :
        (bits,v) ∈ FieldReplay.leaves M w ticks (.run (.inl (.sweep c 0 (heads t)))) (ambient t) ↔
        ∃ sg, observe (trackTable a P) f c.next (c.apply t) bits = some sg ∧ w (.result (some sg)) = v := by
      have hb := cells_apply_le c t
      have hfit : budget f (c.apply t) + (2*(m*g)+1) ≤ ticks := by unfold budget at ht ⊢; rw [Nat.succ_mul] at ht; omega
      let d := 2*(m*g)+1
      have he : ticks = (ticks-d)+d := by dsimp [d]; omega
      rw [he, leaves_segment (sweep a digit i P start c t)]
      exact ih _ _ hs' _ (by dsimp [d]; omega) bits
    change (bs,v) ∈ FieldReplay.leaves M w (ticks+1) (.run (.inl (.ready q (heads t)))) (ambient t) ↔ _
    cases op : (trackTable a P) q (heads t) with
    | halt accept sign =>
      let out := if accept then some sign else none
      have row : M (.run (.inl (.ready q (heads t)))) =
          .goto (.run (.inr (out, (TeamPrivateCleanup.all (Port (m*g))).body.entry))) := by
        simp [M, TeamPrivateCompiler.code, TeamPrivateFragment.rows, TeamPrivateTape.code,
          TeamPrivateTape.negative, op, out]
      have hfit : TeamPrivateCleanup.steps (bank t) < ticks := by
        unfold budget at ht
        rw [TeamPrivateCleanup.steps,bank_cells,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
        omega
      let cost := TeamPrivateCleanup.steps (bank t)
      have he : ticks = (ticks-cost)+cost := by dsimp [cost]; omega
      rw [FieldReplay.leaves,row]
      change (bs,v) ∈ FieldReplay.leaves M w ticks (.run (.inr (out,_))) (ambient t) ↔ _
      rw [he,leaves_segment (cleanup a digit i P start out t)]
      obtain ⟨fuel,hf⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_pos_of_lt hfit).ne'
      rw [show ticks-cost = fuel+1 from hf]
      cases accept <;> cases bs <;>
        simp [FieldReplay.leaves,TeamPrivateCompiler.code,out,observe,TeamPrivateCall.evaluate,op,eq_comm]
    | one c =>
      have row : M (.run (.inl (.ready q (heads t)))) = .goto (.run (.inl (.sweep c 0 (heads t)))) := by
        simp [M, TeamPrivateCompiler.code, TeamPrivateFragment.rows, TeamPrivateTape.code, op]
      simp only [Stops,op] at hs
      simpa only [FieldReplay.leaves,row,observe,TeamPrivateCall.evaluate,op] using cont c hs bs
    | two l r =>
      have row : M (.run (.inl (.ready q (heads t)))) =
          .choose (.run (.inl (.sweep l 0 (heads t)))) (.run (.inl (.sweep r 0 (heads t)))) := by
        simp [M, TeamPrivateCompiler.code, TeamPrivateFragment.rows, TeamPrivateTape.code, op]
      simp only [Stops,op] at hs
      rw [FieldReplay.mem_choose_iff _ _ _ _ _ _ _ row]
      cases bs with
      | nil => simp [observe,TeamPrivateCall.evaluate,op]
      | cons b bits => cases b <;> simp [cont l hs.1, cont r hs.2, observe,TeamPrivateCall.evaluate,op]

/-- The compiled private verifier consumes exactly the native choices that lead
to the observed accepting halt, and the physical scalar is its terminal weight. -/
theorem private_leaf_iff (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (P : TapeTable Q Γ m)
    (start : Q) (w : TeamPrivateCompiler.Control Q m g → F) (raw : List Bool) (f ticks : ℕ)
    (hs : TapeStops P a.blank f start (input a.blank digit i raw))
    (ht : TeamPrivateInput.steps g raw + budget f (tracks a (input a.blank digit i raw)) ≤ ticks)
    (bits : List Bool) (v : F) :
    (bits,v) ∈ FieldReplay.leaves (TeamPrivateCompiler.code a digit i P start) w ticks
      (.load .start) (TeamPrivateInput.initial raw) ↔
      ∃ sg, observe (trackTable a P) f start (tracks a (input a.blank digit i raw)) bits = some sg ∧
        w (.result (some sg)) = v := by
  let entry (hs : Fin (m*g) → Bool) : TeamPrivateCompiler.Control Q m g := .run (.inl (.ready start hs))
  have load := TeamPrivateInput.native_runs a digit i raw (TeamPrivateCompiler.code a digit i P start) .load entry (by
    intro q h; cases q <;> first | rfl | simp [TeamPrivateInput.code] at h)
  let time := TeamPrivateInput.steps g raw
  have he : ticks = (ticks-time)+time := by dsimp [time]; omega
  rw [he, leaves_segment load]
  exact ready_leaf a digit i P start w _ _ _ ((track_stops_iff ..).mpr hs) _ (by dsimp [time]; omega) bits v

end FieldSelect

end BorderVNP
end Computability
end OAI
