import OAI.Computability.BorderVNP.TeamPrivateCall

/-!
# Exact finite outcomes of a clocked private tape call

Each terminating choice sequence occurs once, including a rejecting halt with
weight zero. The two slots of a binary instruction have different first bits
even when they run the same command.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateCall

open TeamPrivateTape
open scoped BigOperators

variable {Q : Type*} {d : ℕ}

private def prepend (b : Bool) :
    (List Bool × TeamRAM.Sign) ↪ List Bool × TeamRAM.Sign where
  toFun x := (b :: x.1, x.2)
  inj' := by rintro ⟨xs, s⟩ ⟨ys, t⟩ h; simpa using h

private theorem prefix_disjoint (s t : Finset (List Bool × TeamRAM.Sign)) :
    Disjoint (s.map (prepend false)) (t.map (prepend true)) := by
  apply Finset.disjoint_left.mpr
  rintro _ hs ht
  obtain ⟨⟨xs, a⟩, _, rfl⟩ := Finset.mem_map.mp hs
  obtain ⟨⟨ys, b⟩, _, he⟩ := Finset.mem_map.mp ht
  change (true :: ys, b) = (false :: xs, a) at he
  simp at he

private theorem mem_prefix (b c : Bool) (xs : List Bool) (v : TeamRAM.Sign)
    (s : Finset (List Bool × TeamRAM.Sign)) :
    (c :: xs, v) ∈ s.map (prepend b) ↔ b = c ∧ (xs, v) ∈ s := by
  constructor
  · intro h
    obtain ⟨⟨ys, u⟩, hm, he⟩ := Finset.mem_map.mp h
    change (b :: ys, u) = (c :: xs, v) at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (b = c ∧ ys = xs) ∧ u = v := by simpa using he
    exact ⟨rfl, hm⟩
  · rintro ⟨rfl, hm⟩
    exact Finset.mem_map.mpr ⟨(xs, v), hm, rfl⟩

private theorem nil_not_mem_prefix (b : Bool) (v : TeamRAM.Sign)
    (s : Finset (List Bool × TeamRAM.Sign)) : ([], v) ∉ s.map (prepend b) := by
  intro h
  obtain ⟨⟨xs, u⟩, _, he⟩ := Finset.mem_map.mp h
  change (b :: xs, u) = ([], v) at he
  simp at he

/-- The consumed choice strings and their terminal signs within the native clock. -/
def outcomes (P : Table Q d) : ℕ → Q → (Fin d → Track) → Finset (List Bool × TeamRAM.Sign)
  | 0, _, _ => ∅
  | f + 1, q, t => match P q (heads t) with
    | .halt accept neg => {([], sign (if accept then some neg else none))}
    | .one c => outcomes P f c.next (c.apply t)
    | .two l r => (outcomes P f l.next (l.apply t)).map (prepend false) ∪
        (outcomes P f r.next (r.apply t)).map (prepend true)

/-- A choice string and sign occur precisely when replay consumes that string and
returns the indicated sign. -/
theorem mem_outcomes_iff (P : Table Q d) (fuel : ℕ) (q : Q) (t : Fin d → Track)
    (bits : List Bool) (v : TeamRAM.Sign) :
    (bits, v) ∈ outcomes P fuel q t ↔
      (evaluate P fuel q t bits).map (fun x => sign x.1) = some v := by
  induction fuel generalizing q t bits with
  | zero => simp [outcomes, evaluate]
  | succ f ih =>
    cases op : P q (heads t) with
    | halt a s => cases bits <;> simp [outcomes, evaluate, op, eq_comm]
    | one c => simpa [outcomes, evaluate, op] using ih c.next (c.apply t) bits
    | two l r =>
      cases bits with
      | nil =>
        simp only [outcomes, evaluate, op, Finset.mem_union, nil_not_mem_prefix]
        simp
      | cons b bits =>
        simp only [outcomes, evaluate, op, Finset.mem_union, mem_prefix]
        cases b <;> simp [ih]

/-- The finite sum of the signed terminal weights is the native tape's path sum. -/
theorem sum_outcomes (P : Table Q d) (fuel : ℕ) (q : Q) (t : Fin d → Track) :
    ∑ x ∈ outcomes P fuel q t, x.2.value = TeamPrivateTape.paths P fuel q t := by
  induction fuel generalizing q t with
  | zero => simp [outcomes, TeamPrivateTape.paths]
  | succ f ih =>
    cases op : P q (heads t) with
    | halt a s =>
      cases a <;> cases s <;>
        simp [outcomes, TeamPrivateTape.paths, op, sign, TeamRAM.Sign.value, TeamTape.haltWeight]
    | one c => simpa [outcomes, TeamPrivateTape.paths, op] using ih c.next (c.apply t)
    | two l r =>
      simp only [outcomes, TeamPrivateTape.paths, op]
      rw [Finset.sum_union (prefix_disjoint _ _), Finset.sum_map, Finset.sum_map]
      exact congrArg₂ Int.add (ih _ _) (ih _ _)

end TeamPrivateCall

end BorderVNP
end Computability
end OAI
