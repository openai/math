import OAI.Computability.NearSquareRoot.BoundedProgram

/-!
# Exact space certificates for root constructors and branches

The cap is measured on the encoded per-register stacks, including parked data.
Inspecting and popping a constructor preserves that cap. Only the pending
return from the single-instruction pop requires an additional return address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space

open IntegerMultiplication IntegerMultiplication.Code

/-- The letters of every live register fit the supplied absolute cap. -/
def DeckCap (cap : ℕ) (r : Deck) : Prop := ∀ j, (letters r j).length ≤ cap

theorem DeckCap.mono {cap cap' : ℕ} {r : Deck} (h : DeckCap cap r)
    (hcap : cap ≤ cap') : DeckCap cap' r := fun j => (h j).trans hcap

theorem DeckCap.pile {base : ℕ} {r : Deck} (h : DeckCap base r) (i : ℕ) (x : Tree) :
    DeckCap (base + x.count) (pile i x r) := by
  intro j
  by_cases hj : j = i
  · subst j
    rw [letters_here, List.length_append, Tree.spell_length]
    have := h i
    omega
  · rw [pile_far i j (Ne.symm hj)]
    exact (h j).trans (Nat.le_add_right ..)

theorem DeckCap.exposeFork {cap i : ℕ} {x y : Tree} {r : Deck}
    (hc : DeckCap cap (Code.pile i (.fork x y) r)) : DeckCap cap (Code.pile i x (Code.pile i y r)) := by
  intro j
  have hj := hc j
  by_cases hji : j = i
  · subst j
    simp only [letters_here, List.length_append, Tree.spell_length, Tree.count] at *
    omega
  · simpa only [pile_far i j (Ne.symm hji)] using hj

/-- Decode the outer event pair and its Boolean tag without inspecting the payload. -/
def decodeBit (c d : Cmd) : Cmd :=
  splitRoot 0 (fun _ => .pass) (splitRoot 0 (fun b => bif b then d else c) .pass)

namespace BoundedFits

theorem pass {env : Env} {r : Deck} {cap depth : ℕ} (hc : DeckCap cap r) :
    BoundedFits env .pass r r 1 cap depth := ⟨1, le_rfl, .pass hc⟩

theorem give (b : Bool) (r : Deck) (i : ℕ) (env : Env) {cap depth : ℕ}
    (hc : DeckCap cap (pile i (.atom b) r)) :
    BoundedFits env (Code.give i b) r (pile i (.atom b) r) 1 cap depth := by
  refine ⟨1, le_rfl, ?_⟩
  rw [letters_pile]
  apply BoundedRun.push
  simpa [DeckCap, letters_pile, Tree.spell] using hc

theorem pack (x y : Tree) (r : Deck) (i : ℕ) (env : Env) {cap depth : ℕ}
    (hc : DeckCap cap (pile i (.fork x y) r)) :
    BoundedFits env (Code.pack i) (pile i x (pile i y r)) (pile i (.fork x y) r)
      1 cap depth := by
  have he : Function.update (letters (pile i x (pile i y r))) i
      (.node :: letters (pile i x (pile i y r)) i) = letters (pile i (.fork x y) r) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [Tree.spell, List.append_assoc]
    · simp [pile_far _ _ (Ne.symm hj), Function.update_of_ne hj]
  refine ⟨1, le_rfl, ?_⟩
  rw [← he]
  exact .push (by rw [he]; exact hc)

private theorem lowSplit {r s t : Reg Ltr} {e : Ltr} {i : ℕ} {l : List Ltr}
    {env : Env} {f : Option Ltr → Cmd} {n cap depth : ℕ}
    (he : r i = e :: l) (hr : Function.update r i l = s)
    (child : BoundedRun cap depth env (f (some e)) s n t)
    (data : ∀ j, (r j).length ≤ cap) (hd : 1 ≤ depth) :
    BoundedRun cap depth env (.look i fun o => .join (.pop i) (f o)) r (1+(1+1+1+n)) t := by
  apply BoundedRun.look
  rw [he, List.head?_cons]
  have pop : BoundedRun cap 0 env (.pop i) r 1 (Function.update r i l) := by
    convert BoundedRun.pop (Γ := env) (r := r) (i := i) data using 1
    simp [he]
  exact .join pop (hr ▸ child) hd

theorem bit {b : Bool} {r s : Deck} {i : ℕ} {c : Bool → Cmd} {d : Cmd} {n cap depth : ℕ}
    {env : Env} (h : BoundedFits env (c b) r s n cap depth)
    (hc : DeckCap cap (pile i (.atom b) r)) (hd : 1 ≤ depth) :
    BoundedFits env (splitRoot i c d) (pile i (.atom b) r) s (n+4) cap depth := by
  obtain ⟨t, ht, child⟩ := h
  refine ⟨1+(1+1+1+t), by omega, ?_⟩
  unfold splitRoot
  apply lowSplit (e := .bit b) (l := letters r i) _ _ child hc hd
  · rw [letters_here]; rfl
  · funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj, pile_far _ _ (Ne.symm hj)]

theorem pair {x y : Tree} {r s : Deck} {i : ℕ} {c : Bool → Cmd} {d : Cmd} {n cap depth : ℕ}
    {env : Env} (h : BoundedFits env d (pile i x (pile i y r)) s n cap depth)
    (hc : DeckCap cap (pile i (.fork x y) r)) (hd : 1 ≤ depth) :
    BoundedFits env (splitRoot i c d) (pile i (.fork x y) r) s (n+4) cap depth := by
  obtain ⟨t, ht, child⟩ := h
  refine ⟨1+(1+1+1+t), by omega, ?_⟩
  unfold splitRoot
  apply lowSplit (e := .node) (l := letters (pile i x (pile i y r)) i) _ _ child hc hd
  · simp [Tree.spell, List.append_assoc]
  · funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj, pile_far _ _ (Ne.symm hj)]

theorem decodeBit {b : Bool} {x : Tree} {r s : Deck} {c d : Cmd} {n cap depth : ℕ}
    {env : Env} (h : BoundedFits env (bif b then d else c) (pile 0 x r) s n cap depth)
    (hc : DeckCap cap (pile 0 (.fork (.atom b) x) r)) (hd : 1 ≤ depth) :
    BoundedFits env (Space.decodeBit c d) (pile 0 (.fork (.atom b) x) r) s (n+8) cap depth :=
  pair (bit h hc.exposeFork hd) hc hd

end BoundedFits

end Space

end NearSquareRoot
end Computability
end OAI
