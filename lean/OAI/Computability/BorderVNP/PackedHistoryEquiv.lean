import OAI.Computability.BorderVNP.ShortenAdaptiveTree
import OAI.Computability.BorderVNP.PackedHistoryCircuitCost

/-! # Fixed public profile slots for an adaptive dependent history

Slots depend only on the public tree shape and level. Their valid contents
may depend on all child choices. Encoding a summand preserves its entire
ordered tuple of child histories, even when different summands output the
same physical state.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive Packing

/-- Public guess pins of a node: disjoint child transcripts and the local count words. -/
def Slot (k : ℕ) (G : ℕ → Type) : ℕ → Type
  | 0 => Empty
  | n+1 => (Fin k × Slot k G n) ⊕ G n

instance (k : ℕ) (G : ℕ → Type) [∀ n, Fintype (G n)] (d : ℕ) : Fintype (Slot k G d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ n ih => exact inferInstanceAs (Fintype ((Fin k × Slot k G n) ⊕ G n))

/-- The number of profile bits grows with the actual nodes, independently of the number of
mathematical histories. -/
theorem slot_card_le (k : ℕ) (G : ℕ → Type) [∀ n, Fintype (G n)] (d M : ℕ)
    (cap : ∀ n < d, Fintype.card (G n) ≤ M) :
    Fintype.card (Slot k G d) ≤ historyTreeCost k 0 M d := by
  apply le_historyTreeCost (fun j => Fintype.card (Slot k G j)) d
  · change Fintype.card Empty ≤ 0
    simp
  · intro j hj
    change Fintype.card ((Fin k × Slot k G j) ⊕ G j) ≤ _
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    exact Nat.add_le_add_left (cap j hj) _

variable {k b : ℕ} {A : ℕ → Type*} {G : ℕ → Type}

/-- An injective, fixed-slot encoding of the actual local choice at each child tuple. -/
structure Codec (S : System k b A) (G : ℕ → Type) where
  /-- The bits written for the local term selected from the child-dependent sum. -/
  word : ∀ j (h : j<b) (c : Fin k → A j), (S.choose j h c).Index → G j → Bool
  /-- Local words uniquely identify each summand in that dependent profile enumeration. -/
  injective : ∀ j h c, Function.Injective (word j h c)

variable {S : System k b A} (C : Codec S G)

/-- The true physical output state for one indexed history of a fixed input leaf tuple. -/
def state (n : ℕ) (h : n ≤ b) (a : Leaves k (A 0) n) (q : (S.histories n h a).Index) : A n :=
  (S.layer n).state ((S.histories n h a).term q)

/-- The full transcript of an adaptive history. No fields are required at a bottom bundle. -/
def encode : (n : ℕ) → (h : n ≤ b) → (a : Leaves k (A 0) n) →
    (S.histories n h a).Index → Slot k G n → Bool
  | 0, _, _, _, j => j.elim
  | n+1, h, a, q, .inl (i,j) => encode n (by omega) (a i) (q.1 i) j
  | n+1, h, a, q, .inr j => C.word n (by omega) (fun i => state n (by omega) (a i) (q.1 i)) q.2 j

/-- Distinct adaptive histories have distinct complete public bit strings, even when some
choices lead to equal final layouts. -/
theorem encode_injective (n : ℕ) (hn : n ≤ b) (a : Leaves k (A 0) n) :
    Function.Injective (encode C n hn a) := by
  induction n with
  | zero => intro q q' _; exact Subsingleton.elim (α := PUnit) q q'
  | succ n ih =>
    rintro ⟨c,u⟩ ⟨d,v⟩ eq
    have hc : c=d := by
      funext i
      apply ih (by omega) (a i)
      exact funext (fun j => congrFun eq (.inl (i,j)))
    subst d
    have hu := C.injective n (by omega) (fun i => state n (by omega) (a i) (c i))
      (show C.word n (by omega) (fun i => state n (by omega) (a i) (c i)) u =
          C.word n (by omega) (fun i => state n (by omega) (a i) (c i)) v from
        funext (fun j => congrFun eq (.inr j)))
    subst v
    rfl

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
