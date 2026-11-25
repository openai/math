import OAI.Computability.BorderVNP.PackedHistoryPhysicalCodec

/-! # Restricting adaptive histories to their physical capacity invariant

Taking a subtype of the child states lets the encoder bound its words only
on admissible packs. For any fixed tuple of admissible leaves, the restricted
and original trees contain exactly the same profile choices, with identical
output states after forgetting the proofs of the capacity invariant.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Capacity

open Shortening Shortening.Adaptive Packing

variable {k b : ℕ} {A : ℕ → Type*}

/-- The next physical state satisfies its bound for every term above bounded children. -/
def Closed (S : System k b A) (good : ∀ n, A n → Prop) : Prop :=
  ∀ j (hj : j < b) (c : Fin k → A j), (∀ i, good j (c i)) →
    ∀ u, good (j+1) ((S.choose j hj c).term u)

/-- Restrict only the states. Every local profile index, including multiplicities
of equal output states, is retained. -/
def restrict (S : System k b A) (good : ∀ n, A n → Prop) (closed : Closed S good) :
    System k b (fun n => {x // good n x}) where
  choose j hj c :=
    let old := S.choose j hj (fun i => (c i).val)
    ⟨old.Index,old.finite,fun u => ⟨old.term u,closed j hj _ (fun i => (c i).property) u⟩⟩

/-- Forget the capacity proofs on the original input leaves. -/
def eraseLeaves {X : Type*} {p : X → Prop} : (n : ℕ) → Leaves k {x // p x} n → Leaves k X n
  | 0, x => x.val
  | n+1, x => fun i => eraseLeaves n (x i)

/-- Admissible original leaves can be supplied directly to the restricted system. -/
def liftLeaves {X : Type*} {p : X → Prop} :
    (n : ℕ) → (x : Leaves k X n) → allLeaves p n x → Leaves k {x // p x} n
  | 0, x, h => ⟨x,h⟩
  | n+1, x, h => fun i => liftLeaves n (x i) (h i)

/-- Forgetting the capacity proofs recovers the supplied input tuple exactly. -/
theorem erase_lift {X : Type*} {p : X → Prop} (n : ℕ) (x : Leaves k X n) (h : allLeaves p n x) :
    eraseLeaves n (liftLeaves n x h) = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact funext fun i => ih (x i) (h i)

private def transport (S : System k b A) {j : ℕ} (hj : j < b)
    {c c' : Fin k → A j} (h : c = c') :
    (S.choose j hj c).Index ≃ (S.choose j hj c').Index :=
  h ▸ Equiv.refl _

private theorem term_transport (S : System k b A) {j : ℕ} (hj : j < b)
    {c c' : Fin k → A j} (h : c = c') (u : (S.choose j hj c).Index) :
    (S.choose j hj c').term (transport S hj h u) = (S.choose j hj c).term u := by
  subst c'
  rfl

/-- The restricted histories are in bijection with the original histories on these leaves.
Corresponding profiles retain exactly the same physical state at the root. -/
theorem history_equiv (S : System k b A) (good : ∀ n, A n → Prop) (closed : Closed S good)
    (n : ℕ) (hn : n ≤ b) (x : Leaves k {a // good 0 a} n) :
    ∃ E : ((restrict S good closed).histories n hn x).Index ≃
        (S.histories n hn (eraseLeaves n x)).Index,
      ∀ q, state n hn (eraseLeaves n x) (E q) =
        (state (S := restrict S good closed) n hn x q).val := by
  induction n with
  | zero => exact ⟨Equiv.refl _, fun _ => rfl⟩
  | succ n ih =>
    let H := restrict S good closed
    have hj : n ≤ b := by omega
    have hl : n < b := by omega
    choose f hf using fun i : Fin k => ih hj (x i)
    let children := Equiv.piCongrRight f
    let old (p : ∀ i, (H.histories n hj (x i)).Index) :=
      fun i => (state (S := H) n hj (x i) (p i)).val
    let new (p : ∀ i, (S.histories n hj (eraseLeaves n (x i))).Index) :=
      fun i => state (S := S) n hj (eraseLeaves n (x i)) (p i)
    have childEq (p : ∀ i, (H.histories n hj (x i)).Index) : old p = new (children p) :=
      funext fun i => (hf i (p i)).symm
    let fiber (p : ∀ i, (H.histories n hj (x i)).Index) :=
      transport S hl (childEq p)
    let E := Equiv.sigmaCongr (β₁ := fun p => (S.choose n hl (old p)).Index) (β₂ := fun p => (S.choose n hl (new p)).Index) children fiber
    exact ⟨E,fun ⟨p,u⟩ => term_transport S hl (childEq p) u⟩

section Physical

open Crossing PackedHistoryCircuit.Physical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I]
    {bits : P → ℕ} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m}
    {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Program (B := B) e view) (good : ∀ n, A n → Prop) (closed : Closed F.system good)

/-- Run exactly the original placed program on the subtype of physically bounded states. -/
noncomputable def boundedProgram : Program (B := B) e
    (fun n (x : {a // good n a}) => view n x.val) where
  step i c := F.step i (fun a => (c a).val)
  advance i c q := ⟨F.advance i (fun a => (c a).val) q,
    closed i.val i.isLt _ (fun a => (c a).property) q⟩
  tensor i c q := F.tensor i (fun a => (c a).val) q
  length i c q := F.length i (fun a => (c a).val) q
  concentration i c q := F.concentration i (fun a => (c a).val) q

/-- The codec of the bounded physical program requires room only on admissible child tuples. -/
theorem boundedProgram_fits {w : ℕ → ℕ}
    (room : ∀ (i : Fin b) (c : Fin k → A i.val), (∀ a, good i.val (c a)) →
      ∀ s, matchedBlocks F i c s < 2^w i.val) : Fits (boundedProgram F good closed) w :=
  fun i c s => room i _ (fun a => (c a).property) s

/-- Applying the physical state restriction preserves every branch of the genuine
tensor expansion on the original leaf tuple, including its entire root state. -/
theorem boundedProgram_history_equiv (n : ℕ) (hn : n ≤ b) (x : Leaves k {a // good 0 a} n) :
    let R := (boundedProgram F good closed).system
    ∃ E : (R.histories n hn x).Index ≃ (F.system.histories n hn (eraseLeaves n x)).Index,
      ∀ q, state (S := F.system) n hn (eraseLeaves n x) (E q) =
        (state (S := R) n hn x q).val :=
  history_equiv F.system good closed n hn x

end Physical
end PackedHistoryCircuit.Capacity

end BorderVNP
end Computability
end OAI
