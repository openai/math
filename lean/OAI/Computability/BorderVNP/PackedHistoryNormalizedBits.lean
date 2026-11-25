import OAI.Computability.BorderVNP.PackedHistoryNormalizedMachine

/-! # Chronological words of the native enriched pack history

Each outer history stores the ordered tuple of child choices and an inner
histogram for those exact children. Concatenating their words in circuit slot
order recovers every choice, including choices with equal terminal states.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open VPVNP.VerifierNetwork Crossing Cover Epoch.Round Shortening Shortening.Adaptive Packing PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m start T : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
variable {W : ℕ → Type} [∀ t, Fintype (W t)] {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)]
variable {w : ℕ → ℕ → ℕ} {good : ∀ t, EnrichedOuter.State S start P bits shape W t → Prop}
variable {deep : S.floor+1+S.drop*T ≤ start} (M : Machine deep good V w)

/-- The true inner count word on the active branch of the public outer epoch. -/
noncomputable def epochBits {n : ℕ} (hn : n<T) (c : Fin (fan S) → Admissible good n) :
    (M.epoch n c).Index → Guess S start w n → Bool :=
  let same : M.epoch n c = (M n hn).choice c := dite_eq_left hn
  ((M n hn).run c).word (M n hn).room ∘ Equiv.cast (congrArg ProfileSum.Index same)

theorem epochBits_injective {n : ℕ} (hn : n<T) (c : Fin (fan S) → Admissible good n) :
    Function.Injective (M.epochBits hn c) := by
  unfold epochBits
  exact ((M n hn).run c).word_injective (M n hn).room |>.comp (Equiv.cast _).injective

variable (bottom : Admissible good 0)

/-- The joint guess assignment in tree order for the actual pack-history index. -/
noncomputable def packBits :
    (n : ℕ) → n ≤ T → (packHistory bottom M.epoch n).Index → Slot (fan S) (Guess S start w) n → Bool
  | 0, _, _, z => z.elim
  | n+1, hn, q, .inl (i,z) => packBits n (Nat.le_of_succ_le hn) (q.1 i) z
  | n+1, hn, q, .inr z => M.epochBits (Nat.lt_of_succ_le hn)
      (fun i => (packHistory bottom M.epoch n).term (q.1 i)) q.2 z

theorem packBits_injective (n : ℕ) (hn : n ≤ T) : Function.Injective (M.packBits bottom n hn) := by
  induction n with
  | zero => intro q q' _; exact Subsingleton.elim (α := PUnit) q q'
  | succ n ih =>
    rintro ⟨c,u⟩ ⟨d,v⟩ eq
    have hc : c = d := funext fun i =>
      ih (Nat.le_of_succ_le hn) (funext fun j => congrFun eq (.inl (i,j)))
    subst d
    have hu := M.epochBits_injective hn (fun i => (packHistory bottom M.epoch n).term (c i))
      (a₁ := u) (a₂ := v) (funext fun j => congrFun eq (.inr j))
    subst v
    rfl

private theorem term_cast {A : Type*} {p q : ProfileSum A} (h : p = q) (i : p.Index) :
    q.term (Equiv.cast (congrArg ProfileSum.Index h) i) = p.term i := by cases h; rfl

/-- Checking the native transcript accepts and reconstructs the state of the
same history at every subtree. -/
theorem packBits_correct {X : Type*} [Fintype X] (f : Frame X (W 0)) (x : X → Bool)
    (initial : f.eval x = bottom.val.words) (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom M.epoch n).Index) :
    flag M.steps n hn (repeatLeaf (fan S) f n) x (M.packBits bottom n hn q) = true ∧
    output M.steps n hn (repeatLeaf (fan S) f n) x (M.packBits bottom n hn q) =
      ((packHistory bottom M.epoch n).term q).val.words := by
  induction n with
  | zero => exact ⟨flag_zero M.steps f x _, (output_zero M.steps f x _).trans initial⟩
  | succ n ih =>
    let h := Nat.lt_of_succ_le hn
    let c (i : Fin (fan S)) := (packHistory bottom M.epoch n).term (q.1 i)
    let y (i : Fin (fan S)) := output M.steps n h.le (repeatLeaf (fan S) f n) x (M.packBits bottom n h.le (q.1 i))
    have reps (i) : represents (good := good) n (y i) (c i) := (ih h.le (q.1 i)).2
    have same : M.epoch n c = (M n h).choice c := dite_eq_left h
    let j := Equiv.cast (congrArg ProfileSum.Index same) q.2
    have root := (M.correct.valid n h c y (M.epochBits h c q.2) reps).mpr ⟨j,rfl⟩
    have next := M.correct.next n h c y (M.epochBits h c q.2) j reps rfl
    refine ⟨(flag_succ M.steps n hn _ x _).mpr ⟨fun i => (ih h.le (q.1 i)).1,root⟩,?_⟩
    exact (funext (output_succ M.steps n hn _ x _)).trans
      (next.trans (congrArg (fun a : Admissible good (n+1) => a.val.words) (term_cast same q.2)))

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
