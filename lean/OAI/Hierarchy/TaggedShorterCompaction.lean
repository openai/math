import OAI.ThreeFlat.Routing.SpillCompaction

namespace OAI
/-! # Two levels of checked compaction for a shorter tagged-call pool

The inner switches pack the two endpoint lists independently at each candidate
batch. The outer switches carry both entire lists as one word. All the networks
and pins are fixed before the activity masks and payloads are known.
-/

noncomputable section
namespace Hierarchy.TaggedShorterCompaction
open ThreeFlat Routing Spill
open scoped Classical BigOperators

abbrev Pair (H m : ℕ) := Bool × RecordPins H m
abbrev Width (H m : ℕ) := Fintype.card (Pair H m)
abbrev Input (S D m : ℕ) := Fin S ⊕ (Fin S × Bool × RecordPins D m)
abbrev Output (M H m : ℕ) := RecordPins M (Width H m)
abbrev Bus (S H m : ℕ) := Fin S × Pair H m

def row {S D m : ℕ} (x : Input S D m → Bool) (s : Fin S) (b : Bool) :
    RecordPins D m → Bool := fun p => x (.inr (s,b,p))

def packedPairs {S D H m : ℕ} (x : Input S D m → Bool) (y : Bus S H m → Bool) :
    RecordPins S (Width H m) → Bool
  | (s,none) => x (.inl s)
  | (s,some j) => y (s,(Fintype.equivFin (Pair H m)).symm j)

private def Port (S D H M m : ℕ) : Option (Fin S × Bool) → Type
  | none => RecordPins S (Width H m) ⊕ Output M H m
  | some _ => RecordPins D m ⊕ RecordPins H m

private instance (S D H M m : ℕ) (k : Option (Fin S × Bool)) : Fintype (Port S D H M m k) := by
  cases k <;> dsimp [Port] <;> infer_instance

private def wire (S D H M m : ℕ) : (k : Option (Fin S × Bool)) →
    Port S D H M m k → (Input S D m ⊕ Output M H m) ⊕ Bus S H m
  | none, .inl (s,none) => .inl (.inl (.inl s))
  | none, .inl (s,some j) => .inr (s,(Fintype.equivFin (Pair H m)).symm j)
  | none, .inr p => .inl (.inr p)
  | some (s,b), .inl p => .inl (.inl (.inr (s,b,p)))
  | some (s,b), .inr p => .inr (s,b,p)

variable {F : Type*} [CommSemiring F] {S D H M m : ℕ}
variable (near : Compactor F D H m) (far : Compactor F S M (Width H m))

private def part : (k : Option (Fin S × Bool)) → BitNetwork F (Fintype.card (Port S D H M m k))
  | none => far.network
  | some _ => near.network

def network := TypedWiring.glue (part near far) (wire S D H M m)

theorem network_cells : (network near far).cells = far.network.cells + (2*S)*near.network.cells := by
  simp [network,TypedWiring.glue_cells,Fintype.sum_option,part,Nat.mul_comm]

/-- The two switches' intermediate outputs are summed. Whenever every local
list is legal, precisely its deterministic output reaches the next level. -/
theorem network_eval (x : Input S D m → Bool) (z : Output M H m → Bool)
    (y : Bus S H m → Bool)
    (hits : ∀ s b, near.run (row x s b) = some (fun p => y (s,b,p))) :
    TypedWiring.value (network near far) (Sum.elim x z) =
      if far.run (packedPairs x y) = some z then 1 else 0 := by
  classical
  let : DecidableEq (Bus S H m) := Classical.decEq _
  rw [network,TypedWiring.glue_value]
  let val (s : Option (Fin S × Bool)) (v : Bus S H m → Bool) :=
    TypedWiring.value (part near far s)
      (fun p => Sum.elim (Sum.elim x z) v (wire S D H M m s p))
  have inner (s : Fin S) (b : Bool) (v : Bus S H m → Bool) :
      val (some (s,b)) v = if (fun p => y (s,b,p)) = (fun p => v (s,b,p)) then 1 else 0 := by
    have pins : (fun p => Sum.elim (Sum.elim x z) v (wire S D H M m (some (s,b)) p)) =
        Sum.elim (row x s b) (fun p => v (s,b,p)) := by funext p; cases p <;> rfl
    calc
      _ = TypedWiring.value near.network (Sum.elim (row x s b) (fun p => v (s,b,p))) := congrArg (TypedWiring.value near.network) pins
      _ = _ := by simpa only [hits,Option.some.injEq] using near.checked (row x s b) (fun p => v (s,b,p))
  have outer (v : Bus S H m → Bool) : val none v =
      if far.run (packedPairs x v) = some z then 1 else 0 := by
    have pins : (fun p => Sum.elim (Sum.elim x z) v (wire S D H M m none p)) =
        Sum.elim (packedPairs x v) z := by
      funext p
      rcases p with ⟨s,_ | j⟩ | p <;> rfl
    exact (congrArg (TypedWiring.value far.network) pins).trans (far.checked _ _)
  change (∑ v, ∏ s, val s v) = _
  rw [Finset.sum_eq_single y]
  · rw [Fintype.prod_option,outer]
    suffices (∏ sb : Fin S × Bool, val (some sb) y) = 1 by rw [this,mul_one]
    exact Finset.prod_eq_one fun ⟨s,b⟩ _ => (inner s b y).trans (ite_eq_left rfl)
  · intro v _ ne
    obtain ⟨⟨s,b,p⟩,bad⟩ := Function.ne_iff.mp ne
    apply Finset.prod_eq_zero (Finset.mem_univ (some (s,b)))
    exact (inner s b v).trans (ite_eq_right (fun eq => bad (congrFun eq p).symm))
  · simp

/-- There is only one physical output, and both compaction layers conserve the
complete records, even when distinct links carry the same bit string. -/
theorem routes (x : Input S D m → Bool)
    (localFit : ∀ s b, 2*(occupied (row x s b)).card ≤ H)
    (poolFit : 2*(Finset.univ.filter (fun s : Fin S => x (.inl s) = true)).card ≤ M) :
    ∃ y : Bus S H m → Bool, ∃ z : Output M H m → Bool,
      (∀ s b, payloads (fun p => y (s,b,p)) = payloads (row x s b) ∧
        ZeroBlanks (fun p => y (s,b,p))) ∧
      payloads z = payloads (packedPairs x y) ∧ ZeroBlanks z ∧
      ∀ z', TypedWiring.value (network near far) (Sum.elim x z') = if z = z' then 1 else 0 := by
  choose sides hits using fun s b => near.complete (row x s b) (localFit s b)
  let y : Bus S H m → Bool := fun p => sides p.1 p.2.1 p.2.2
  obtain ⟨z,hz⟩ := far.complete (packedPairs x y) poolFit
  refine ⟨y,z,fun s b => ⟨near.preserves _ _ (hits s b),near.normalized _ _ (hits s b)⟩,
    far.preserves _ _ hz,far.normalized _ _ hz,?_⟩
  intro z'
  by_cases heq : z = z' <;> simp [network_eval near far x z' y hits,hz,heq]

/-- Both layouts are purchased at their actual slot counts. The second
network moves a pair of lists, including an activity bit per record. -/
theorem exists_layouts (F : Type*) [CommSemiring F] :
    ∃ cutoff c : ℕ, ∀ (S D H M m : ℕ), 0 < H → H ≤ D → cutoff ≤ 2*H →
      0 < M → M ≤ S → cutoff ≤ 2*M →
      ∃ (near : Compactor F D H m) (far : Compactor F S M (Width H m)),
        (network near far).cells ≤ S*(Nat.log 2 S+2*(H*(m+1))+4)*c +
          (2*S)*(D*(Nat.log 2 D+m+4)*c) := by
  obtain ⟨cut,c,build⟩ := exists_sparse_compactors F
  refine ⟨cut,c,fun S D H M m hH hHD hN hM hMS hF => ?_⟩
  obtain ⟨near,hnear⟩ := build D H m hH hHD hN
  obtain ⟨far,hfar⟩ := build S M (Width H m) hM hMS hF
  refine ⟨near,far,?_⟩
  rw [network_cells]
  have hw : Width H m = 2*(H*(m+1)) := by simp [Width,Pair,RecordPins,SlotBits]
  rw [←hw]
  exact Nat.add_le_add hfar (Nat.mul_le_mul_left _ hnear)

end Hierarchy.TaggedShorterCompaction

end
end OAI
