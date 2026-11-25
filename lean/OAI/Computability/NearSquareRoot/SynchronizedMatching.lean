import OAI.Computability.NearSquareRoot.SynchronizedPair
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fintype

/-! # Routing and synchronizing a matching of local pair gates

A matching is an injective placement of labelled, oriented pairs. Within
a block it can be permuted onto a prescribed address bit. The extra
pairs are filled with identities. All aligned pairs then use three common
Walsh rounds interleaved with diagonal phase streams.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPair

open Matrix

variable {S T : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] in
private theorem block_diag (a b : S → ℂ) :
    blockDiagonal (fun s => diag (a s) (b s)) =
      diagonal (fun x : Fin 2 × S => ![a x.2, b x.2] x.1) := by
  rw [← blockDiagonal_diagonal (fun s => ![a s, b s])]
  congr 1
  funext s
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag]

/-- Consecutive Walsh rounds act on every aligned pair, with only diagonal
phases depending on the pair. -/
theorem parallel_threeWalsh (M : S → PairMatrix) (hM : ∀ s, ThreeWalsh (M s)) :
    let H := blockDiagonal (fun _ : S => walsh)
    ∃ p q r : Fin 2 × S → ℂ,
      (∀ x, ‖p x‖ = 1 ∧ ‖q x‖ = 1 ∧ ‖r x‖ = 1) ∧
      blockDiagonal M = H * diagonal p * H * diagonal q * H * diagonal r := by
  choose a b c d e f ha hb hc hd he hf hm using hM
  dsimp only
  refine ⟨fun x => ![a x.2, b x.2] x.1, fun x => ![c x.2, d x.2] x.1,
    fun x => ![e x.2, f x.2] x.1, ?_, ?_⟩
  · rintro ⟨i, s⟩
    fin_cases i <;> simp [ha, hb, hc, hd, he, hf]
  · rw [← block_diag, ← block_diag, ← block_diag]
    simp only [← blockDiagonal_mul]
    exact congrArg blockDiagonal (funext hm)

/-- A block-local permutation aligns every active pair. The completed family
takes the specified value on each such pair and is the identity elsewhere. -/
theorem align_matching [Fintype T] (src : Fin 2 × T ↪ Fin 2 × S) (M : T → PairMatrix)
    (hM : ∀ t, ThreeWalsh (M t)) :
    ∃ (label : T ↪ S) (route : Equiv.Perm (Fin 2 × S)) (table : S → PairMatrix),
      (∀ t bit, route (src (bit, t)) = (bit, label t)) ∧
      (∀ t, table (label t) = M t) ∧ (∀ s ∉ Set.range label, table s = 1) ∧
      ∀ s, ThreeWalsh (table s) := by
  classical
  have hc := Fintype.card_le_of_embedding src
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  obtain ⟨label⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card T ≤ Fintype.card S by omega)
  let aligned (x : Fin 2 × T) : Fin 2 × S := (x.1, label x.2)
  have hinj : Function.Injective aligned := by
    intro x y h
    have hx : x.1 = y.1 := congrArg (fun p : Fin 2 × S => p.1) h
    have hy : label x.2 = label y.2 := congrArg (fun p : Fin 2 × S => p.2) h
    exact Prod.ext hx (label.injective hy)
  obtain ⟨route, hr⟩ := Equiv.Perm.exists_extending_pair src aligned src.injective hinj
  let table := Function.extend label M fun _ => 1
  have on (t : T) : table (label t) = M t := label.injective.extend_apply ..
  have off (s : S) (hs : s ∉ Set.range label) : table s = 1 :=
    Function.extend_apply' _ _ _ hs
  refine ⟨label, route, table, fun t bit => hr (bit, t), on, off, fun s => ?_⟩
  by_cases hs : s ∈ Set.range label
  · obtain ⟨t, rfl⟩ := hs
    rw [on]
    exact hM t
  · rw [off _ hs]
    exact identity_threeWalsh

end SynchronizedPair

end NearSquareRoot
end Computability
end OAI
