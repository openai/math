import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites
import OAI.Computability.BorderVNP.PackedInheritedWorkReplay
import OAI.Computability.BorderVNP.PackedHistoryNormalizedBits

/-! # Physical readback along the complete selected outer history

Each local guess is the canonical inner histogram word of the actual epoch.
The outer circuit applies its step to the previously evaluated child banks.
Its terminal private programs are the recursively installed programs on this
very pack-history term, with all subdivisions and dense saves included.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open Crossing Cover Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited PublicCapacity
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m start T : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
variable {W : ℕ → Type} [∀ t, Fintype (W t)] {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)]
variable {w : ℕ → ℕ → ℕ} {good : ∀ t, EnrichedOuter.State S start P bits shape W t → Prop}
variable {deep : S.floor+1+S.drop*T ≤ start} (M : Machine.{0,u} deep good V w)

variable (bottom : Admissible good 0)

variable {Z : ℕ → Type} [∀ t, Fintype (Z t)] (steps : Steps (fan S) T Z (Guess S start w))
variable (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)
variable (read : ∀ n (a : Admissible good n), Site.Programs a.val.pack.layout → (Z n → Bool) → Prop)

/-- On the canonical history bits, the actual compiled outer tree satisfies
the same readback property of the real private programs proved by its
subdivision, inner tree and terminal placement at each active epoch. -/
theorem private_pack_output {σ : Type} [Fintype σ] (f : Frame σ (Z 0)) (x : σ → Bool)
    (base : Site.Programs bottom.val.pack.layout) (leaf : read 0 bottom base (f.eval x))
    (next : ∀ (n : ℕ) (hn : n<T) (c : Fin (fan S) → Admissible good n)
      (old : ∀ i, Site.Programs (c i).val.pack.layout) (y : Fin (fan S) → Z n → Bool),
      (∀ i, read n (c i) (old i) (y i)) → ∀ q : (M.epoch n c).Index,
      read (n+1) ((M.epoch n c).term q) (M.stepPrivatePrograms rows number hn c old q)
        (fun z => (steps n hn).eval (Sum.elim (fun j => y j.1 j.2) (M.epochBits hn c q)) (.inl z)))
    (n : ℕ) (hn : n ≤ T) (q : (packHistory bottom M.epoch n).Index) :
    read n ((packHistory bottom M.epoch n).term q) (M.historyPrivatePrograms rows number bottom base n hn q)
      (output steps n hn (repeatLeaf (fan S) f n) x (M.packBits bottom n hn q)) := by
  induction n with
  | zero =>
    have hz := output_zero steps f x (M.packBits bottom 0 hn q)
    exact hz.symm ▸ leaf
  | succ n ih =>
    let h := Nat.lt_of_succ_le hn
    let c (i : Fin (fan S)) := (packHistory bottom M.epoch n).term (q.1 i)
    let old (i : Fin (fan S)) := M.historyPrivatePrograms rows number bottom base n h.le (q.1 i)
    let y (i : Fin (fan S)) := output steps n h.le (repeatLeaf (fan S) f n) x (M.packBits bottom n h.le (q.1 i))
    have localRead (i : Fin (fan S)) : read n (c i) (old i) (y i) := ih h.le (q.1 i)
    have he : output steps (n+1) hn (repeatLeaf (fan S) f (n+1)) x (M.packBits bottom (n+1) hn q) =
        fun z => (steps n h).eval (Sum.elim (fun j => y j.1 j.2) (M.epochBits h c q.2)) (.inl z) :=
      funext (output_succ steps n hn (repeatLeaf (fan S) f (n+1)) x (M.packBits bottom (n+1) hn q))
    rw [he]
    exact next n h c old y localRead q.2

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
