import OAI.Computability.VPVNP.EvaluatorWeightedStep
import OAI.Computability.VPVNP.EvaluatorProgramRawSafety
import OAI.Computability.VPVNP.SpaceRunMonotone

/-!
# Independent time and space bounds for a weighted matrix step

The index choice, field multiplication and ordinal commit use short clocks.
The entry query supplies its own space-bounded execution. Consequently the
query's potentially exponential running time never enters the stack capacity.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.WeightedStep

open RAMTape SliceArithmetic EvaluatorRoutineSafety
open EvaluatorChronologicalLoop (stackFits)

variable {P Q : Type} [DecidableEq Q] {p e w v : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K] {c : Vector p e}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K)
    (ports : Port P → Q) (hp : Function.Injective ports) (ambient : Stacks Q)
    (extra : Stacks P) (dim : BurstRAM.Word v)

local notation "word" j => BurstRAM.wordBits (Fin.castLE dim.isLt.le j : BurstRAM.Word v)
local notation "frame" => installStacks ports ambient
local notation "bankAt" => (fun (i : Fin dim.val) (j q : List Bool) (a : K) ↦ frame (bank φ w dim i j q a extra))

/-- At call boundaries the largest field stream occupies one working word
per extension coefficient. -/
def bankSpace (v e w extraSpace : ℕ) := v + e + w + e*w + extraSpace

omit [DecidableEq Q] in
theorem bank_length (extraSpace : ℕ) (hextra : ∀ k, (extra k).length ≤ extraSpace)
    (i : Fin dim.val) (next query : List Bool) (hn : next.length ≤ v) (hq : query.length ≤ e*w) (a : K) :
    stackFits (bankSpace v e w extraSpace) (bank φ w dim i next query a extra) := by
  intro k
  cases k with
  | indices k => cases k <;> simp [bank, IndexRegisters.bank, bankSpace] <;> omega
  | arithmetic k =>
    rcases k with k | k
    · exact Nat.zero_le _
    · cases k <;> simp [bank, MultiplyCall.clean, MultiplyCall.external, bits, bankSpace] <;> omega
  | width => simp [bank, bankSpace]; omega
  | aux k => exact (hextra k).trans (by unfold bankSpace; omega)

/-- Space reserved for the short subroutines. -/
def localTicks (v e w : ℕ) := (10*v+5) + MultiplyCall.callCap e w + (5*v+3)

include hp in
private theorem select_bounded (cap : ℕ) (s : Fin dim.val × K)
    (hroom : ∀ k, (bankAt s.1 [] [] s.2 k).length + (10*v+5) ≤ cap) :
    Bounded (IndexRegisters.select.onPorts (ports ∘ Port.indices)).body (stackFits cap)
      (fun _ : Unit ↦ bankAt s.1 [] [] s.2) (fun j : Fin dim.val ↦ bankAt s.1 (word j) [] s.2) (10*v+5) := by
  let m := ports ∘ Port.indices
  have hm : Function.Injective m := hp.comp (fun _ _ h ↦ Port.indices.inj h)
  let base := bankAt s.1 [] [] s.2
  let localBank (next : List Bool) := IndexRegisters.bank (BurstRAM.wordBits dim) (word s.1) next
  have eq (next : List Bool) : installStacks m base (localBank next) = bankAt s.1 next [] s.2 := by
    apply installStacks_frame hm
    · intro k; exact installStacks_at hp ..
    · intro k hk
      by_cases h : ∃ t, ports t = k
      · obtain ⟨t, rfl⟩ := h
        dsimp only [base]
        rw [installStacks_at hp, installStacks_at hp]
        cases t with
        | indices x => exact (hk x rfl).elim
        | arithmetic | width | aux => rfl
      · exact (installStacks_outside _ _ (not_exists.mp h)).trans
          (installStacks_outside _ _ (not_exists.mp h)).symm
  have h : Bounded IndexRegisters.select.body (stackFits cap) (fun _ : Unit ↦ localBank [])
      (fun j : Fin dim.val ↦ localBank (word j)) (10*v+5) := by
    intro reserve fuel hf _ cont hc
    have hr := IndexRegisters.select_safe dim (word s.1) (stackFits cap) cont (fuel-(10*v+5))
      (fun u hu k ↦ (hu k).trans (by
        have hh := hroom (m k)
        simp only [m, Function.comp_apply, installStacks_at hp] at hh
        exact hh)) (fun j ↦ hc j _ (by omega))
    rwa [Nat.sub_add_cancel (by omega)] at hr
  have lift := Bounded.onPorts_frame IndexRegisters.select m (installStacks m base)
    (fun _ _ ↦ installStacks_at hm ..) (installStacks_update hm base)
    (large := stackFits cap) (fun u hu k ↦ by
      by_cases hh : ∃ a, m a = k
      · obtain ⟨a, rfl⟩ := hh; rw [installStacks_at hm]; exact hu a
      · rw [installStacks_outside _ _ (not_exists.mp hh)]
        exact (Nat.le_add_right _ _).trans (hroom k)) h
  intro reserve fuel hf x cont hc
  have hsafe := lift reserve fuel hf x cont (fun j k hk ↦ by
    rw [Function.comp_apply, eq]
    exact hc j k hk)
  rwa [Function.comp_apply, eq] at hsafe

include hp in
/-- From a space-bounded scalar reader, the whole callback returns a legal
weighted payload on every nonrejecting branch within its stated clock. -/
theorem callback_bounded (he : 0 < e) (hw : Word.workingWidth p ≤ w) (read : FiniteRoutine Q)
    (matrix : Matrix (Fin dim.val) (Fin dim.val) K) (cap queryTicks : ℕ)
    (hroom : ∀ (i : Fin dim.val) (next query : List Bool), next.length ≤ v → query.length ≤ e*w →
      ∀ (a : K) k, (bankAt i next query a k).length + localTicks v e w ≤ cap)
    (hread : ∀ (s : Fin dim.val × K) (j : Fin dim.val), ∃ d ≤ queryTicks,
      read.BoundedRun cap d (bankAt s.1 (word j) [] s.2)
        (bankAt s.1 (word j) (bits φ w (matrix s.1 j)) s.2)) :
    Bounded (callback ports read).body (stackFits cap)
      (fun s : Fin dim.val × K ↦ bankAt s.1 [] [] s.2)
      (fun s : Fin dim.val × K ↦ bankAt s.1 [] [] s.2) (ticks v e w queryTicks) := by
  let chosen (x : (Fin dim.val × K) × Fin dim.val) := bankAt x.1.1 (word x.2) [] x.1.2
  let entry (x : (Fin dim.val × K) × Fin dim.val) := bankAt x.1.1 (word x.2) (bits φ w (matrix x.1.1 x.2)) x.1.2
  let product (x : (Fin dim.val × K) × Fin dim.val) := bankAt x.1.1 (word x.2) [] (x.1.2*matrix x.1.1 x.2)
  have select : Bounded (IndexRegisters.select.onPorts (ports ∘ Port.indices)).body (stackFits cap)
      (fun s : Fin dim.val × K ↦ bankAt s.1 [] [] s.2) chosen (10*v+5) := by
    intro reserve fuel hf s cont hc
    exact select_bounded φ ports hp ambient extra dim cap s (fun k ↦ by
      have hh := hroom s.1 [] [] (by simp) (by simp) s.2 k
      unfold localTicks at hh; omega) reserve fuel hf () cont (fun j ↦ hc (s,j))
  have query : Bounded read.body (stackFits cap) chosen entry queryTicks :=
    Bounded.of_space_runs (g := id) (fun x ↦ hread x.1 x.2)
  have mul : Bounded (MultiplyCall.machine.onPorts (ports ∘ Port.arithmetic)).body (stackFits cap)
      entry product (MultiplyCall.callCap e w) := by
    apply Bounded.of_runs_with_room (g := id)
    · intro x; exact multiply_framed φ ports hp ambient extra dim he hw x.1.1 x.2 x.1.2 _
    · intro x u hu k
      have hh := hroom x.1.1 (word x.2) (bits φ w (matrix x.1.1 x.2)) (by simp) (by simp [bits]) x.1.2 k
      have h := hu k; dsimp only [entry] at h; dsimp only at hh; unfold localTicks at hh; omega
  have commit : Bounded (IndexRegisters.commit.onPorts (ports ∘ Port.indices)).body (stackFits cap)
      product (fun s : Fin dim.val × K ↦ bankAt s.1 [] [] s.2) (5*v+3) := by
    apply Bounded.of_runs_with_room (g := fun x ↦ (x.2, x.1.2*matrix x.1.1 x.2))
    · intro x; exact ⟨_, le_rfl, commit_framed φ ports hp ambient extra dim x.1.1 x.2 _⟩
    · intro x u hu k
      have hh := hroom x.1.1 (word x.2) [] (by simp) (by simp) (x.1.2*matrix x.1.1 x.2) k
      have h := hu k; dsimp only [product] at h; dsimp only at hh; unfold localTicks at hh; omega
  exact ((select.followedBy query).followedBy mul).followedBy commit

end Evaluator.WeightedStep

end VPVNP
end Computability
end OAI
