import OAI.Computability.NearSquareRoot.KernelEffectiveMixBankPacket
import OAI.Computability.NearSquareRoot.KernelEffectiveMixParameters
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSound
import OAI.Computability.NearSquareRoot.PhysicalWalshContext

/-! # Soundness of a generated matrix mixer in the recursive stream grammar

The command runs on the full routed packet, keeping its recursion descriptor.
The clock for physically replicating the width ruler fits the local arena,
so the same command also admits bounded live data and return stacks.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveMixBank

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshContext
open KernelPass KernelPass.ComputableSyntax KernelPassMix

variable {U F X D H : Type} [Codec H] [Codec D] {a i o : ℕ}

/-- The two arithmetic rulers are the first two fields of the grid header. -/
def routeKey (D : Type) (h : PhysicalWalshGrid.Header × D) : Rulers := h.1.1

/-- Lift the witnessed run of the very same command to a bounded open call
without consuming a child allowance. -/
theorem Sound.runs {cmd : Cmd} {key : H → Rulers} {f : RowFunction}
    (h : Sound cmd key i o f) (m : Meter U) (u : X → U) (z : X → H × Bank)
    (K : ℕ) (volume : ∀ x, expense key (z x) ≤ K*(m.arena (u x)+1)) :
    PhysicalWalsh.Runs cmd m 0 u (fun x => send (z x))
      (fun x => send (answer key i o f (z x))) := by
  obtain ⟨C, run⟩ := h
  refine ⟨(C+1)*(K+1), fun x env t s _ p base cap => ?_⟩
  have e : expense key (z x) + 1 ≤ (K+1)*(m.arena (u x)+1) := by
    rw [Nat.succ_mul]; have := volume x; omega
  have bytes : size (z x) ≤ expense key (z x) := Nat.le_add_right ..
  have localBound : size (z x) + C*(expense key (z x)+1) ≤ (C+1)*(K+1)*(m.arena (u x)+1) := calc
    _ ≤ (C+1)*(expense key (z x)+1) := by rw [Nat.succ_mul]; omega
    _ ≤ _ := (Nat.mul_le_mul_left (C+1) e).trans_eq (Nat.mul_assoc ..).symm
  have time : (C+1)*(K+1)*(m.arena (u x)+1) ≤ (C+1)*(K+1)*(m.scan (u x)+1) :=
    Nat.mul_le_mul_left _ (Nat.succ_le_succ (m.arena_le (u x)))
  apply (BoundedFits.of_fits (run (z x) env p)
    (cap := base + ((C+1)*(K+1)*(m.arena (u x)+1)+s))
    (depth := (C+1)*(K+1)*(m.arena (u x)+1)+s) ?_ (by omega)).mono (by omega) le_rfl le_rfl
  intro j
  have start := (cap.pile 0 (send (z x))) j
  change _ ≤ base + size (z x) at start
  omega

variable (L : KernelScaleBank.Layout a U F) (w : U → ℕ) (desc : U → D)
  {m : Meter U} (fit : ∀ s, routeArena L w desc s ≤ m.arena s)

include fit in
private theorem expense_packet (s : U) (x : Rows (routeLayout L w desc) s i) :
    expense (routeKey D) (packet (routeLayout L w desc) s x) ≤ (i+6)*(m.arena s+1) := by
  have bankBound := (fitsLayout L w desc fit).packet s x
  have gr : PhysicalWalshGrid.budget L w s ≤ m.arena s := by
    apply le_trans _ (fit s)
    unfold routeArena
    omega
  have cpu : ((L.rows s).length+1)*size (tally (w s+1)) ≤ 3 * PhysicalWalshGrid.budget L w s := by
    simp only [size_tally,tally_length,PhysicalWalshGrid.budget]
    ring_nf
    omega
  have hG := Nat.mul_le_mul_left 3 gr
  change size (packet (routeLayout L w desc) s x) +
    ((tally (L.rows s).length).length+1)*size (tally (w s+1)) ≤ _
  rw [tally_length]
  rw [Nat.add_mul i 3] at bankBound
  rw [Nat.add_mul i 6]
  omega

omit [Codec D] in
private theorem answer_mix (c : Fin o → Fin i → Coefficient) (s : U)
    (x : Rows (routeLayout L w desc) s i) (room : PhysicalWalshGrid.mixFits L w c s x) :
    answer (routeKey D) i o (mixMarked c) (packet (routeLayout L w desc) s x) =
      packet (routeLayout L w desc) s (PhysicalWalshGrid.mix L w c s x) := by
  apply answer_bank (routeKey D) _ (L.rows s) (w s) (mixMarked c)
    (fun z b => Dusk.mark (x b z)) (fun z b => Dusk.mark (rounded (c b) (fun j => x j z))) rfl
  intro z hz
  exact mixMarked_exact c (fun j => x j z) (room z hz)

variable (xor : Fin (a+1) × Fin (a+1) → ∀ s, PhysicalWalshGrid.Row L w s → PhysicalWalshGrid.Row L w s)
  (child : Fin (a+1) → ∀ s, PhysicalWalshGrid.Row L w s → PhysicalWalshGrid.Row L w s)
  (xorReady : Fin (a+1) × Fin (a+1) → ∀ s, PhysicalWalshGrid.Row L w s → Prop)
  (childReady : Fin (a+1) → ∀ s, PhysicalWalshGrid.Row L w s → Prop)

include fit

/-- A generated, well-ranged dyadic mixer implements the typed primitive on
the layout used for recursive children and permutations. -/
theorem implements_mix (u : X → U) (c : Fin o → Fin i → Coefficient) (cmd : Cmd)
    (h : Sound cmd (routeKey D) i o (mixMarked c)) :
    PhysicalWalshCompile.Implements (routeOps L w desc xor child) (routeGuards L w desc xorReady childReady)
      m u ⟨i,o,.mix c⟩ cmd := by
  intro x room
  have run := h.runs m u (fun t => packet (routeLayout L w desc) (u t) (x t)) (i+6)
    (fun t => expense_packet L w desc fit (u t) (x t))
  change PhysicalWalsh.Runs cmd m 0 u _ (fun t => send (packet (routeLayout L w desc) (u t)
    (PhysicalWalshGrid.mix L w c (u t) (x t))))
  simpa only [answer_mix L w desc c _ _ (room _)] using run

/-- On a tag-zero opcode the compiler's typed decoder uses precisely its
row-major coefficient table. Missing entries decode as zero. -/
theorem implements_leaf_mix (u : X → U) (op : Op) (tag : op.1 = 0) (cmd : Cmd)
    (h : Sound cmd (routeKey D) (arg op 0) (arg op 1) (mixMarked (EffectiveMix.coeff op))) :
    PhysicalWalshCompile.Implements (routeOps L w desc xor child) (routeGuards L w desc xorReady childReady)
      m u (Packed.leaf (a+1) op) cmd := by
  rw [Packed.leaf, ite_eq_left tag]
  exact implements_mix L w desc fit xor child xorReady childReady u (EffectiveMix.coeff op) cmd h

end KernelEffectiveMixBank

end NearSquareRoot
end Computability
end OAI
