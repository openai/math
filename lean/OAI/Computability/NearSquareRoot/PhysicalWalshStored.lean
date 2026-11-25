import OAI.Computability.NearSquareRoot.PhysicalWalshGridLeaves
import OAI.Computability.NearSquareRoot.PhysicalWalshPacked

/-! # Total physical semantics of the fixed-point leaf instructions

The machine always packs the low bits of each accumulator after the signed
shift. Within its proven headroom this is exactly the rounded numerical
operation. On other inputs the stored semantics describe the actual bitstream.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshGrid

open IntegerMultiplication Code Space PhysicalWalsh KernelPass KernelPassMix

variable {a q i o : ℕ} {U X F : Type} (L : KernelScaleBank.Layout a U F) (w : U → ℕ)

/-- The physical row data for an arbitrary mixer input. Only the entries at
addresses in `L.rows` are serialized. On safe inputs the numerical formula
also describes its natural extension to any extra mathematical coordinates. -/
noncomputable def storedMix (c : Fin o → Fin i → Coefficient) (u : U) (x : Rows (layout L w) u i) :
    Rows (layout L w) u o := by
  classical
  exact if mixFits L w c u x then mix L w c u x else fun b z => packed (c b) fun j => x j z

noncomputable def storedScale (test : Column (a+1) → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → Coefficient)
    (u : U) (x : Row L w u) : Row L w u := by
  classical
  exact if scaleFits L w test table u x then scale L w test table u x else fun z =>
    KernelScaleRecord.stored (table (KernelScaleBank.signature L test u z)) (x z)

theorem storedMix_bounded (c : Fin o → Fin i → Coefficient) (u : X → U)
    (x : ∀ t, Rows (layout L w) (u t) i) :
    BoundedTask (budget L w ∘ u) (budget L w ∘ u)
      (fun t => send (packet (layout L w) (u t) (x t)))
      (fun t => send (packet (layout L w) (u t) (storedMix L w c (u t) (x t)))) := by
  let y t := storedMix L w c (u t) (x t)
  let p := fun t => packet (layout L w) (u t) (x t)
  let r := fun t => packet (layout L w) (u t) (y t)
  apply retain (budget L w ∘ u) Prod.fst Easy.fst (fun t => header L w (u t))
    (fun t => (p t).2) (fun t => (r t).2) _ _ (fun t => packet_bound L w _ _) (fun t => packet_bound L w _ _)
  have eq (t : X) (z : F) (hz : z ∈ L.rows (u t)) :
      mixMarked c (tally (w (u t)+1), List.ofFn (fun j => Dusk.mark (x t j z))) =
        List.ofFn (fun b => Dusk.mark (y t b z)) := by
    by_cases h : mixFits L w c (u t) (x t)
    · simpa [y,storedMix,h,mix] using mixMarked_exact c (fun j => x t j z) (h z hz)
    · simpa [y,storedMix,h] using packed_eq c (fun j => x t j z)
  have core := KernelPassMixBanks.bounded_mixBanks_header ([],[]) ([],[]) (mixMarked c) (mixMarked_easy c)
    (fun t => L.rows (u t)) (w ∘ u) (fun t z j => Dusk.mark (x t j z)) (fun t z b => Dusk.mark (y t b z)) 7
    (fun t z _ j => by rw [Dusk.volume]; simp only [Function.comp_apply]; omega) eq
  apply core.mono <;> intro t <;> exact Nat.mul_le_mul_left _ (by simp [Function.comp_apply])

theorem storedScale_bounded (test : Column (a+1) → Fin q → ZMod 2) (table : (Fin q → ZMod 2) → Coefficient)
    (u : X → U) (x : ∀ t, Rows (layout L w) (u t) 1) :
    BoundedTask (budget L w ∘ u) (budget L w ∘ u)
      (fun t => send (packet (layout L w) (u t) (x t)))
      (fun t => send (packet (layout L w) (u t) (fun _ : Fin 1 => storedScale L w test table (u t) (x t 0)))) := by
  let y := fun t (_ : Fin 1) => storedScale L w test table (u t) (x t 0)
  let p := fun t => packet (layout L w) (u t) (x t)
  let r := fun t => packet (layout L w) (u t) (y t)
  apply retain (budget L w ∘ u) Prod.snd Easy.snd (fun t => header L w (u t))
    (fun t => (p t).2) (fun t => (r t).2) _ _ (fun t => packet_bound L w _ _) (fun t => packet_bound L w _ _)
  have core := KernelScaleBank.storedBank_bounded (reindex L u) test table (w ∘ u) (fun t => x t 0)
  have eq (t : X) (z : F) (hz : z ∈ L.rows (u t)) :
      KernelScaleRecord.stored (table (KernelScaleBank.signature L test (u t) z)) (x t 0 z) = y t 0 z := by
    by_cases h : scaleFits L w test table (u t) (x t 0)
    · exact (KernelScaleRecord.stored_eq_rounded _ _ (h z hz)).trans (by simp [y,storedScale,h,scale])
    · simp [y,storedScale,h]
  apply (core.mono (time' := budget L w ∘ u) (space' := budget L w ∘ u)
    (fun _ => Nat.mul_le_mul_right _ (Nat.le_succ _)) (fun _ => Nat.mul_le_mul_right _ (Nat.le_succ _))).conform
    (fun _ => rfl) (fun _ => rfl)
  · intro t
    simp [p,layout,packet,KernelScaleBank.bank,reindex,header,KernelScaleBank.header,
        KernelScaleBank.width,Function.comp_def,List.ofFn_succ]
  · intro t
    simp only [r,packet,layout,KernelScaleBank.bank, List.ofFn_succ, List.ofFn_zero]
    congr 2
    exact congrArg (fun r : List Dusk.Pair => [r]) (List.map_congr_left (fun z hz => congrArg Dusk.mark (eq t z hz)))

variable (xor : Fin (a+1) × Fin (a+1) → ∀ u, Row L w u → Row L w u)
  (child : Fin (a+1) → ∀ u, Row L w u → Row L w u)
  (xorReady : Fin (a+1) × Fin (a+1) → ∀ u, Row L w u → Prop)
  (childReady : Fin (a+1) → ∀ u, Row L w u → Prop)

noncomputable def storedOps : Ops (a+1) (layout L w) where
  mix := storedMix L w
  xor := xor
  scale := fun _ test table => storedScale L w test table
  child := child

def storedGuards : Guards (a+1) (layout L w)
  | _, _, .xor g, u, x => xorReady g u (x 0)
  | _, _, .child a, u, x => childReady a u (x 0)
  | _, _, _, _, _ => True

/-- Compilation of the stored semantics requires no arithmetic bounds. -/
theorem storedLeaves {m : Meter U} (hb : ∀ u, budget L w u ≤ m.arena u) (u : X → U)
    (xrun : ∀ g (x : ∀ t, Rows (layout L w) (u t) 1), (∀ t, xorReady g (u t) (x t 0)) →
      OpenRun m 0 u (fun t => send (packet (layout L w) (u t) (x t)))
        (fun t => send (packet (layout L w) (u t) (fun _ : Fin 1 => xor g (u t) (x t 0)))))
    (crun : ∀ axis (x : ∀ t, Rows (layout L w) (u t) 1), (∀ t, childReady axis (u t) (x t 0)) →
      OpenRun m 1 u (fun t => send (packet (layout L w) (u t) (x t)))
        (fun t => send (packet (layout L w) (u t) (fun _ : Fin 1 => child axis (u t) (x t 0))))) :
    LeafRuns m (storedOps L w xor child) (storedGuards L w xorReady childReady) X u := by
  intro i o p leaf x ready
  cases p with
  | mix c => exact OpenRun.closed ((storedMix_bounded L w c u x).mono
      (fun t => (hb (u t)).trans (m.arena_le _)) (fun t => hb (u t)))
  | scale _ t c => exact OpenRun.closed ((storedScale_bounded L w t c u x).mono
      (fun t => (hb (u t)).trans (m.arena_le _)) (fun t => hb (u t)))
  | xor g => exact xrun g x ready
  | child a => exact crun a x ready
  | seq _ _ => cases leaf
  | parallel _ _ => cases leaf

/-- Sequential intermediate results agree whenever their own reached banks
satisfy the numerical headroom checks. -/
theorem stored_eq_rounded (p : Plan (a+1) i o) (u : U) (x : Rows (layout L w) u i)
    (ready : Ready (ops L w xor child) (guards L w xorReady childReady) p u x) :
    (storedOps L w xor child).applyPlan p u x = (ops L w xor child).applyPlan p u x := by
  induction p with
  | mix c =>
    have fit : mixFits L w c u x := ready
    simp only [Ops.applyPlan, storedOps, ops, storedMix, fit, ↓reduceIte]
  | scale q t c =>
    have fit : scaleFits L w t c u (x 0) := ready
    simp only [Ops.applyPlan, storedOps, ops, storedScale, fit, ↓reduceIte]
  | xor _ | child _ => rfl
  | seq p q hp hq =>
    simp only [Ops.applyPlan]
    rw [hq x ready.1]
    exact hp _ ready.2
  | parallel p q hp hq =>
    simp only [Ops.applyPlan]
    rw [hp _ ready.1, hq _ ready.2]

end PhysicalWalshGrid

end NearSquareRoot
end Computability
end OAI
