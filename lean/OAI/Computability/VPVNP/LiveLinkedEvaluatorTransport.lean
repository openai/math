import OAI.Computability.VPVNP.LiveLinkedEvaluatorGeometry

/-!
# Preservation of the outgoing physical cut during incoming preparation

The last-group flag, the outgoing header configuration field, and the outgoing
configuration bank suffice to reuse the same output data after initialization.
The incoming gather leaves these cells unchanged by disjoint allocation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM PairStages LiveConfigGather LiveEvaluatorEncoding
open scoped Fin.CommRing

variable (G : PairStages.Group) {M : ℕ}

/-- The two memories agree on the last-group flag, all outgoing configuration bits, and every
word of the proposed output state bank. -/
structure OutputFrame (M : ℕ) (m m' : Memory G.w) : Prop where
  flag : m' ((Router.last.data G.g G.lit) 0).val = m ((Router.last.data G.g G.lit) 0).val
  field (j : Fin (fieldWords M * G.w)) : m' ((cutSource G true).val+j.val) = m ((cutSource G true).val+j.val)
  bank (i : Fin (fieldWords M)) : m' ((G.transitionPub 2).val+i.val) = m ((G.transitionPub 2).val+i.val)

namespace Output
variable {G} {m m' : Memory G.w} {b : Option (Code G.evaluator.extra M)}

/-- Reuse an outgoing cut or endpoint witness in a new memory that agrees on the output frame. -/
def transport (o : Output G m b) (frame : OutputFrame G M m m') : Output G m' b := match o with
  | .cut F bits flag img fresh hs value => .cut F bits (frame.flag.trans flag) (fun j => (frame.field j).trans (img j)) fresh hs value
  | .final flag zero fresh value => .final (frame.flag.trans flag) (fun j => (frame.bank j).trans (zero j)) fresh value

theorem transport_logs (o : Output G m b) (frame : OutputFrame G M m m') : (o.transport frame).logs = o.logs := by
  cases o <;> rfl

end Output

theorem gatherMemory_outside (F : EvaluatorGather.Fit G false (k G)) (m : Memory G.w)
    (bits : Fin (k G * G.w) → Bool) (a : ℕ) (ht : a ≠ G.addr.val)
    (outside : a < (G.transitionPub 1).val ∨ (G.transitionPub 1).val+k G ≤ a) :
    gatherMemory G false F m bits a = m a := by
  unfold gatherMemory retag
  have hsep : a < (EvaluatorGather.operands G false 1).val ∨ (EvaluatorGather.operands G false 1).val + k G ≤ a := outside
  rw [writeMemory, ite_eq_right ht, gathered_outside _ _ _ _ _ hsep, writeMemory, ite_eq_right ht]

theorem gatheredOutputFrame (a : Addresses G) (F : EvaluatorGather.Fit G false (k G)) (m : Memory G.w)
    (bits : Fin (k G * G.w) → Bool) : OutputFrame G (radius G) m (gatherMemory G false F m bits) := by
  obtain ⟨l,r,e,flag,fl,o,n,s,rad,wc,kc⟩ := a
  refine ⟨gatherMemory_outside G F m bits _ (by omega) (Or.inl (by omega)), ?_, ?_⟩
  · intro j
    have hj : j.val < k G * G.w := j.isLt
    exact gatherMemory_outside G F m bits _ (by omega) (Or.inl (by omega))
  · intro j
    exact gatherMemory_outside G F m bits _ (by omega) (Or.inr (by omega))

private theorem putMemory_outside (m : Memory G.w) (j : ℕ) (htag : j ≠ G.addr.val)
    (hbank : j ≠ (G.transitionPub 1).val) : putMemory G false m j = m j := by
  change writeMemory (writeMemory (writeMemory m G.addr _) (G.transitionPub 1) _) G.addr _ j = m j
  simp only [writeMemory, ite_eq_right htag, ite_eq_right hbank]

theorem putInitialFrame (a : Addresses G) (m : Memory G.w) : OutputFrame G (radius G) m (putMemory G false m) := by
  obtain ⟨l,r,e,flag,fl,o,n,s,rad,wc,kc⟩ := a
  have hk : 0 < k G := by dsimp [k,fieldWords]; omega
  refine ⟨putMemory_outside G m _ (by omega) (by omega), ?_, ?_⟩
  · intro j
    have hj : j.val < k G*G.w := j.isLt
    exact putMemory_outside G m _ (by omega) (by omega)
  · intro j
    exact putMemory_outside G m _ (by omega) (by omega)

/-- An empty evaluator starts in its canonical accepting state, and the
first router skips all input-tape preparation. -/
theorem empty_initial_image (m : Memory G.w) (empty : G.evaluator.extra = 0)
    (fit : GeometryFit G M) (zero : ∀ j : Fin (fieldWords M), m ((G.transitionPub 1).val+j.val) = 0)
    (c : Code G.evaluator.extra M) : LiveEvaluatorRAM.ConfigAt (putMemory G false m) (G.transitionPub 1) c ↔
      c = .accepted := by
  have hf := fit.prep.oldFit
  rw [← LiveEvaluatorGroup.fieldWords_eq_calls] at hf
  have ht : EvaluatorSentinel.tag G false = 1 := by simp [EvaluatorSentinel.tag, LiveEvaluatorInitialize.controlTag, empty]
  apply configAt_eq_iff G fit.prep.width fit.prep.states _ c
  apply LiveEvaluatorRAM.configAt_of_words fit.prep.width fit.prep.states .accepted
  intro j
  have hindex : (G.transitionPub 1 + (j.val : Word G.w)).val = (G.transitionPub 1).val+j.val := by
    rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
  rw [hindex]
  unfold putMemory EvaluatorSentinel.transferred EvaluatorSentinel.put retag
  have fresh (i : Fin (fieldWords M)) : (G.transitionPub 1).val+i.val ≠ G.addr.val := by
    have := fit.oldTag; have := i.isLt; omega
  rw [writeMemory, ite_eq_right (fresh j), ht, show EvaluatorSentinel.operands G false 1 = G.transitionPub 1 from rfl]
  apply LiveEvaluatorInitialize.final_stores fit.prep.width fit.prep.states (G.transitionPub 1) _ _ j
  intro i
  rw [writeMemory, ite_eq_right (fresh i), zero]

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
