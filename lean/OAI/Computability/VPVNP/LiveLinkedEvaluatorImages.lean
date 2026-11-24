import OAI.Computability.VPVNP.LiveLinkedEvaluatorRoutes
import OAI.Computability.VPVNP.LiveLinkedEvaluatorTransition
import OAI.Computability.VPVNP.LiveEvaluatorGatheredGroup

/-!
# Evaluator configuration images after linked routes

Tag transfers leave the disjoint configuration banks intact. Each completed
gather represents exactly its raw field, and the one-call final state writer
represents the canonical accepting halt on a blank outgoing bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM LiveStageLink PairStages LiveConfigGather LiveEvaluatorEncoding LiveEvaluatorRAM
open LiveEvaluatorGroup (fieldWords_eq_calls configAt_gathered_disjoint_iff)
open scoped Fin.CommRing

variable (G : PairStages.Group) {M : ℕ}

private theorem offset (b : Word G.w) (i : Fin (fieldWords M)) (fit : b.val+fieldWords M ≤ 2^G.w) :
    (b+(i.val : Word G.w)).val = b.val+i.val := by
  rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt (by have := i.isLt; omega)]

theorem configAt_write_iff {b addr v : Word G.w} (m : Memory G.w)
    (hw : 2 ≤ G.w) (hs : G.evaluator.extra+2 ≤ 2^G.w) (fit : b.val+fieldWords M ≤ 2^G.w)
    (fresh : addr.val < b.val ∨ b.val+fieldWords M ≤ addr.val) (c : Code G.evaluator.extra M) :
    ConfigAt (writeMemory m addr v) b c ↔ ConfigAt m b c := by
  rw [configAt_iff_words hw hs, configAt_iff_words hw hs]
  apply forall_congr'
  intro i
  have he : (b+(i.val : Word G.w)).val ≠ addr.val := by rw [offset G b i fit]; have := i.isLt; omega
  rw [writeMemory, ite_eq_right he]

/-- A native configuration image fixes the represented code uniquely. -/
theorem configAt_eq_iff {b : Word G.w} {m : Memory G.w} (hw : 2 ≤ G.w)
    (hs : G.evaluator.extra+2 ≤ 2^G.w) {c : Code G.evaluator.extra M} (h : ConfigAt m b c)
    (z : Code G.evaluator.extra M) : ConfigAt m b z ↔ z = c := by
  constructor
  · intro hz
    let f := format (M := M) hw hs
    apply Function.LeftInverse.injective f.parse_words
    exact funext fun i => ((configAt_iff_words hw hs b m z).mp hz i).symm.trans
      ((configAt_iff_words hw hs b m c).mp h i)
  · rintro rfl; exact h

/-- The just-gathered bank is valid precisely for the decoded cut value. -/
theorem gather_image (outgoing : Bool) (F : EvaluatorGather.Fit G outgoing (fieldWords M))
    (hs : G.evaluator.extra+2 ≤ 2^G.w) (m : Memory G.w) (bits : Fin (fieldWords M*G.w) → Bool)
    (c : Code G.evaluator.extra M) :
    ConfigAt (gatherMemory G outgoing F m bits) (EvaluatorGather.operands G outgoing 1) c ↔
      (format F.width hs).decode bits = some c :=
  (configAt_write_iff G _ F.width hs F.dest F.tagOutside c).trans (gathered_configAt_iff ..)

/-- The incoming evaluator image survives all outgoing gather and router writes. -/
theorem gather_frame (F : EvaluatorGather.Fit G true (fieldWords M)) (m : Memory G.w)
    (bits : Fin (fieldWords M*G.w) → Bool) (hl : PrepLayout G.evaluator G.transitionPub M)
    (fresh : G.addr.val < (G.transitionPub 1).val ∨ (G.transitionPub 1).val+fieldWords M ≤ G.addr.val)
    (sep : (G.transitionPub 1).val+fieldWords M ≤ (G.transitionPub 2).val ∨
      (G.transitionPub 2).val+fieldWords M ≤ (G.transitionPub 1).val) (c : Code G.evaluator.extra M) :
    ConfigAt (gatherMemory G true F m bits) (G.transitionPub 1) c ↔ ConfigAt m (G.transitionPub 1) c := by
  have fit := hl.oldFit
  rw [← fieldWords_eq_calls] at fit
  have hbase : EvaluatorGather.operands G true 1 = G.transitionPub 2 := rfl
  unfold gatherMemory retag
  rw [configAt_write_iff G _ F.width hl.states fit fresh c]
  refine (configAt_gathered_disjoint_iff _ hl.oldFit F.dest ?_ bits c).trans
    (configAt_write_iff G _ F.width hl.states fit fresh c)
  simpa only [← fieldWords_eq_calls, hbase] using sep

/-- The final endpoint's router and state writer preserve the incoming image. -/
theorem put_frame (m : Memory G.w) (hl : PrepLayout G.evaluator G.transitionPub M)
    (fresh : G.addr.val < (G.transitionPub 1).val ∨ (G.transitionPub 1).val+fieldWords M ≤ G.addr.val)
    (sep : (G.transitionPub 2).val < (G.transitionPub 1).val ∨
      (G.transitionPub 1).val+fieldWords M ≤ (G.transitionPub 2).val) (c : Code G.evaluator.extra M) :
    ConfigAt (putMemory G true m) (G.transitionPub 1) c ↔ ConfigAt m (G.transitionPub 1) c := by
  have fit := hl.oldFit
  rw [← fieldWords_eq_calls] at fit
  unfold putMemory EvaluatorSentinel.transferred EvaluatorSentinel.put retag
  rw [show EvaluatorSentinel.operands G true 1 = G.transitionPub 2 from rfl, configAt_write_iff G _ hl.width hl.states fit fresh c, configAt_write_iff G _ hl.width hl.states fit sep c,
    configAt_write_iff G _ hl.width hl.states fit fresh c]

/-- On a blank outgoing bank the final route imposes exactly the accepting halt. -/
theorem put_image (m : Memory G.w) (hl : PrepLayout G.evaluator G.transitionPub M)
    (zero : ∀ i : Fin (fieldWords M), m ((G.transitionPub 2).val+i.val) = 0)
    (fresh : G.addr.val < (G.transitionPub 2).val ∨ (G.transitionPub 2).val+fieldWords M ≤ G.addr.val)
    (z : Code G.evaluator.extra M) : ConfigAt (putMemory G true m) (G.transitionPub 2) z ↔ z = .accepted := by
  have fit := hl.outFit
  rw [← fieldWords_eq_calls] at fit
  apply configAt_eq_iff G hl.width hl.states _ z
  apply configAt_of_words hl.width hl.states .accepted
  intro i
  rw [offset G _ i fit]
  apply EvaluatorSentinel.final_image G hl.width hl.states _ _ fresh i
  intro j
  have he : (G.transitionPub 2).val+j.val ≠ G.addr.val := by have := j.isLt; omega
  rw [show EvaluatorSentinel.operands G true 1 = G.transitionPub 2 from rfl, retag, writeMemory, ite_eq_right he, zero]

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
