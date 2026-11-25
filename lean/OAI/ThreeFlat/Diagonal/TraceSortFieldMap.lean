import OAI.ThreeFlat.Diagonal.TraceSortStages
import OAI.Computability.VPVNP.RAMMemoryMessages

namespace OAI
/-! # Identifying the gate program's physical send addresses with the replay model -/

namespace ThreeFlat.Diagonal.TraceSortSite

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSort
open TraceSlots

variable {w d : ℕ} {α : Type*}

abbrev schedule (d : ℕ) := phases (1+d) (1+d) le_rfl

def fromPhysical (x : Computability.VPVNP.RAMLayout.Layer d → Fin (2^d) → Fin 2 → α)
    (s : Stage (1+d)) (h : 1 ≤ s.stride) : Fin (2^d) → Fin 2 → α :=
  x ((crossStageEquiv 1 d).symm ⟨s,h⟩)

def bundle (send : ∀ s : Stage (1+d), Sends 1 d s α) :
    (ss : List (Stage (1+d))) → Fields 1 d α ss
  | [] => PUnit.unit
  | s :: ss => (send s, bundle send ss)

private theorem bundle_eq (send : ∀ s : Stage (1+d), Sends 1 d s α)
    (ss : List (Stage (1+d))) (hn : ss.Nodup) :
    fieldsOfStages ss hn (fun s _ => send s) = bundle send ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => exact Prod.ext rfl (ih (List.nodup_cons.mp hn).2)

theorem physical_bundle (x : Computability.VPVNP.RAMLayout.Layer d → Fin (2^d) → Fin 2 → α) :
    physicalFieldsEquiv 1 d α x = bundle (fromPhysical x) (schedule d) :=
  bundle_eq _ _ (phases_nodup le_rfl)

def widened (send : StageData w d) (s : Stage (1+d)) (h : 1 ≤ s.stride)
    (v : Fin (2^d)) (i : Fin 2) := toOrdered (send s h v i)

theorem states_replay (send : StageData w d) (v : Fin (2^d)) (ss : List (Stage (1+d)))
    (cur : Fin 2 → Narrow w) :
    toOrdered ∘ states send v ss cur = replay v ss (bundle (widened send) ss) (toOrdered ∘ cur) := by
  induction ss generalizing cur with
  | nil => rfl
  | cons s ss ih =>
    change toOrdered ∘ states send v ss (next s v (send s) cur) = _
    rw [ih, next_ordered]
    rfl

theorem toOrdered_injective : Function.Injective (toOrdered (w := w)) := by
  intro a b h
  have e := congrArg OrderedSlot.record h
  cases a <;> cases b <;> simp_all [toOrdered, WordRecord.record_injective.eq_iff]

theorem outgoingChecks_iff (send : StageData w d) (v : Fin (2^d)) (ss : List (Stage (1+d)))
    (cur : Fin 2 → Narrow w) :
    outgoingChecks send v ss cur ↔ checks v ss (bundle (widened send) ss) (toOrdered ∘ cur) := by
  induction ss generalizing cur with
  | nil => rfl
  | cons s ss ih =>
    simp only [outgoingChecks, bundle, checks, ih]
    have hs : toOrdered ∘ next s v (send s) cur = localLayer s (widened send s) v (toOrdered ∘ cur) := next_ordered s v (send s) cur
    rw [hs]
    apply and_congr_left
    intro _
    constructor
    · intro h k
      funext i
      exact congrArg toOrdered (congrFun (h k) i)
    · intro h k
      funext i
      exact toOrdered_injective (congrFun (h k) i)

end ThreeFlat.Diagonal.TraceSortSite

end OAI
