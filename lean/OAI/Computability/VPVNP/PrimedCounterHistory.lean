import OAI.Computability.VPVNP.PrimedCounterData
import OAI.Computability.VPVNP.PrimedCounterFoldOrder
import OAI.Computability.VPVNP.PrimedScheduleRAM

/-!
# Lifting a per-call memory invariant through a native RAM history

Consecutive post-assembly items occupy consecutive absolute cursor values.
A successful item transfers the real external memory (including its reads
and writes) to the next item. Matching rejection and success at each step
therefore gives matching rejection and success for the whole scheduled fold.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.History

open BurstRAM PrimedSchedule

variable {U w : ℕ} {I State C : Type*}

/-- Each item in the list has absolute cursor equal to its list index plus the starting offset. -/
def Ordered (pos : I → Fin U) (k : ℕ) (xs : List I) : Prop :=
  ∀ j : Fin xs.length, (pos (xs.get j)).val = k + j.val

private theorem Ordered.head {pos : I → Fin U} {k : ℕ} {i : I} {xs : List I}
    (h : Ordered pos k (i::xs)) : (pos i).val = k := by simpa using h 0

private theorem Ordered.tail {pos : I → Fin U} {k : ℕ} {i : I} {xs : List I}
    (h : Ordered pos k (i::xs)) : Ordered pos (k+1) xs := by
  intro j
  simpa [Nat.add_assoc, Nat.add_comm 1 j.val] using h j.succ

/-- Identify all cursor values after a fixed list of preceding calls. -/
theorem ordered_after {pos : I → Fin U} (front : List (Fin U)) (xs : List I)
    (he : front ++ xs.map pos = List.finRange U) : Ordered pos front.length xs := by
  intro j
  have hlen := congrArg List.length he
  simp only [List.length_append, List.length_map, List.length_finRange] at hlen
  have hpos : front.length + j.val < U := (Nat.add_lt_add_left j.isLt front.length).trans_eq hlen
  have hx := congrArg (fun l : List (Fin U) => l[front.length+j.val]?) he
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by simp), List.getElem?_eq_getElem (by simpa using hpos)] at hx
  simpa using congrArg Fin.val (Option.some.inj hx)

/-- Simultaneous rejection, or two successful computations related by their
results. -/
inductive Match {α β : Type*} (rel : α → β → Prop) : Option α → Option β → Prop
  | reject : Match rel none none
  | accept {a b} (h : rel a b) : Match rel (some a) (some b)

theorem Match.some_iff {α β : Type*} {a : α} {b : β} {rel : α → β → Prop} :
    Match rel (some a) (some b) ↔ rel a b := by
  constructor
  · intro h
    cases h with
    | accept h => exact h
  · exact Match.accept

/-- A single-call proof supplies both directions of execution, the next
persistent control, the per-call probe bound, and the invariant on real
post-memory. -/
abbrev Step (P : BurstRAM.Program w C) (fuel bound : ℕ) (pos : I → Fin U) (bits : I → List Bool)
    (logical : State → I → Option State) (inv : ℕ → State → Memory w → Prop) :=
  ∀ (i : I) (s : State) (m : Memory w), inv (pos i).val s m →
    Match (fun s' (r : Report w) => r.result = control w U ((pos i).val+1) ∧
        r.probes ≤ bound ∧ inv ((pos i).val+1) s' (after m r.events))
      (logical s i) (execute P fuel (P.start (cursor w (pos i).val)) m (bits i))

/-- Match the entire parser fold with the genuine successive-call interpreter,
including exact cursor, memory, report length and individual probe bounds. -/
theorem fold_run (P : BurstRAM.Program w C) (fuel bound : ℕ) (pos : I → Fin U) (bits : I → List Bool)
    (logical : State → I → Option State) (inv : ℕ → State → Memory w → Prop)
    (one : Step P fuel bound pos bits logical inv) (xs : List I) (k : ℕ)
    (ho : Ordered pos k xs) (s : State) (m : Memory w) (hi : inv k s m) :
    Match (fun s' (rs : List (Report w)) => rs.length = xs.length ∧
        endState (control w U k) rs = control w U (k+xs.length) ∧
        inv (k+xs.length) s' (after m (eventLog rs)) ∧ ∀ r ∈ rs, r.probes ≤ bound)
      (xs.foldlM logical s) (runSegment P fuel (control w U k) m (xs.map bits)) := by
  induction xs generalizing k s m with
  | nil => exact Match.accept ⟨rfl, rfl, hi, fun _ hr => by simp at hr⟩
  | cons i xs ih =>
    have hk := ho.head
    have hlt : k < U := hk ▸ (pos i).isLt
    have hctrl : PrimedSchedule.control w U k = some (cursor w k) := by simp [PrimedSchedule.control, hlt]
    have he := one i s m (hk ▸ hi)
    cases hl : logical s i with
    | none =>
      rw [hl, hk] at he
      cases hv : execute P fuel (P.start (cursor w k)) m (bits i) with
      | none => simp [hctrl, runSegment, hv, hl, Match.reject]
      | some r => rw [hv] at he; cases he
    | some next =>
      rw [hl, hk] at he
      cases hv : execute P fuel (P.start (cursor w k)) m (bits i) with
      | none => rw [hv] at he; cases he
      | some r =>
        rw [hv] at he
        obtain ⟨hr, hb, hm⟩ := Match.some_iff.mp he
        have htail := ih (k+1) ho.tail next (after m r.events) hm
        cases hlf : xs.foldlM logical next with
        | none =>
          rw [hlf] at htail
          cases hrf : runSegment P fuel (control w U (k+1)) (after m r.events) (xs.map bits) with
          | none => simp [hl, hlf, runSegment, hctrl, hv, hr, hrf, Match.reject]
          | some => rw [hrf] at htail; cases htail
        | some last =>
          rw [hlf] at htail
          cases hrf : runSegment P fuel (control w U (k+1)) (after m r.events) (xs.map bits) with
          | none => rw [hrf] at htail; cases htail
          | some rs =>
            rw [hrf] at htail
            obtain ⟨hlen,hend,hinv,hbounds⟩ := Match.some_iff.mp htail
            simp only [List.foldlM_cons, hl, bind, Option.bind_some, hlf, List.map_cons, runSegment,
              hctrl, hv, hr, hrf, Option.map_some]
            apply Match.accept
            have heq : k+(i::xs).length = k+1+xs.length := by simp; omega
            refine ⟨by simp [hlen], ?_, ?_, ?_⟩
            · simpa only [endState, hr, heq] using hend
            · rw [heq]
              simpa only [eventLog, List.flatMap_cons, after, List.foldl_append] using hinv
            · intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact hb
              · exact hbounds _ ha

/-- Convert individual probe bounds and exact report length into the global
and per-call transcript caps. -/
theorem within {rs : List (Report w)} {S H bound : ℕ}
    (hp : ∀ r ∈ rs, r.probes ≤ bound) (hh : 1+bound ≤ H) (ht : (1+bound)*rs.length ≤ S*H) :
    withinCaps S H rs := by
  have hsum (ls : List (Report w)) (hs : ∀ r ∈ ls, r.probes ≤ bound) :
      RAMBuckets.cost Report.probes ls ≤ (1+bound)*ls.length := by
    induction ls with
    | nil => simp [RAMBuckets.cost]
    | cons a l ih =>
      have h₁ := hs a (List.mem_cons_self ..)
      have h₂ := ih (fun r hr => hs r (List.mem_cons_of_mem _ hr))
      rw [RAMBuckets.cost, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
  exact ⟨(hsum rs hp).trans ht, fun r hr => (Nat.add_le_add_left (hp r hr) 1).trans hh⟩

end PrimedCounter.History

end VPVNP
end Computability
end OAI
