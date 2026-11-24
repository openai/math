import OAI.Computability.VPVNP.LiveStageLinkPaths
import OAI.Computability.VPVNP.PrimedScheduleRAM

/-!
# A complete accepting stage inside the native linker

The segment before the accepting report keeps its stage tag and ordinary
persistent state. The accepting report transfers control, preserving all
source writes except for the linker's update to its own reserved word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveStageLink

open BurstRAM BurstRAM.PrivateRAM

variable {d r k w : ℕ} {pcs : Fin d → ℕ}

/-- Each source report preserves the linker's reserved tag address. -/
def PreservesTag (addr : Word w) (rs : List (Report w)) : Prop :=
  ∀ rep ∈ rs, ∀ mem, after mem rep.events addr.val = mem addr.val

/-- At each continuing report, the next dispatch sees the same tag. The
accepting report may write the tag because it immediately halts or transfers. -/
def PreservesTagOnReturns (addr : Word w) : Memory w → List (Report w) → Prop
  | _, [] => True
  | m, rep :: rs =>
    (rep.result.isSome → after m rep.events addr.val = m addr.val) ∧
      PreservesTagOnReturns addr (after m rep.events) rs

theorem PreservesTag.onReturns {addr : Word w} {rs : List (Report w)} (h : PreservesTag addr rs) (m : Memory w) :
    PreservesTagOnReturns addr m rs := by
  induction rs generalizing m with
  | nil => trivial
  | cons r rs ih =>
    exact ⟨fun _ => h r (by simp) m, ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) _⟩

theorem PreservesTagOnReturns.singleton_accept (addr : Word w) (m : Memory w) (r : Report w)
    (h : r.result = none) : PreservesTagOnReturns addr m [r] := by simp [PreservesTagOnReturns,h]

theorem PreservesTagOnReturns.append {addr : Word w} {m : Memory w} {xs ys : List (Report w)}
    (hx : PreservesTagOnReturns addr m xs) (hy : PreservesTagOnReturns addr (after m (eventLog xs)) ys) :
    PreservesTagOnReturns addr m (xs ++ ys) := by
  induction xs generalizing m with
  | nil => exact hy
  | cons x xs ih =>
    have ht : after m (eventLog (x::xs)) = after (after m x.events) (eventLog xs) := by simp [after,eventLog,List.foldl_append]
    rw [ht] at hy
    exact ⟨hx.1, ih hx.2 hy⟩

/-- Memory passed across an accepting boundary. -/
def transferMemory (addr : Word w) (dest : Option (Fin d)) (m : Memory w) :=
  match dest with
  | some t => writeMemory m addr (tagWord w t)
  | none => m

theorem transferMemory_tag (addr : Word w) (s : Fin d) (m : Memory w) :
    transferMemory addr (some s) m addr.val = tagWord w s := by simp [transferMemory, writeMemory]

theorem linkedReport_result (next : Fin d → Option (Fin d)) (addr : Word w) (s : Fin d) (rep : Report w) :
    (linkedReport next addr s rep).result = match rep.result with
      | some v => some v | none => (next s).map (fun _ => 0) := by
  cases rep with
  | mk es out => cases out <;> cases hn : next s <;> simp [linkedReport, prependLog, exitReport, hn]

private theorem after_eventLog_cons (m : Memory w) (r : Report w) (rs : List (Report w)) :
    after m (eventLog (r :: rs)) = after (after m r.events) (eventLog rs) := by simp [eventLog,after,List.foldl_append]

variable (T : (s : Fin d) → Template (pcs s) r k) (next : Fin d → Option (Fin d))
variable (pub : Fin k → Word w) (addr : Word w)

/-- Complete native simulation of one accepting component, including every
returned cursor, external word effect and the precise cumulative probe cost. -/
theorem runSegment_accepting {fuel cap : ℕ} (s : Fin d) (hfits : d ≤ 2^w) (hcap : fuel+2*d+5 ≤ cap)
    (st : Word w) (m : Memory w) (bs : List (List Bool)) (rs : List (Report w))
    (htag : m addr.val = tagWord w s) (hframe : PreservesTagOnReturns addr m rs)
    (hsrc : runSegment ((T s).instantiate w pub).program fuel (some st) m bs = some rs)
    (hend : endState (some st) rs = none) :
    let outs := rs.map (linkedReport next addr s)
    runSegment (machine T next pub addr).program cap (some st) m bs = some outs ∧
    endState (some st) outs = (next s).map (fun _ => 0) ∧
    after m (eventLog outs) = transferMemory addr (next s) (after m (eventLog rs)) ∧
    RAMBuckets.cost Report.probes outs =
      RAMBuckets.cost Report.probes rs + rs.length + (if (next s).isSome then 1 else 0) := by
  induction bs generalizing st m rs with
  | nil =>
    simp only [runSegment, Option.some.injEq] at hsrc
    subst rs
    contradiction
  | cons bits bs ih =>
    dsimp only
    simp only [runSegment] at hsrc
    cases he : execute ((T s).instantiate w pub).program fuel (((T s).instantiate w pub).program.start st) m bits with
    | none => simp [he] at hsrc
    | some rep =>
      simp only [he, Option.map_eq_some_iff] at hsrc
      obtain ⟨rest, hr, rfl⟩ := hsrc
      have hex := execute_linked_of_stage T next pub addr s hfits hcap st m htag bits rep he
      have ho := linkedReport_after next addr s rep m
      have hv := linkedReport_result next addr s rep
      have hp := linkedReport_probes next addr s rep
      cases hout : rep.result with
      | none =>
        rw [hout] at hr
        cases bs with
        | cons _ _ => simp [runSegment] at hr
        | nil =>
          simp [runSegment] at hr
          subst rest
          cases hn : next s <;>
            simp_all [runSegment, List.map_cons, endState, eventLog, RAMBuckets.cost, transferMemory] <;> omega
      | some st' =>
        have htail := hframe.2
        have ht : after m rep.events addr.val = tagWord w s := (hframe.1 (by simp [hout])).trans htag
        rw [hout] at hr
        change endState rep.result rest = none at hend
        rw [hout] at hend
        obtain ⟨hrun, hstate, hmem, hcost⟩ := ih st' (after m rep.events) rest ht htail hr hend
        simp only [hout] at hv ho
        simp [hout] at hp
        simp only [List.map_cons, runSegment, hex, hv, ho, hrun, Option.map_some,
          endState, hstate, after_eventLog_cons, hmem, RAMBuckets.cost, hp, List.length_cons, hcost, true_and]
        omega

end LiveStageLink

end VPVNP
end Computability
end OAI
