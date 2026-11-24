import OAI.Computability.VPVNP.LiveExponentRows
import OAI.Computability.VPVNP.RAMSuccessor
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Native path multiplicity and resource bounds of exponent addition

For any initialized buffers the exponent stage accepts either once or zero
times. A successful run has one data call for every physical cut digit, one
accepting end call, and no binary choices. The count covers all finite native
call streams, including streams of unintended lengths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveExponent

open BurstRAM
open scoped Classical

variable {w t Z : ℕ}

private theorem halted_stream (pub : Fin 5 → Word w) (f : ℕ) (bs : List (List Bool))
    (s : Word w) (m : Memory w) (rs : List (Report w)) (hs : s ≤ pub 4)
    (hr : runSegment (digitTemplate.instantiate w pub).program (f+31) (some s) m bs = some rs)
    (he : endState (some s) rs = none) : bs = List.replicate ((pub 4).val + 1 - s.val) [] := by
  induction bs generalizing s m rs with
  | nil =>
    change some [] = some rs at hr
    cases hr
    contradiction
  | cons b bs ih =>
    rw [runSegment] at hr
    cases h : execute (digitTemplate.instantiate w pub).program (f+31)
        ((digitTemplate.instantiate w pub).program.start s) m b with
    | none => simp [h] at hr
    | some r =>
      rw [h, Option.map_eq_some_iff] at hr
      obtain ⟨rest, htail, rfl⟩ := hr
      change endState r.result rest = none at he
      rcases lt_or_eq_of_le hs with hlt | rfl
      · obtain ⟨rfl,rfl⟩ := data_result hlt h
        have hsp : (s+1).val = s.val+1 := Fin.val_add_one_of_lt' (by
          have := (pub 4).isLt
          change s.val < (pub 4).val at hlt
          omega)
        change runSegment _ _ (some (s+1)) _ _ = _ at htail
        change endState (some (s+1)) rest = none at he
        have hle : s+1 ≤ pub 4 := by
          change (s+1).val ≤ (pub 4).val
          rw [hsp]
          exact hlt
        change s.val < (pub 4).val at hlt
        rw [ih (s+1) _ rest hle htail he, hsp,
          show (pub 4).val + 1 - s.val = ((pub 4).val + 1 - (s.val+1))+1 by omega,
          List.replicate_succ]
      · rw [show f+31 = (f+26)+5 by omega, execute_done pub (pub 4) m b (f+26) rfl] at h
        by_cases hb : b = []
        · simp only [hb, ite_true, Option.some.injEq] at h
          subst r
          cases bs with
          | nil => simp [hb]
          | cons c bs => contradiction
        · simp [hb] at h

/-- All successful digit reports followed by the accepting call. -/
def stageReports (pub : Fin 5 → Word w) (t Z : ℕ) (m : Memory w) : List (Report w) :=
  rowsReports pub Z (List.finRange t) m ++ [⟨[.tick,.tick,.tick,.tick],none⟩]

private theorem flatten_empty (rows : List (Fin t)) :
    rows.flatMap (fun _ => List.replicate Z ([] : List Bool)) = List.replicate (rows.length*Z) [] := by
  induction rows with
  | nil => simp
  | cons a rows ih =>
    rw [List.flatMap_cons, ih, List.replicate_append_replicate, List.length_cons, Nat.succ_mul, Nat.add_comm]

private theorem canonical_stage {pub : Fin 5 → Word w} (L : BufferLayout pub t Z) (hZ : 0 < Z) (hw : 2 ≤ w)
    {x y : Fin t → Word Z} {m : Memory w} (v : BufferValues pub x y m)
    (inc : Fin t → Word w) (hi : ∀ a, m (counterAddr pub a).val = inc a)
    (hc : ∀ a, (inc a).val+1 < 2^w) (f : ℕ) :
    runSegment (digitTemplate.instantiate w pub).program (f+31) (some 0) m
      (List.replicate (t*Z+1) []) =
      if ∀ a, (y a).val = (x a).val+(inc a).val then some (stageReports pub t Z m) else none := by
  have he := run_stage L hZ hw v inc hi hc (fun _ => List.replicate Z []) (by simp) [] f
  rw [flatten_empty, List.length_finRange] at he
  simpa [stageReports, List.replicate_add] using he

/-- The cardinality of native accepting paths for any report cap. -/
theorem pathCount {pub : Fin 5 → Word w} (L : BufferLayout pub t Z) (hZ : 0 < Z) (hw : 2 ≤ w)
    {x y : Fin t → Word Z} {m : Memory w} (v : BufferValues pub x y m)
    (inc : Fin t → Word w) (hi : ∀ a, m (counterAddr pub a).val = inc a)
    (hc : ∀ a, (inc a).val+1 < 2^w) (f : ℕ) (cap : List (Report w) → Prop) :
    Nat.card (ActualPaths (digitTemplate.instantiate w pub).program (f+31) 0 m cap) =
      if (∀ a, (y a).val = (x a).val+(inc a).val) ∧ cap (stageReports pub t Z m) then 1 else 0 := by
  let paths := ActualPaths (digitTemplate.instantiate w pub).program (f+31) 0 m cap
  have uniq (a : paths) : a.val = List.replicate (t*Z+1) [] := by
    obtain ⟨rs, hr, he, _⟩ := a.property
    simpa [L.size] using halted_stream pub f a.val 0 m rs (Fin.zero_le _) hr he
  have run := canonical_stage L hZ hw v inc hi hc f
  by_cases hgood : (∀ a, (y a).val = (x a).val+(inc a).val) ∧ cap (stageReports pub t Z m)
  · rw [ite_eq_left hgood]
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨⟨fun a b => Subtype.ext ((uniq a).trans (uniq b).symm)⟩, ⟨⟨List.replicate (t*Z+1) [],stageReports pub t Z m,?_,?_,hgood.2⟩⟩⟩
    · exact run.trans (ite_eq_left hgood.1)
    · rw [stageReports, endState_append]
      rfl
  · rw [ite_eq_right hgood]
    have : IsEmpty paths := ⟨fun a => by
      obtain ⟨rs, hr, _, hp⟩ := a.property
      rw [uniq a, run] at hr
      split at hr
      · rename_i he
        exact hgood ⟨he, Option.some.inj hr ▸ hp⟩
      · contradiction⟩
    exact Nat.card_of_isEmpty

private theorem rowResources (pub : Fin 5 → Word w) (n p : ℕ) (m : Memory w) :
    RAMBuckets.cost Report.probes (rowReports pub n p m) = 5*n ∧
    (rowReports pub n p m).length = n ∧
    ∀ r ∈ rowReports pub n p m, r.probes = 4 ∧ r.events.length = 30 := by
  induction n generalizing p m with
  | zero => simp [rowReports, RAMBuckets.cost]
  | succ n ih =>
    let r := digitReport pub (atPos p) m
    have h := ih (p+1) (after m r.events)
    change 1+r.probes+_ = _ ∧ (_:: _).length = _ ∧ ∀ a ∈ r :: _, _
    rw [(digitReport_cost pub (atPos p) m).1, h.1, List.length_cons, h.2.1, List.forall_mem_cons]
    exact ⟨by omega, rfl, ⟨(digitReport_cost ..).1, (digitReport_cost ..).2.1⟩, h.2.2⟩

private theorem rowsResources (pub : Fin 5 → Word w) (rows : List (Fin t)) (m : Memory w) :
    RAMBuckets.cost Report.probes (rowsReports pub Z rows m) = 5*(rows.length*Z) ∧
    (rowsReports pub Z rows m).length = rows.length*Z ∧
    ∀ r ∈ rowsReports pub Z rows m, r.probes = 4 ∧ r.events.length = 30 := by
  induction rows generalizing m with
  | nil => simp [rowsReports, RAMBuckets.cost]
  | cons a rows ih =>
    have h := rowResources pub Z (a.val*Z) m
    have h' := ih (writeMemory m (counterAddr pub a) 0)
    simp only [rowsReports, RAMBuckets.cost_append, h.1, h'.1, List.length_append, h.2.1, h'.2.1,
      List.length_cons, Nat.succ_mul, List.forall_mem_append]
    exact ⟨by ring, by omega, h.2.2, h'.2.2⟩

/-- Total native cost, call count and per-call clock/probe bound. -/
theorem stageResources (pub : Fin 5 → Word w) (t Z : ℕ) (m : Memory w) :
    RAMBuckets.cost Report.probes (stageReports pub t Z m) = 5*(t*Z)+1 ∧
    (stageReports pub t Z m).length = t*Z+1 ∧
    ∀ r ∈ stageReports pub t Z m, r.probes ≤ 4 ∧ r.events.length ≤ 30 := by
  have h := rowsResources (Z := Z) pub (List.finRange t) m
  simp only [List.length_finRange] at h
  simp only [stageReports, RAMBuckets.cost_append, h.1, List.length_append, h.2.1,
    List.forall_mem_append, List.forall_mem_singleton]
  exact ⟨rfl,rfl,fun r hr => ⟨(h.2.2 r hr).1.le,(h.2.2 r hr).2.le⟩,show 0 ≤ 4 ∧ 4 ≤ 30 from by decide⟩

theorem stageCaps (pub : Fin 5 → Word w) (m : Memory w) {S H : ℕ}
    (hcost : 5*(t*Z)+1 ≤ S*H) (hb : 5 ≤ H) : withinCaps S H (stageReports pub t Z m) :=
  ⟨(stageResources ..).1 ▸ hcost, fun r hr => by have := (stageResources pub t Z m).2.2 r hr; omega⟩

end LiveExponent

end VPVNP
end Computability
end OAI
