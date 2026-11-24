import OAI.Computability.VPVNP.CompressorRecordsOrdinalRun
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# External addresses of complete ordinal scans

Read and write bounds verified on individual source calls are preserved
when the calls run consecutively. The resulting bounds allow the online
dispatcher to replay a pass after changing its own control words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.OrdinalRun

open BurstRAM SourceTransport

variable {w : ℕ} {Q : Type*}

/-- A native scan reads and writes only the union of its rows' data cells. -/
theorem footprint (P : BurstRAM.Program w Q) (fuel : ℕ) (cursor : ℕ → Word w)
    (N : ℕ) (I : ℕ → Memory w → Prop) (readable writable : ℕ → Prop)
    (advance : ∀ j < N, ∀ m, I j m → ∀ bits rep, execute P fuel (P.start (cursor j)) m bits = some rep →
      rep.result = some (cursor (j+1)) ∧ I (j+1) (after m rep.events) ∧
        Reads readable rep.events ∧ Writes writable rep.events)
    (j : ℕ) (bs : List (List Bool)) (m : Memory w) (rs : List (Report w))
    (size : j+bs.length ≤ N) (inv : I j m) (run : runSegment P fuel (some (cursor j)) m bs = some rs) :
    Reads readable (eventLog rs) ∧ Writes writable (eventLog rs) := by
  induction bs generalizing j m rs with
  | nil =>
    change some [] = some rs at run
    cases Option.some.inj run
    exact ⟨fun _ _ h => (List.not_mem_nil h).elim,fun _ _ h => (List.not_mem_nil h).elim⟩
  | cons b bs ih =>
    cases h : execute P fuel (P.start (cursor j)) m b with
    | none => simp [runSegment,h] at run
    | some rep =>
      have hj : j<N := by rw [List.length_cons] at size; omega
      obtain ⟨inc,next,rd,wr⟩ := advance j hj m inv b rep h
      simp only [runSegment,h,inc,Option.map_eq_some_iff] at run
      obtain ⟨tail,rt,rfl⟩ := run
      obtain ⟨tr,tw⟩ := ih (j+1) _ tail (by rw [List.length_cons] at size; omega) next rt
      refine ⟨fun a v he => ?_,fun a v he => ?_⟩
      · exact (List.mem_append.mp he).elim (rd a v) (tr a v)
      · exact (List.mem_append.mp he).elim (wr a v) (tw a v)

/-- The report list records every successor cursor in visit order. -/
theorem successors (P : BurstRAM.Program w Q) (fuel : ℕ) (cursor : ℕ → Word w) (N : ℕ)
    (advance : ∀ j < N, ∀ m bits rep, execute P fuel (P.start (cursor j)) m bits = some rep →
      rep.result = some (cursor (j+1)))
    (j : ℕ) (bs : List (List Bool)) (m : Memory w) (rs : List (Report w))
    (size : j+bs.length ≤ N) (run : runSegment P fuel (some (cursor j)) m bs = some rs) :
    rs.map Report.result = (List.range' (j+1) bs.length).map (fun l => some (cursor l)) := by
  induction bs generalizing j m rs with
  | nil => change some [] = some rs at run; cases Option.some.inj run; rfl
  | cons b bs ih =>
    cases h : execute P fuel (P.start (cursor j)) m b with
    | none => simp [runSegment,h] at run
    | some rep =>
      have hj : j<N := by rw [List.length_cons] at size; omega
      have inc := advance j hj m b rep h
      simp only [runSegment,h,inc,Option.map_eq_some_iff] at run
      obtain ⟨tail,rt,rfl⟩ := run
      have last := ih (j+1) _ tail (by rw [List.length_cons] at size; omega) rt
      simp only [List.map_cons,List.length_cons,List.range'_succ,inc,last]

end CompressorRecords.OrdinalRun

end VPVNP
end Computability
end OAI
