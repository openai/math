import OAI.Computability.VPVNP.CompressorOnlineWorkerSegment

/-! # The directory frame of a complete ordinal worker stream

Use the same single-call ready and memory invariants as the reverse row
decomposition. The private source fuel is extended to the outer cap
before applying that invariant. The ordinal and number of remaining
bursts determine which dispatcher guard applies.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Schedule.Online

open BurstRAM

variable {d w : ℕ} {C : Catalog d} {i : Fin d} {ports : Ports w}
  {pub : Fin (C i).params → Word w} {stop : Word w} {fuel cap N : ℕ}
  {inv : Word w → Memory w → Prop}
private abbrev source (C : Catalog d) (i : Fin d) (pub : Fin (C i).params → Word w) :=
  ((C i).table.instantiate w pub).program

local notation "P" => source C i pub

theorem ordinalFrame (step : WorkerStep ports i pub stop cap fuel inv) (hfuel : fuel ≤ cap)
    (cursor : ℕ → Word w) (active : ∀ j<N, cursor j < stop) (closed : stop ≤ cursor N)
    (progress : ∀ j<N, ∀ (mem : Memory w) (b : List Bool) (r : Report w),
      execute P fuel ((P).start (cursor j)) mem b = some r → r.result = some (cursor (j+1)))
    (j : ℕ) (bits : List (List Bool)) (m : Memory w) (rs : List (Report w))
    (hlen : j+bits.length=N) (ready : Ready C i ports pub stop m) (hi : inv (cursor j) m)
    (run : runSegment P fuel (some (cursor j)) m bits = some rs) :
    ValidTrace C i ports pub stop (cursor j) m rs := by
  induction bits generalizing j m rs with
  | nil =>
    change some [] = some rs at run
    cases Option.some.inj run
    have he : j=N := by simpa only [List.length_nil,Nat.add_zero] using hlen
    exact ⟨ready,he ▸ closed⟩
  | cons b bs ih =>
    have hj : j<N := by rw [List.length_cons] at hlen; omega
    cases h : execute P fuel ((P).start (cursor j)) m b with
    | none => simp [runSegment,h] at run
    | some r =>
      have inc := progress j hj m b r h
      have extended := execute_extend h (cap-fuel)
      rw [Nat.add_sub_of_le hfuel] at extended
      obtain ⟨_,k,ret,ready',hi'⟩ := step (cursor j) m b r ready hi (active j hj) extended
      obtain rfl : k = cursor (j+1) := Option.some.inj (ret.symm.trans inc)
      simp only [runSegment,h,inc,Option.map_eq_some_iff] at run
      obtain ⟨rest,tail,rfl⟩ := run
      exact ⟨ready,active j hj,_,inc,ih (j+1) _ rest (by rw [List.length_cons] at hlen; omega) ready' hi' tail⟩

end CompressorRecords.Schedule.Online

end VPVNP
end Computability
end OAI
