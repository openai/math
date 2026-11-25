import OAI.Computability.BorderVNP.PackedDirectoryRoom
import OAI.Computability.BorderVNP.PackedDirectoryBudget
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Native execution and uniqueness of the populated delivery table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- For a sufficiently large word and disjoint placement tables, the actual signed native
machine accepts the directory construction uniquely. It publishes the required ordered
intervals, makes no guesses, and adds only positive signs. The tick cost is at most a
constant per team/site in the sparse grid. -/
theorem native_directory {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (B : ℕ) :
    let d := frameLayout (readings pub) (readings m)
    let f := frameField (readings pub) (readings m)
    let pp := placement (readings m) (f 64)
    let lp := placement (readings m) (f 65)
    let rows := d.directory pp lp
    0 < d.teams → 0 < d.processors → 0 < d.block → 0 < d.literal/2 →
    d.fields ≤ 2 → d.processors*d.literal ≤ d.sites*d.block → d.processors ≤ d.sites →
    d.entries ≤ d.teams*d.sites → Sizes d (f 64) (f 65) pp lp B →
    wordBound B < 2^w → (pub 0).val+70 < f 8 → f 8+7*d.candidates ≤ f 64 →
    f 8+7*d.candidates ≤ f 65 →
    ∃ es t, Runs pub macros program s m es t (publish m (pub 0).val (f 8) rows) ∧
      traceCost es ≤ setup.slots + (candidate.slots+19)*(8*(d.teams*d.sites)) + 8 ∧
      (∀ e ∈ es, e.choices = [] ∧ e.sign = .plus) ∧
      (∀ bits fs, TeamRAM.execute (program.program.fetch pub macros) ⟨0,s⟩ m bits = some fs ↔
        fs = es ∧ bits = es.map TeamRAM.Event.choices) := by
  intro d f pp lp rows ht hr hb htail hfields capacity sites entries sz wordRoom before privateRoom liveRoom
  have small : B ≤ wordBound B := by
    unfold wordBound
    nlinarith [Nat.zero_le (B^4),Nat.zero_le (B^3),Nat.zero_le (B^2)]
  have bound : d.stride < 2^w := sz.stride.trans_lt (small.trans_lt wordRoom)
  have room : f 8 + 7*d.candidates < 2^w :=
    privateRoom.trans_lt (sz.bases.1.trans_lt (small.trans_lt wordRoom))
  obtain ⟨es,t,run,ct⟩ := program_runs pub macros s m ht hr hb before bound room privateRoom liveRoom
    (candidates_fit sz htail hb wordRoom)
  have cost := d.candidates_le hb hfields capacity sites entries
  refine ⟨es,t,run,?_,run.unsigned_events (by decide),fun bits fs => ?_⟩
  · exact ct.trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ cost) _) _)
  · rw [Code.execute_iff_runs (by decide : program.withoutAccept = true)]
    constructor
    · rintro ⟨⟨u,mu,r⟩,hbits⟩
      obtain ⟨rfl,_,_⟩ := r.unique_of_deterministic deterministic run
      exact ⟨rfl,hbits.symm⟩
    · rintro ⟨rfl,rfl⟩
      exact ⟨⟨t,_,run⟩,rfl⟩

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
