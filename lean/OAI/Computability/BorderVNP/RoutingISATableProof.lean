import OAI.Computability.BorderVNP.RoutingISATableIntervalPass
import OAI.Computability.BorderVNP.RoutingISATableAddressImage
import OAI.Computability.BorderVNP.RoutingISATableEvents
import OAI.Computability.BorderVNP.RoutingISAOffsetPass

/-! # Execution and total cost of the fixed public routing schedule

The word program constructs its entire schedule from descriptor lengths. Every
intermediate addition, multiplication, and division is justified from the input
layout. No step iterates over the represented wire bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The physical straight-line and loop code computes the exact four table images.
Its tick cost is linear in the number of descriptors plus cubic in the number of teams. -/
theorem scheduleTable_image {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : TableLayout) (row : ℕ → TableRow)
    (al : l.Allocated w) (fit : l.RowsFit w row) (frame : (pub 0).val = l.frame)
    (loaded : l.frameFields (readings m)) (records : l.recordsMatch row (readings m)) :
    BoundedRun pub macros scheduleTable s m (256*((l.teams+1)^3+l.count+1))
      (fun z => l.ready z ∧ l.Image row (readings m) z.mem) := by
  let N := l.teams
  let M := readings m
  let P (z : NatState) := l.ready z ∧ l.Image row M z.mem
  let ic := l.count*(tabulateInterval.slots+1)+2
  let oc := 128*(N+1)^3
  have post (u : Bank w) (mu : Memory w) (h : l.ready (.ofWords u mu) ∧ l.IntervalImage row M l.count (readings mu)) :
      BoundedRun pub macros offsetPass u mu oc P := by
    have rr := offsetPass_image pub macros l row u mu al fit h.1 h.2.widths
    apply rr.mono le_rfl
    rintro z ⟨ready,off,used,out⟩
    refine ⟨ready, ⟨?_, ?_, off, used, ?_⟩⟩
    · intro k hk
      have inside := l.contains_offset (a := .widths) hk
      exact (out _ (al.separate .widths .offsets _ (by decide) inside)
        (al.separate .widths .used _ (by decide) inside)).trans (h.2.widths k hk)
    · intro j hj
      have inside := l.contains_offset (a := .ordinals) hj
      exact (out _ (al.separate .ordinals .offsets _ (by decide) inside)
        (al.separate .ordinals .used _ (by decide) inside)).trans (h.2.ordinals j hj)
    · intro x hw ho hf hu
      exact (out x hf hu).trans (h.2.outside x hw ho)
  have middle (u : Bank w) (mu : Memory w)
      (h : l.ready (.ofWords u mu) ∧ readings mu = zeroPrefix l.widths (N^2) M) :
      BoundedRun pub macros (.seq intervalPass offsetPass) u mu (ic+oc) P :=
    (run_intervalPass pub macros l row al fit M records u mu h.1
      (h.2 ▸ intervalImage_cleared l row M)).seq post
  have init := (run_tableSetup pub macros s m l al frame loaded).seq
    (b := .seq clearPairWidths (.seq intervalPass offsetPass)) (Q := P)
    (t := (4*N^2+2)+(ic+oc)) (fun u mu h =>
      (run_clearPairWidths pub macros l al u mu h.1).seq (fun t mt h' =>
        middle t mt ⟨h'.1,h'.2.trans (congrArg (zeroPrefix l.widths (N^2)) h.2)⟩))
  apply init.mono _ (fun _ h => h)
  have hsetup : tableSetup.slots ≤ 128 := by decide
  have hinterval : tabulateInterval.slots+1 ≤ 128 := by decide
  dsimp only [ic,oc,N]
  nlinarith only [hsetup, Nat.mul_le_mul_left l.count hinterval, Nat.zero_le (l.teams^3),
    Nat.zero_le (l.teams^2), Nat.zero_le l.teams, Nat.zero_le l.count]

/-- Running the emitted finite team opcode table from PC zero accepts on its genuine
chronological memory trace. Each step consumes no guess and contributes sign plus.
Every read and overwritten old word is consistent with the original memory. -/
theorem scheduleTable_execute {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : TableLayout) (row : ℕ → TableRow)
    (al : l.Allocated w) (fit : l.RowsFit w row) (frame : (pub 0).val = l.frame)
    (loaded : l.frameFields (readings m)) (records : l.recordsMatch row (readings m)) :
    ∃ es t mt, Runs pub macros scheduleTable s m es t mt ∧
      TeamRAM.execute (scheduleTable.program.fetch pub macros) ⟨0,s⟩ m (es.map TeamRAM.Event.choices) = some es ∧
      TeamRAM.Correct m es ∧ (∀ e ∈ es, e.choices = [] ∧ e.sign = .plus) ∧
      traceCost es ≤ 256*((l.teams+1)^3+l.count+1) ∧ l.Image row (readings m) (readings mt) ∧
      AddressTables al.teamCount (l.widthMatrix row) (readings pub) (readings mt) := by
  obtain ⟨es,t,mt,run,cost,_,image⟩ := scheduleTable_image pub macros s m l row al fit frame loaded records
  have exec := run.execute
  exact ⟨es,t,mt,run,exec,(TeamRAM.execute_spec exec).2.1,run.unsigned_events scheduleTable_unsigned,
    cost,image,image.addressTables al _ frame loaded⟩

end RoutingISA

end BorderVNP
end Computability
end OAI
