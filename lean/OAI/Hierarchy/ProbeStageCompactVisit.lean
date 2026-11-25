import OAI.Hierarchy.ProbeStageCompactChoice
import OAI.Hierarchy.ProbeStageCompactEndpoint
import OAI.Hierarchy.ProbeStageCompactBody
import OAI.Hierarchy.ProbeStageCompactTransfer

namespace OAI
/-! # One actual counted allocator visit, with the complete external memory restored -/

namespace Hierarchy.ProbeStage.Native.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d
local notation "A" => recordAdvice h d j
local notation "S" => recordScratch h d j
local notation "R" => recordRow h d j i.val

theorem body_exec (hh : 4≤ h) (hd : 1≤ d) (π : Equiv.Perm (Fin (2^h))) (m : Memory W)
    (rom : immutable h d W j m) (ids : ∀q,m (argumentAddr j i q)=
      (Endpoints.words (history h d π j.val).tiles (radix_pos h d) (history h d π j.val).encode i q:Word W))
    (pre : PrefixState hd π j i.val m) (zero : ∀q : Fin 6,Record.image A S R m (base h+q.val)=0) :
    (body h d j).Exec (CompactLoop.cells h i.val m) (CompactLoop.cells h i.val (Record.image A S R m))
      (stageClock+rowTicks h d j i.val m+unstageClock) := by
  let entry:=CompactLoop.cells h i.val m
  let n:=staged j i entry
  let snap:=saved j i m
  have first : (stage h d j).Exec entry n stageClock := stage_exec hd hh j i entry (cells_cursor i m)
  have middle : (Record.procedure W A S (row h)).Exec n (Record.image A S (row h) n)
      (1000+82*(recordAdvice h d j).chunks+100*Record.scans A S (row h) n+18*Record.clears A S (row h) n) :=
    Record.execute A S (row h) n (staged_fits j i hh)
  have ⟨leftRel,scans⟩:=choice_model j i hd hh π m n snap rom ids pre
    (stage_model j i hh m) (saved_id j i hh m)
  have ls:=start_side hd j i π m rom ids pre true
  have left:=endpoint_commit hd j i _ _ _ _ _ ls
  have rs:=after_left hd j i left (start_side hd j i π m rom ids pre false)
  have ⟨rightRel,lcost⟩:=endpoint_model hd hh j i true _ _ _ _ _ snap leftRel ls
  have ⟨outRel,rcost⟩:=endpoint_model hd hh j i false _ _ _ _ _ snap rightRel rs
  have sameClears : Record.clears A S (row h) n=Record.clears A S R m := by
    exact congrArg₂ Nat.add lcost rcost
  rw [scans,sameClears] at middle
  have cur : Record.image A S (row h) n (base h+6)=(i.val:Word W) := by
    have prior:=outRel.fixed (6 : Fin 8) (Or.inr (by decide))
    have old:=staged_frame j i entry (base h+6) (Or.inr le_rfl)
    exact prior.trans (old.trans (cells_cursor i m))
  have last : (unstage h d j).Exec (Record.image A S (row h) n) (unstaged j i (Record.image A S (row h) n)) unstageClock :=
    unstage_exec hd hh j i (Record.image A S (row h) n) cur
  rw [unstage_model j i hd hh m (Record.image A S R m) (Record.image A S (row h) n) outRel zero] at last
  intro P regs K M
  exact Procedure.Exec.then (Procedure.Exec.then first middle) last M

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
