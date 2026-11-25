import OAI.Hierarchy.ProbeStageCompactFast

namespace OAI
/-! # The two native branches enter fallback with the same cursor and selected word -/
namespace Hierarchy.ProbeStage.Native.Compact
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
set_option maxRecDepth 4096
variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => wordBits h d copies
local notation "A" => recordAdvice h d j
local notation "S" => recordScratch h d j
local notation "R" => recordRow h d j i
local notation "Q" => row h

theorem chosen_before (hh : 4≤h) (q : Fin 12) : (Q).chosen<scratch h d j q := by
  have small : base h+3<base h+8 := by omega
  exact small.trans_le ((window_before (d:=d) hh j).trans (cell_low (h:=h) j (.temp q)))

theorem scan_model (hd : 1≤d) (hh : 4≤h) (π : Equiv.Perm (Fin (2^h))) (m n : Memory W)
    (saved : Fin 8→Word W) (rom : immutable h d W j m)
    (ids : ordinalIDs j i hd π m) (pre : PrefixState hd π j i.val m)
    (fast : Model j i saved (fastMemory j i m)
      (FastField.image (Record.find A S) (Record.writes (Record.prepare A Q S) n))) :
    Model j i saved (scanningMemory j i m) (Record.scanInput A S Q n) := by
  let orig:=fastMemory j i m
  let stg:=FastField.image (Record.find A S) (Record.writes (Record.prepare A Q S) n)
  change Model j i saved orig stg at fast
  let addr:Word W:=(S).bit
  let ℓ:=stringLength h
  let rowColors:=(formatAdvice h d).row (queryRow j i π)
  let idx:=PackedMask.firstIndex rowColors (queryGood j i π)
  have lim : idx≤ℓ := by
    unfold idx PackedMask.firstIndex
    dsimp only
    split
    · exact (Fin.isLt _).le
    · exact le_rfl
  have source:=choice_input hd j i π m rom ids pre
  have index : orig addr.val=(idx:Word W) := by
    change FastField.image (Record.find A S) _ (scratch h d j 6:Word W).val=_
    rw [Fin.val_cast_of_lt (scratch_fits j 6)]
    change Function.update _ (scratch h d j 6) _ (scratch h d j 6)=_
    rw [Function.update_self]
    exact FastField.machine_choice _ _ _ _ _ _ source.packed source.length source.pos source.room source.avail
  have shared : stg addr.val=orig addr.val := fast.temp hh 6
  have choice : Record.bootChoice A S stg=Record.bootChoice A S orig := by
    change (if stg addr.val=(ℓ:Word W) then _ else _)=(if orig addr.val=(ℓ:Word W) then _ else _)
    rw [shared,index]
    split_ifs with full
    · rfl
    · have diff : idx≠ℓ := fun e=>full (congrArg (fun u : ℕ=>(u:Word W)) e)
      have lt : idx<ℓ := lt_of_le_of_ne lim diff
      exact string_model j i hd hh π m n saved rom ids fast ⟨idx,lt⟩
  have count : Record.bootCount A S stg=Record.bootCount A S orig := by
    change (if stg addr.val=_ then _ else _)=(if orig addr.val=_ then _ else _)
    rw [shared]
  have sr : ((S).bit:Word W).val≠(R).chosen := by
    change (scratch h d j 6:Word W).val≠(R).chosen
    rw [Fin.val_cast_of_lt (scratch_fits j 6)]
    exact (chosen_low j i 6).ne'
  have sq : ((S).bit:Word W).val≠(Q).chosen := by
    change (scratch h d j 6:Word W).val≠(Q).chosen
    rw [Fin.val_cast_of_lt (scratch_fits j 6)]
    exact (chosen_before j hh 6).ne'
  change Model j i saved (Record.writes (Record.start A R S) orig) (Record.writes (Record.start A Q S) stg)
  rw [Record.start_image A R S orig sr,Record.start_image A Q S stg sq,choice,count]
  exact (fast.update_result 0 _).update_common (common_temp j i hh 7) _

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
