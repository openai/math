import OAI.Hierarchy.ProbeStagePhysicalStart

namespace OAI
/-! # The two native preselection runs agree at the entrance to the rank commits -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

private theorem fallback_cursor {w : ℕ} (s : Fallback.Layout) (m : Memory w)
    (apart : (s.remaining : Word w).val ≠ s.chosen) :
    Fallback.image s m (s.remaining : Word w).val=0 := by
  let cell : Word w := s.remaining
  have finish (t : ℕ) (mem : Memory w) (cur : mem cell.val=(t:Word w)) :
      WordStore.down cell (Fallback.next s) t mem cell.val=0 := by
    induction t generalizing mem with
    | zero => simpa [WordStore.down] using cur
    | succ t ih =>
      change WordStore.down cell (Fallback.next s) t
        (Fallback.next s (writeMemory mem cell (mem cell.val-1))) cell.val=0
      apply ih
      let nextMem := writeMemory mem cell (mem cell.val-1)
      have kept : Fallback.next s nextMem cell.val=nextMem cell.val :=
        Function.update_of_ne (show cell.val≠s.chosen from apart) _ _
      change Fallback.next s nextMem cell.val=(t:Word w)
      rw [kept]
      change (if cell.val=cell.val then mem cell.val-1 else mem cell.val)=(t:Word w)
      simp [cur,Nat.cast_add]
  exact finish _ m (by simp [cell])

variable {h d : ℕ} (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d
local notation "A" => recordAdvice h d j.val
local notation "S" => recordScratch h d j.val
local notation "R" => recordRow h d j.val i.val

private theorem fixed_bit (m : Memory W) (rom : immutable h d W j m)
    (ids : ordinalIDs j i hd π m) (pre : PrefixState hd π j i.val m) :
    atCommits j i m (scratch h d j 6)=
      (PackedMask.firstIndex ((formatAdvice h d).row (queryRow j i π)) (queryGood j i π):Word W) := by
  let s := Record.fallback A R S
  let scan := scanningMemory j i m
  let fast := fastMemory j i m
  have hh := choice_input hd j i π m rom ids pre
  have kept := Fallback.frame s (scan (s.remaining:Word W).val).val scan (scratch h d j 6)
    (by
      change scratch h d j 6≠(scratch h d j 7:Word W).val
      rw [Fin.val_cast_of_lt (scratch_fits j 7)]
      exact scratch_ne j (by decide : (6:Fin 12)≠7)) hh.bitChosen
  change atCommits j i m (scratch h d j 6)=scan (scratch h d j 6) at kept
  rw [kept]
  have start := Record.start_image A R S fast (by
    simpa only [Fin.val_cast_of_lt hh.bitFit] using hh.bitChosen)
  change Record.writes (Record.start A R S) fast _=_
  have away : scratch h d j 6≠(S).remaining := scratch_ne j (by decide : (6:Fin 12)≠7)
  have other : scratch h d j 6≠(R).chosen := (chosen_low j i 6).ne'
  rw [start,Function.update_of_ne away,Function.update_of_ne other]
  change FastField.image (Record.find A S) (preparedMemory j i m) (Record.find A S).output=_
  rw [FastField.image,Function.update_self]
  exact FastField.machine_choice (Record.find A S) _ _ _ _ _ hh.packed hh.length hh.pos hh.room hh.avail

theorem atCommits_agree (m n : Memory W) (romM : immutable h d W j m) (romN : immutable h d W j n)
    (argsM : ∀ q,m (argumentAddr j i q)=
      (Endpoints.words (history h d π j.val).tiles (radix_pos h d) (history h d π j.val).encode i q:Word W))
    (argsN : ∀ q,n (argumentAddr j i q)=
      (Endpoints.words (history h d π j.val).tiles (radix_pos h d) (history h d π j.val).encode i q:Word W))
    (preM : PrefixState hd π j i.val m) (preN : PrefixState hd π j i.val n)
    (agree : ∀x,x<heapEnd h d copies → m x=n x) :
    ∀x,x<heapEnd h d copies → atCommits j i m x=atCommits j i n x := by
  classical
  have idsM := ordinalIDs_of_words j i hd π m argsM
  have idsN := ordinalIDs_of_words j i hd π n argsN
  intro x below
  by_cases chosen : x=(R).chosen
  · subst x
    exact (ordinal_choice hd j i π m romM argsM preM).2.trans
      (ordinal_choice hd j i π n romN argsN preN).2.symm
  by_cases bit : x=scratch h d j 6
  · subst x
    exact (fixed_bit hd π j i m romM idsM preM).trans (fixed_bit hd π j i n romN idsN preN).symm
  by_cases cursor : x=scratch h d j 7
  · subst x
    let s := Record.fallback A R S
    have fit : (s.remaining:Word W).val=scratch h d j 7 := Fin.val_cast_of_lt (scratch_fits j 7)
    have apart : (s.remaining:Word W).val≠s.chosen := by rw [fit];exact (chosen_low j i 7).ne'
    have zero (mem : Memory W) : atCommits j i mem (scratch h d j 7)=0 := by
      rw [←fit]
      exact fallback_cursor s (scanningMemory j i mem) apart
    exact (zero m).trans (zero n).symm
  rw [atCommits,atCommits,Record.left_prepared _ _ _ _ _ bit chosen cursor (scratch_fits j 7),
    Record.left_prepared _ _ _ _ _ bit chosen cursor (scratch_fits j 7)]
  change preparedMemory j i m x=preparedMemory j i n x
  by_cases slot : ∃ q : Fin 6,x=scratch h d j (Fin.castLE (by decide : 6≤12) q)
  · obtain ⟨q,hq⟩ := slot
    rw [hq]
    exact (prepared_word j i hd m romM _ _ _ idsM q).trans (prepared_word j i hd n romN _ _ _ idsN q).symm
  · have away (q : Fin 6) : x≠scratch h d j (Fin.castLE (by decide : 6≤12) q) := fun eq => slot ⟨q,eq⟩
    rw [prepared_frame j i m x away,prepared_frame j i n x away]
    exact agree x below

end
end Hierarchy.ProbeStage.Native

end OAI
