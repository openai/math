import OAI.Hierarchy.ProbeStagePreparedWords
import OAI.Hierarchy.ProbeStageRecordChoice

namespace OAI
/-! # Physical counter, mask, and string reads at the chooser's two checkpoints -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
attribute [local instance] Classical.decEq
noncomputable section

variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => wordBits h d copies
local notation "S" => recordScratch h d j.val
local notation "R" => recordRow h d j.val i.val
local notation "A" => recordAdvice h d j.val

def fastMemory (m : Memory W) := FastField.image (Record.find A S) (preparedMemory j i m)
def scanningMemory (m : Memory W) := Record.scanInput A S R m

theorem fast_frame (m : Memory W) (x : ℕ) (outside : x≠scratch h d j 6) :
    fastMemory j i m x=preparedMemory j i m x := Function.update_of_ne outside _ _

theorem scanning_frame (m : Memory W) (x : ℕ) (chosen : x≠(R).chosen)
    (unused : x≠scratch h d j 7) (bit : x≠scratch h d j 6) :
    scanningMemory j i m x=preparedMemory j i m x := by
  have ready := Record.start_image A R S (fastMemory j i m) (by
    change (scratch h d j 6 : Word W).val≠(R).chosen
    rw [Fin.val_cast_of_lt (scratch_fits j 6)]
    exact (chosen_low j i 6).ne')
  change Record.writes (Record.start A R S) (fastMemory j i m) x=_
  have other : x≠(S).remaining := unused
  rw [ready,Function.update_of_ne other,Function.update_of_ne chosen,fast_frame j i m _ bit]

theorem scanning_region (m : Memory W) (k : Fin 16) (o : ℕ) :
    scanningMemory j i m (region h d j k+o)=m (region h d j k+o) := by
  have above (q : Fin 12) : scratch h d j q<region h d j k+o :=
    (scratch_separate h d j.val q k).trans_le (Nat.le_add_right _ _)
  rw [scanning_frame j i m _ ((chosen_low j i 7).trans (above 7)).ne' (above 7).ne' (above 6).ne',
    prepared_region]

theorem scanning_scratch (m : Memory W) (q : Fin 6) :
    scanningMemory j i m (scratch h d j ⟨q.val,by omega⟩)=preparedMemory j i m (scratch h d j ⟨q.val,by omega⟩) :=
  scanning_frame j i m _ (chosen_low j i _).ne' (scratch_ne j (by intro e;have := congrArg Fin.val e;dsimp at this;omega))
    (scratch_ne j (by intro e;have := congrArg Fin.val e;dsimp at this;omega))

def queryBlock (π : Equiv.Perm (Fin (2^h))) (left : Bool) := endpointKey j π left i
def queryRow (π : Equiv.Perm (Fin (2^h))) := maskIndex (history h d π j.val).tiles (radix_pos h d) i
def queryFull (π : Equiv.Perm (Fin (2^h))) (left : Bool) := by
  classical
  exact Greedy.prefixFull (endpointKey j π left) (assigned j π).color i.val (queryBlock j i π left)

def ordinalIDs (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (m : Memory W) : Prop :=
  ∀ q,m (argumentAddr j i q)=
    (argumentValue j (blockNumber hd j π (queryBlock j i π true))
      (blockNumber hd j π (queryBlock j i π false)) (queryRow j i π) q:Word W)

/-- The ABI here is exactly the output of the native endpoint publication. -/
theorem ordinalIDs_of_words (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (m : Memory W)
    (stored : ∀ q,m (argumentAddr j i q)=
      (Endpoints.words (history h d π j.val).tiles (radix_pos h d) (history h d π j.val).encode i q : Word W)) :
    ordinalIDs j i hd π m := by
  intro q
  fin_cases q <;> apply stored

def countPtr (left : Bool) : Fin 12 := if left then 0 else 1
def maskPtr (left : Bool) : Fin 12 := if left then 2 else 3

theorem prepared_mask_address (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (m : Memory W)
    (rom : immutable h d W j m) (ids : ordinalIDs j i hd π m) (left : Bool) (k : Fin (fieldChunks h)) :
    let p := preparedMemory j i m
    (p (scratch h d j (maskPtr left):Word W).val+p (scratch h d j 4:Word W).val+(k.val:Word W)).val =
      maskLocation h d j.val left (blockNumber hd j π (queryBlock j i π left)) (queryRow j i π) k := by
  let b := fun u => blockNumber hd j π (queryBlock j i π u)
  let r := queryRow j i π
  let rep := prepared_word j i hd m rom (b true) (b false) r ids
  have off := mask_offset hd j.isLt.le (b left) r k
  have fit := region_word j.isLt (maskArea left) off
  dsimp only
  rw [Fin.val_cast_of_lt (scratch_fits j _),Fin.val_cast_of_lt (scratch_fits j _)]
  cases left <;> simp only [maskPtr,ite_true,ite_false,Bool.false_eq_true,maskArea] at *
  · rw [show preparedMemory j i m (scratch h d j 3)=_ from rep 3,
      show preparedMemory j i m (scratch h d j 4)=_ from rep 4,←Nat.cast_add,←Nat.cast_add]
    apply Fin.val_cast_of_lt
    simpa [loadedValue,maskArea,Nat.add_assoc] using fit
  · rw [show preparedMemory j i m (scratch h d j 2)=_ from rep 2,
      show preparedMemory j i m (scratch h d j 4)=_ from rep 4,←Nat.cast_add,←Nat.cast_add]
    apply Fin.val_cast_of_lt
    simpa [loadedValue,maskArea,Nat.add_assoc] using fit

theorem scanning_count_address (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (m : Memory W)
    (rom : immutable h d W j m) (ids : ordinalIDs j i hd π m) (left : Bool) (c : Fin (radix h d)) :
    (scanningMemory j i m (scratch h d j (countPtr left):Word W).val+(c.val:Word W)).val =
      counterLocation h d j.val left (blockNumber hd j π (queryBlock j i π left)) c := by
  let b := fun u => blockNumber hd j π (queryBlock j i π u)
  let rep := prepared_word j i hd m rom (b true) (b false) (queryRow j i π) ids
  have fit := region_word j.isLt (countArea left) (count_offset hd j.isLt.le (b left) c)
  rw [Fin.val_cast_of_lt (scratch_fits j _)]
  cases left
  · rw [show scanningMemory j i m (scratch h d j (countPtr false))=_ from (scanning_scratch j i m 1).trans (rep 1),←Nat.cast_add]
    apply Fin.val_cast_of_lt
    simpa [loadedValue,countArea,Nat.add_assoc] using fit
  · rw [show scanningMemory j i m (scratch h d j (countPtr true))=_ from (scanning_scratch j i m 0).trans (rep 0),←Nat.cast_add]
    apply Fin.val_cast_of_lt
    simpa [loadedValue,countArea,Nat.add_assoc] using fit

theorem prepared_mask (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (m : Memory W)
    (rom : immutable h d W j m) (ids : ordinalIDs j i hd π m) (pre : PrefixState hd π j i.val m)
    (left : Bool) (k : Fin (fieldChunks h)) :
    let p := preparedMemory j i m
    (p (p (scratch h d j (maskPtr left):Word W).val+p (scratch h d j 4:Word W).val+(k.val:Word W)).val).val =
      PackedMask.word ((formatAdvice h d).row (queryRow j i π)) (queryFull j i π left) (fieldWidth h) k.val := by
  let b := blockNumber hd j π (queryBlock j i π left)
  let r := queryRow j i π
  have fr : preparedMemory j i m (maskLocation h d j.val left b r k)=m (maskLocation h d j.val left b r k) := by
    simpa only [maskLocation,Nat.add_assoc] using prepared_region j i m (maskArea left)
      (b.val*((radix h d)^4*fieldChunks h)+(rowCode r*fieldChunks h+k.val))
  dsimp only
  rw [prepared_mask_address j i hd π m rom ids,fr,pre.2 left (queryBlock j i π left) r k]
  apply Fin.val_cast_of_lt
  exact (PackedMask.word_lt ..).trans_le ((least_size h d).trans (regionSize_fits j).le)

theorem scanning_count (hd : 1≤d) (π : Equiv.Perm (Fin (2^h))) (m : Memory W)
    (rom : immutable h d W j m) (ids : ordinalIDs j i hd π m) (pre : PrefixState hd π j i.val m)
    (left : Bool) (c : Fin (radix h d)) :
    (scanningMemory j i m ((scanningMemory j i m (scratch h d j (countPtr left):Word W).val)+(c.val:Word W)).val).val =
      Greedy.prefixCount (endpointKey j π left) (assigned j π).color i.val (queryBlock j i π left) c := by
  let b := blockNumber hd j π (queryBlock j i π left)
  have fr : scanningMemory j i m (counterLocation h d j.val left b c)=m (counterLocation h d j.val left b c) := by
    simpa only [counterLocation,Nat.add_assoc] using scanning_region j i m (countArea left) (b.val*radix h d+c.val)
  rw [scanning_count_address j i hd π m rom ids,fr,pre.1 left (queryBlock j i π left) c]
  apply Fin.val_cast_of_lt
  have count : Greedy.prefixCount (endpointKey j π left) (assigned j π).color i.val (queryBlock j i π left) c ≤ 2^h := by
    unfold Greedy.prefixCount Greedy.load
    calc
      _ ≤ Fintype.card (Fin (2^h)) := Finset.card_le_univ _
      _ = _ := Fintype.card_fin _
  exact count.trans_lt ((height_extent h d).trans_lt (extent_word h d copies))

end
end Hierarchy.ProbeStage.Native

end OAI
