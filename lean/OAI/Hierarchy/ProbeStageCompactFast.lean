import OAI.Hierarchy.ProbeStageCompactPrepare
import OAI.Hierarchy.ProbeStagePhysicalChoice

namespace OAI
/-! # The staged packed-mask lookup and its literal string read -/
namespace Hierarchy.ProbeStage.Native.Compact
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => wordBits h d copies
local notation "A" => recordAdvice h d j
local notation "S" => recordScratch h d j

theorem Model.temp {j : Fin (rounds d)} {i : Fin (2^h)} {saved : Fin 8→Word W} {m n : Memory W} (s : Model j i saved m n)
    (hh : 4≤h) (q : Fin 12) : n ((scratch h d j q:Word W).val)=m ((scratch h d j q:Word W).val) := by
  rw [Fin.val_cast_of_lt (scratch_fits j q)]
  exact s.common _ (common_temp j i hh q)

theorem packed_model (hd : 1≤d) (hh : 4≤h) (π : Equiv.Perm (Fin (2^h))) (m n : Memory (wordBits h d copies))
    (saved : Fin 8→Word (wordBits h d copies)) (rom : immutable h d (wordBits h d copies) j m)
    (ids : ordinalIDs j i hd π m) (pre : PrefixState hd π j i.val m)
    (prepared : Model j i saved (preparedMemory j i m) (Record.writes (Record.prepare A (row h) S) n)) :
    FastField.Represents (Record.find A S) (Record.writes (Record.prepare A (row h) S) n)
      ((formatAdvice h d).row (queryRow j i π)) (queryFull j i π true) (queryFull j i π false) := by
  let look:=Record.find A S
  let p₀:=preparedMemory j i m
  let p₁:=Record.writes (Record.prepare A (row h) S) n
  let qr:=queryRow j i π
  change Model j i saved p₀ p₁ at prepared
  let read (t : Memory W) (side : Bool) (k : Fin (fieldChunks h)) :=
    t (t (scratch h d j (maskPtr side):Word W).val+t (scratch h d j 4:Word W).val+(k.val:Word W)).val
  have atMask (side : Bool) (k : Fin (fieldChunks h)) : read p₁ side k=read p₀ side k := by
    dsimp only [read]
    let b:=blockNumber hd j π (queryBlock j i π side)
    have address : (p₀ (scratch h d j (maskPtr side):Word W).val+p₀ (scratch h d j 4:Word W).val+(k.val:Word W)).val=
        maskLocation h d j side b qr k := prepared_mask_address j i hd π m rom ids side k
    rw [prepared.temp hh (maskPtr side),prepared.temp hh 4,address]
    simpa only [maskLocation,Nat.add_assoc] using prepared.common _
      (common_area j i hh (maskArea side) ⟨_,mask_offset hd j.isLt.le b qr k⟩)
  have available (k : Fin (fieldChunks h)) :
      FastField.availableWord look p₁ k.val=FastField.availableWord look p₀ k.val :=
    congrArg₂ (fun l r : Word W=>BinaryOp.bitAnd.eval l r) (atMask true k) (atMask false k)
  have small (k : Fin (fieldChunks h)) : (FastField.availableWord look p₀ k.val).val<2^fieldWidth h := by
    have left : (read p₀ true k).val<2^fieldWidth h :=
      (prepared_mask j i hd π m rom ids pre true k).le.trans_lt (PackedMask.word_lt ..)
    change ((BinaryOp.bitAnd.eval (read p₀ true k) (read p₀ false k))).val<_
    simp only [BinaryOp.eval,Fin.val_ofNat]
    exact (Nat.mod_le ..).trans_lt (Nat.and_le_left.trans_lt left)
  have source:=choice_input hd j i π m rom ids pre
  have rep : FastField.Represents look p₁ ((formatAdvice h d).row qr) (queryFull j i π true) (queryFull j i π false) := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      exact (congrArg Fin.val (atMask true ⟨k,hk⟩)).trans (source.packed.left k hk)
    · intro k hk
      exact (congrArg Fin.val (atMask false ⟨k,hk⟩)).trans (source.packed.right k hk)
    · intro k hk
      let off:=FastField.availableWord look p₀ k
      rw [available ⟨k,hk⟩]
      apply Eq.trans ?_ (source.packed.table k hk)
      have bound : off.val < regionSize h d := (small ⟨k,hk⟩).trans_le (least_size h d)
      have address : ((region h d j 7:Word W)+off).val=region h d j 7+off.val := by
        simpa using add_word (region_word j.isLt (7:Fin 16) bound)
      change p₁ ((region h d j 7:Word W)+off).val=p₀ ((region h d j 7:Word W)+off).val
      rw [address]
      exact prepared.common _ (common_area j i hh 7 ⟨_,bound⟩)
  exact rep

theorem fast_model (hd : 1≤d) (hh : 4≤h) (π : Equiv.Perm (Fin (2^h))) (m n : Memory (wordBits h d copies))
    (saved : Fin 8→Word (wordBits h d copies)) (rom : immutable h d (wordBits h d copies) j m)
    (ids : ordinalIDs j i hd π m) (pre : PrefixState hd π j i.val m)
    (prepared : Model j i saved (preparedMemory j i m) (Record.writes (Record.prepare A (row h) S) n)) :
    Model j i saved (fastMemory j i m)
      (FastField.image (Record.find A S) (Record.writes (Record.prepare A (row h) S) n)) := by
  let look:=Record.find A S
  let p₀:=preparedMemory j i m
  let p₁:=Record.writes (Record.prepare A (row h) S) n
  let qr:=queryRow j i π
  let good:=queryGood j i π
  have source:=choice_input hd j i π m rom ids pre
  have rep:=packed_model j i hd hh π m n saved rom ids pre prepared
  have original:=FastField.machine_choice look p₀ ((formatAdvice h d).row qr) _ _ good source.packed source.length source.pos source.room source.avail
  have staged:=FastField.machine_choice look p₁ ((formatAdvice h d).row qr) _ _ good rep source.length source.pos source.room source.avail
  change Model j i saved (Function.update p₀ look.output _) (Function.update p₁ look.output _)
  rw [staged.trans original.symm]
  exact prepared.update_common (common_temp j i hh 6) _

theorem string_model (hd : 1≤d) (hh : 4≤h) (π : Equiv.Perm (Fin (2^h))) (m n : Memory (wordBits h d copies))
    (saved : Fin 8→Word (wordBits h d copies)) (rom : immutable h d (wordBits h d copies) j m)
    (ids : ordinalIDs j i hd π m)
    (fast : Model j i saved (fastMemory j i m)
      (FastField.image (Record.find A S) (Record.writes (Record.prepare A (row h) S) n))) (k : Fin (stringLength h)) :
    Record.stringWord A S (FastField.image (Record.find A S) (Record.writes (Record.prepare A (row h) S) n)) (k.val:Word W)=
      Record.stringWord A S (fastMemory j i m) (k.val:Word W) := by
  let f₀:=fastMemory j i m
  let f₁:=FastField.image (Record.find A S) (Record.writes (Record.prepare A (row h) S) n)
  let qr:=queryRow j i π
  change Model j i saved f₀ f₁ at fast
  let b:=fun side=>blockNumber hd j π (queryBlock j i π side)
  have off : f₀ (scratch h d j 5:Word W).val=((rowCode qr*stringLength h:ℕ):Word W) := by
    change fastMemory j i m (scratch h d j 5:Word W).val=_
    rw [Fin.val_cast_of_lt (scratch_fits j 5),fast_frame j i m _ (scratch_ne j (by decide : (5:Fin 12)≠6))]
    exact prepared_word j i hd m rom (b true) (b false) qr ids 5
  have bound : rowCode qr*stringLength h+k.val < regionSize h d :=
    lt_of_lt_of_le ((Nat.add_lt_add_left k.isLt _).trans_le (by
      rw [←Nat.succ_mul]
      exact Nat.mul_le_mul_right _ (rowCode_lt qr))) (region_room (h:=h) hd j.isLt.le).2.2.2.1
  have fit := region_word j.isLt (6:Fin 16) bound
  change f₁ ((region h d j 6:Word W)+f₁ (scratch h d j 5:Word W).val+(k.val:Word W)).val=
    f₀ ((region h d j 6:Word W)+f₀ (scratch h d j 5:Word W).val+(k.val:Word W)).val
  rw [fast.temp hh 5,off,←Nat.cast_add,←Nat.cast_add,
    Fin.val_cast_of_lt (by simpa only [Nat.add_assoc] using fit),Nat.add_assoc]
  exact fast.common _ (common_area j i hh 6 ⟨_,bound⟩)

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
