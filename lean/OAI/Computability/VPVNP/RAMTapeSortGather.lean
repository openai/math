import OAI.Computability.VPVNP.RAMTapeSortGatherScan
import OAI.Computability.VPVNP.RAMSortBlockSlices

/-! # Fetching one record from an arbitrary physical sort block

The two reverse buffers restore the selected record and then the skipped
prefix. The selected record also goes to the operand stack in forward order.
The finite control depends only on the five-field record format. Neither the
word width nor the requested offset occurs in its states.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortGather

open Routine

private def emit (x : Bool) := (push Port.block x).followedBy (push Port.output x)

private def emitRecord : FiniteRoutine Port :=
  .ofRoutine (popLoop Port.recordBack (fun _ => true) (emit false) (emit true))

private def rewindPrefix : FiniteRoutine Port :=
  .ofRoutine (popLoop Port.saved (fun _ => true) (push Port.block false) (push Port.block true))

private theorem set_block (w i : ℕ) (block saved selected out val : List Bool) :
    Function.update (store w i block saved selected out) .block val =
      store w i val saved selected out := by funext k; cases k <;> rfl

private theorem set_output (w i : ℕ) (block saved selected out val : List Bool) :
    Function.update (store w i block saved selected out) .output val =
      store w i block saved selected val := by funext k; cases k <;> rfl

private theorem set_saved (w i : ℕ) (block saved selected out val : List Bool) :
    Function.update (store w i block saved selected out) .saved val =
      store w i block val selected out := by funext k; cases k <;> rfl

private theorem set_recordBack (w i : ℕ) (block saved selected out val : List Bool) :
    Function.update (store w i block saved selected out) .recordBack val =
      store w i block saved val out := by funext k; cases k <;> rfl

private theorem emitRecord_runs (w i : ℕ) (block saved data out : List Bool) :
    emitRecord.Runs (3*data.length+1) (store w i block saved data out)
      (store w i (data.reverse++block) saved [] (data.reverse++out)) := by
  induction data generalizing block out with
  | nil =>
    exact Runs.popLoop_empty Port.recordBack (fun _ => true) (emit false) (emit true) rfl
  | cons b bs ih =>
    have pushB := runs_push Port.block b (store w i block saved bs out)
    have pushO := runs_push Port.output b (store w i (b::block) saved bs out)
    simp only [set_block, set_output, store] at pushB pushO
    have he := pushB.followedBy pushO
    have hh := Runs.popLoop_continue Port.recordBack (fun _ => true) (emit false) (emit true)
      (s := store w i block saved (b::bs) out) rfl rfl
      (by rw [set_recordBack]; cases b <;> exact he) (ih (b::block) (b::out))
    rw [show 1+(1+1)+(3*bs.length+1) = 3*(bs.length+1)+1 by omega] at hh
    simpa only [emitRecord, FiniteRoutine.ofRoutine, FiniteRoutine.Runs, List.reverse_cons,
      List.append_assoc, List.singleton_append, List.length_cons] using hh

private theorem rewindPrefix_runs (w i : ℕ) (block saved selected out : List Bool) :
    rewindPrefix.Runs (2*saved.length+1) (store w i block saved selected out)
      (store w i (saved.reverse++block) [] selected out) := by
  induction saved generalizing block with
  | nil =>
    exact Runs.popLoop_empty Port.saved (fun _ => true) (push Port.block false) (push Port.block true) rfl
  | cons b bs ih =>
    have hp := runs_push Port.block b (store w i block bs selected out)
    simp only [set_block, store] at hp
    have hh := Runs.popLoop_continue Port.saved (fun _ => true) (push Port.block false)
      (push Port.block true) (s := store w i block (b::bs) selected out) rfl rfl
      (by rw [set_saved]; cases b <;> exact hp) (ih (b::block))
    rw [show 1+1+(2*bs.length+1) = 2*(bs.length+1)+1 by omega] at hh
    simpa only [rewindPrefix, FiniteRoutine.ofRoutine, FiniteRoutine.Runs, List.reverse_cons,
      List.append_assoc, List.singleton_append, List.length_cons] using hh

/-- Consume a unary record offset, preserve its source block, and prepend the selected
record to the destination. All temporary stacks are cleared on return. -/
def fetch : FiniteRoutine Port :=
  ((skip.followedBy select).followedBy emitRecord).followedBy rewindPrefix

/-- Tick allowance to skip i five-word records, fetch the next one and restore both it and the
skipped prefix to the block. -/
def cost (i w : ℕ) := i*(40*w+12)+45*w+14

theorem fetch_runs (w i : ℕ) (s : Stacks Port) (pre data tail : List Bool)
    (hp : pre.length = i*(5*w)) (hd : data.length = 5*w)
    (hb : s .block = pre ++ data ++ tail) (hi : s .offset = List.replicate i true)
    (hw : s .width = List.replicate w true) (ht : s .widthBack = [])
    (hs : s .saved = []) (hr : s .recordBack = []) :
    fetch.Runs (cost i w) s
      (Function.update (Function.update s .offset []) .output (data ++ s .output)) := by
  have h₁ := skip_runs w i pre (data++tail) [] [] (s .output) hp
  have h₂ := select_runs w 0 data tail pre.reverse [] (s .output) hd
  have h₃ := emitRecord_runs w 0 tail pre.reverse data.reverse (s .output)
  have h₄ := rewindPrefix_runs w 0 (data++tail) pre.reverse [] (data++s .output)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h₁ h₂ h₃ h₄
  have h := ((FiniteRoutine.Runs.followedBy h₁ h₂).followedBy h₃).followedBy h₄
  have hstart : store w i (pre ++ (data ++ tail)) [] [] (s .output) = s := by
    funext k
    cases k <;> simp [store, hb, hi, hw, ht, hs, hr, List.append_assoc]
  have hend : store w 0 (pre ++ (data ++ tail)) [] [] (data++s .output) =
      Function.update (Function.update s .offset []) .output (data++s .output) := by
    funext k
    cases k <;> simp [store, hb, hw, ht, hs, hr, List.append_assoc]
  rw [hstart, hend, hp, hd] at h
  unfold fetch
  convert h using 1
  unfold cost
  ring

open RAMSerialization

/-- In the physical block encoding the fetched bits are exactly the record slice,
including when the supplied bits encode a malformed record. -/
theorem fetch_slice_runs (H w : ℕ) (i : Fin (4*H)) (bits : Fin (RAMLayout.blockBits H w) → Bool)
    (s : Stacks Port) (hb : s .block = List.ofFn bits) (hi : s .offset = List.replicate i.val true)
    (hw : s .width = List.replicate w true) (ht : s .widthBack = [])
    (hs : s .saved = []) (hr : s .recordBack = []) :
    fetch.Runs (cost i.val w) s (Function.update (Function.update s .offset []) .output
      (List.ofFn (recordSlice H w bits i) ++ s .output)) := by
  let off := i.val*(5*w)
  let all := List.ofFn bits
  have hend : off+5*w ≤ all.length := by
    change i.val*(5*w)+5*w ≤ (List.ofFn bits).length
    rw [List.length_ofFn, RAMLayout.blockBits, Nat.mul_assoc, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ i.isLt
  have hpre : (all.take off).length = off := by simp [List.length_take, show off ≤ all.length by omega]
  have hdata : ((all.drop off).take (5*w)).length = 5*w := by
    simp [List.length_take, List.length_drop, show 5*w ≤ all.length-off by omega]
  have heq : (all.drop off).take (5*w) = List.ofFn (recordSlice H w bits i) := by
    apply List.ext_getElem (by simp [hdata])
    intro k hk _
    rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn]
    unfold recordSlice
    apply congrArg bits
    apply Fin.ext
    simp only [off, Nat.mul_assoc]
  have split : s .block = all.take off ++ (all.drop off).take (5*w) ++ (all.drop off).drop (5*w) := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop, hb]
  have h := fetch_runs w i.val s (all.take off) ((all.drop off).take (5*w))
    ((all.drop off).drop (5*w)) hpre hdata split hi hw ht hs hr
  rwa [heq] at h

end RAMTape.SortGather

end VPVNP
end Computability
end OAI
