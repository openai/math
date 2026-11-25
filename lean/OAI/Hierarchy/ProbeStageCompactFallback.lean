import OAI.Hierarchy.ProbeStageCompactScanStart

namespace OAI
/-! # Refinement of every native fallback countdown and candidate update -/
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

private theorem memory_update {w : ℕ} (m : Memory w) (cell v : Word w) :
    writeMemory m cell v=Function.update m cell.val v := by
  funext x
  by_cases atCell : x=cell.val
  · subst x
    simp [writeMemory]
  · simp [writeMemory,atCell]

theorem fallback_model (hh : 4≤h) (u v : Memory W) (saved : Fin 8→Word W) (initial : Model j i saved u v)
    (limit : (u ((S).remaining:Word W).val).val ≤ radix h d)
    (addresses : ∀ side (c : Fin (radix h d)),
      Common j i (u (scratch h d j (countPtr side):Word W).val+(c.val:Word W)).val) :
    Model j i saved (Fallback.image (Record.fallback A R S) u) (Fallback.image (Record.fallback A Q S) v) := by
  let cell:Word W:=(S).remaining
  let ptr (side : Bool) : ℕ:=(scratch h d j (countPtr side):Word W).val
  let f:=Record.fallback A R S
  let g:=Record.fallback A Q S
  have cellVal : cell.val=scratch h d j 7 := Fin.val_cast_of_lt (scratch_fits j 7)
  have cellCommon : Common j i cell.val := cellVal ▸ common_temp j i hh 7
  have ptrCell (side : Bool) : ptr side≠cell.val := by
    dsimp only [ptr]
    rw [Fin.val_cast_of_lt (scratch_fits j _),cellVal]
    apply scratch_ne j
    cases side <;> decide
  have ptrChosen (side : Bool) : ptr side≠(R).chosen := by
    dsimp only [ptr]
    rw [Fin.val_cast_of_lt (scratch_fits j _)]
    exact (chosen_low j i _).ne'
  have origChosen : ((R).chosen:Word W).val=(R).chosen :=
    Fin.val_cast_of_lt ((chosen_low j i 7).trans (scratch_fits j 7))
  have stageChosen : ((Q).chosen:Word W).val=(Q).chosen :=
    Fin.val_cast_of_lt ((chosen_before j hh 7).trans (scratch_fits j 7))
  have loop (t : ℕ) (a b : Memory W) (rel : Model j i saved a b)
      (cur : a cell.val=(t:Word W)) (cap : t ≤ radix h d)
      (ptrs : ∀ side,a (ptr side)=u (ptr side)) :
      Model j i saved (WordStore.down cell (Fallback.next f) t a)
        (WordStore.down cell (Fallback.next g) t b) := by
    induction t generalizing a b with
    | zero => exact rel
    | succ t ih =>
      let a' := writeMemory a cell (a cell.val-1)
      let b' := writeMemory b cell (b cell.val-1)
      have mid : Model j i saved a' b' := by
        dsimp only [a',b']
        rw [memory_update,memory_update,rel.common _ cellCommon]
        exact rel.update_common cellCommon _
      have now : a' cell.val=(t:Word W) := by simp [a',writeMemory,cur,Nat.cast_add]
      have oldPtr (side : Bool) : a' (ptr side)=u (ptr side) := by
        simpa only [a',memory_update,Function.update_of_ne (ptrCell side)] using ptrs side
      have ctr (side : Bool) : b' (b' (ptr side)+(t:Word W)).val=a' (a' (ptr side)+(t:Word W)).val := by
        have shared : b' (ptr side)=a' (ptr side) := mid.temp hh (countPtr side)
        rw [shared,oldPtr side]
        exact mid.common _ (addresses side ⟨t,by omega⟩)
      have possible : Fallback.possible g b' (t:Word W) ↔ Fallback.possible f a' (t:Word W) := by
        change (b' (b' (ptr true)+(t:Word W)).val<_ ∧ b' (b' (ptr false)+(t:Word W)).val<_) ↔
          (a' (a' (ptr true)+(t:Word W)).val<_ ∧ a' (a' (ptr false)+(t:Word W)).val<_)
        rw [ctr true,ctr false,show g.quota=f.quota from rfl]
      have output : b' ((Q).chosen:Word W).val=a' ((R).chosen:Word W).val := by
        rw [stageChosen,origChosen]
        exact mid.result 0
      have picked : Fallback.result g b'=Fallback.result f a' := by
        change (if Fallback.possible g b' (b' cell.val) then b' cell.val else b' ((Q).chosen:Word W).val)=
          (if Fallback.possible f a' (a' cell.val) then a' cell.val else a' ((R).chosen:Word W).val)
        rw [mid.common _ cellCommon,now,output]
        by_cases ok : Fallback.possible f a' (t:Word W)
        · simp only [ite_eq_left ok,ite_eq_left (possible.mpr ok)]
        · simp only [ite_eq_right ok,ite_eq_right (fun h=>ok (possible.mp h))]
      have step : Model j i saved (Fallback.next f a') (Fallback.next g b') := by
        dsimp only [Fallback.next]
        rw [picked]
        exact mid.update_result 0 _
      apply ih (Fallback.next f a') (Fallback.next g b') step
      · have away : cell.val≠f.chosen := cellVal ▸ (chosen_low j i 7).ne'
        exact (Function.update_of_ne away _ _).trans now
      · omega
      · intro side
        exact (Function.update_of_ne (ptrChosen side) _ _).trans (oldPtr side)
  change Model j i saved (WordStore.down cell (Fallback.next f) (u cell.val).val u)
    (WordStore.down cell (Fallback.next g) (v cell.val).val v)
  rw [initial.common _ cellCommon]
  exact loop _ u v initial (by simp) limit (fun _=>rfl)

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
