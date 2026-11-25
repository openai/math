import OAI.Hierarchy.ProbeStageCompactWindow

namespace OAI
/-! # The six native directory reads with a fixed staging row -/

namespace Hierarchy.ProbeStage.Native.Compact
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d
local notation "A" => recordAdvice h d j
local notation "S" => recordScratch h d j
local notation "R" => recordRow h d j i

def stagedLoad (h d j : ℕ) (k : Fin 6) : Record.Load :=
  ⟨scratch h d j ⟨k.val,by omega⟩,region h d j ⟨k.val,by omega⟩,base h+(dirInput k).val⟩

theorem staged_dirs : Record.dirs A (row h) S=List.ofFn (stagedLoad h d j) := rfl

private theorem dir_model (hh : 4≤ h) (id : Fin 3→ Fin (regionSize h d)) (saved : Fin 8→ Word W)
    (args : ∀q : Fin 3,saved ⟨q.val,by omega⟩=(id q).val)
    (ks : List (Fin 6)) (m n : Memory W) (rel : Model j i saved m n)
    (words : ∀q,m (argumentAddr j i q)=((id q).val:Word W)) :
    Model j i saved
      (Record.writes (ks.map (fun k=>(physicalLoad j i k).expr)) m)
      (Record.writes (ks.map (fun k=>(stagedLoad h d j k).expr)) n) := by
  induction ks generalizing m n with
  | nil => exact rel
  | cons k ks ih =>
    let t : Fin 12 := ⟨k.val,by omega⟩
    let b : Fin 16 := ⟨k.val,by omega⟩
    let q := dirInput k
    let field : Fin 8 := ⟨q.val,by omega⟩
    have orig := (argument_low j i q t).trans (scratch_fits j t)
    have below := window_before (d:=d) hh j
    have high := cell_low (h:=h) j (.temp t)
    have fit : base h+q.val<2^W := by
      have room : scratch h d j t<2^W := scratch_fits j t
      change _≤ scratch h d j t at high
      omega
    have left : (physicalLoad j i k).addr m=region h d j b+(id q).val := by
      change ((region h d j b:Word W)+m (argumentAddr j i q:Word W).val).val=_
      rw [Fin.val_cast_of_lt orig,words,add_word (region_word j.isLt b (id q).isLt)]
    have savedKey := (rel.fixed field (Or.inl q.isLt)).trans (args q)
    have right : (stagedLoad h d j k).addr n=region h d j b+(id q).val := by
      change ((region h d j b:Word W)+n ((base h+q.val:ℕ):Word W).val).val=_
      rw [Fin.val_cast_of_lt fit,savedKey,add_word (region_word j.isLt b (id q).isLt)]
    have read := rel.common _ (common_area j i hh b (id q))
    change Model j i saved (Record.writes _ (Function.update m (scratch h d j t) (m ((physicalLoad j i k).addr m))))
      (Record.writes _ (Function.update n (scratch h d j t) (n ((stagedLoad h d j k).addr n))))
    rw [left,right,read]
    apply ih _ _ (rel.update_common (common_temp j i hh t) _)
    intro r
    simpa only [Function.update_of_ne (argument_low j i r t).ne] using words r

/-- Staging changes the three physical word addresses holding the endpoint
IDs. The six native loads still read the very same immutable directory cells. -/
theorem prepare_model (hh : 4≤ h) (hd : 1≤ d) (π : Equiv.Perm (Fin (2^h))) (m n : Memory W)
    (saved : Fin 8→ Word W) (rel : Model j i saved m n)
    (args : ∀q,m (argumentAddr j i q)=(Endpoints.words (history h d π j.val).tiles (radix_pos h d)
      (history h d π j.val).encode i q:Word W))
    (ids : ∀q : Fin 3,saved ⟨q.val,by omega⟩=m (argumentAddr j i q)) :
    Model j i saved (preparedMemory j i m) (Record.writes (Record.prepare A (row h) S) n) := by
  let bl := fun side=>blockNumber hd j π (queryBlock j i π side)
  let r := queryRow j i π
  have bounds := region_room (h:=h) hd j.isLt.le
  have small (q : Fin 3) : argumentValue j (bl true) (bl false) r q<regionSize h d := by
    fin_cases q
    · exact (bl true).isLt.trans_le bounds.1
    · exact (bl false).isLt.trans_le bounds.1
    · exact (rowCode_lt r).trans_le bounds.2.2.1
  let code (q : Fin 3) : Fin (regionSize h d) := ⟨_,small q⟩
  have values : ∀ q,m (argumentAddr j i q)=((code q).val:Word W) :=
    ordinalIDs_of_words j i hd π m args
  have execution := dir_model j i hh code saved (fun q=>(ids q).trans (values q))
    (List.finRange 6) m n rel values
  change Model j i saved (Record.writes (Record.prepare A R S) m) _
  rw [Record.prepare_eq,Record.prepare_eq,physical_dirs,staged_dirs]
  simpa only [List.map_ofFn, ← List.ofFn_eq_map,Function.comp_def] using execution

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
