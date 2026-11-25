import OAI.Hierarchy.ProbeStagePhysicalOrdinal

namespace OAI
/-! # Dependence of a genuine endpoint commit on the original CT allocation -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

private theorem update_agree {w : ℕ} {m n : Memory w} {P : ℕ→Prop}
    (agree : ∀ x,P x → m x=n x) (a : ℕ) (v : Word w) :
    ∀ x,P x → Function.update m a v x=Function.update n a v x := by
  intro x hx
  by_cases eqn : x=a
  · subst x
    simp
  · simpa only [Function.update_of_ne eqn] using agree x hx

private theorem fold_agree {w : ℕ} (ds : List (ScatterRefinement.Edit w)) {m n : Memory w}
    {P : ℕ→Prop} (equal : ∀ x,P x → m x=n x) :
    ∀ x,P x → ds.foldl ScatterRefinement.Edit.apply m x=ds.foldl ScatterRefinement.Edit.apply n x := by
  induction ds generalizing m n with
  | nil => exact equal
  | cons d ds ih =>
    apply ih
    intro x hx
    by_cases atWord : x=d.dst.val
    · subst x
      simp only [ScatterRefinement.Edit.apply,writeMemory,equal _ hx]
    · simp only [ScatterRefinement.Edit.apply,writeMemory,ite_eq_right atWord,equal _ hx]

private theorem source_image {w B ℓ : ℕ} (s : RankUpdate.Layout) (m : Memory w) (r : ℕ)
    (strings : MaskIndex B → Fin ℓ → Fin B) (c : Fin B) (width : ℕ)
    (place : MaskIndex B→ℕ→Word w) (frozen : ℕ→Prop)
    (input : Record.EndpointInput s m r strings c width place frozen) :
    RankUpdate.image s m =
      ((RankUpdate.edits strings c r s.quota).map (ScatterRefinement.event width place)).foldl
        ScatterRefinement.Edit.apply (RankUpdate.updates s m) := by
  let ps := RankUpdate.edits strings c r s.quota
  let ds := ps.map (ScatterRefinement.event width place)
  let dir := input.literal
  have cnt := RankUpdate.edits_length s m input.distinct r input.previous input.quotaFit input.rankFit
    strings c input.length
  have execution := ScatterRefinement.image_eq (RankUpdate.page w s) (RankUpdate.prepared s m)
    ds frozen dir.pointers (by simpa [ds,ps] using dir.slots)
    (fun i hi => by simpa [ds,ps] using dir.entry i (by simpa [ds,ps] using hi))
    (by
      intro e he
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
      exact dir.disjoint p hp)
  simpa only [RankUpdate.image,cnt,List.length_map,ds,ps,RankUpdate.prepared_eq s m input.distinct] using execution.1

variable {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d

include hd

/-- Both executions start with the real counter and the selected immutable
directory of the same endpoint. Every indirect clear is the same edit, even
when the list clears several bits from one packed word. -/
theorem endpoint_agree (l : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) (r : ℕ)
    (m n : Memory W) (sm : SideSource j i l b c r m) (sn : SideSource j i l b c r n)
    {P : ℕ→Prop} (agree : ∀x,P x→m x=n x) :
    ∀x,P x → RankUpdate.image (physicalSide j i l) m x=RankUpdate.image (physicalSide j i l) n x := by
  let s := physicalSide j i l
  have am := endpoint_input hd j i l b c r m sm
  have an := endpoint_input hd j i l b c r n sn
  have pointer : RankUpdate.counter s m=RankUpdate.counter s n := by
    simp only [RankUpdate.counter,s,sm.selected,sn.selected,sm.countPtr,sn.countPtr]
  have rank : m (RankUpdate.counter s m).val=n (RankUpdate.counter s n).val := Fin.ext (am.previous.trans an.previous.symm)
  have inc : RankUpdate.newCount s m=RankUpdate.newCount s n := congrArg (·+1) rank
  have which := c.isLt.trans_le (region_room hd j.isLt.le).2.1
  have dir : RankUpdate.dirWord s.heads s.chosen m=RankUpdate.dirWord s.heads s.chosen n := by
    change m ((region h d j.val 8:Word W)+m ((physicalSide j i l).chosen:Word W).val).val=
      n ((region h d j.val 8:Word W)+n ((physicalSide j i l).chosen:Word W).val).val
    rw [sm.selected,sn.selected,add_word (region_word j.isLt 8 which)]
    exact (occurrence_header hd j m sm.rom c).1.trans (occurrence_header hd j n sn.rom c).1.symm
  have len : RankUpdate.dirWord s.lengths s.chosen m=RankUpdate.dirWord s.lengths s.chosen n :=
    Fin.ext (am.length.trans an.length.symm)
  rw [source_image _ _ _ _ _ _ _ _ am,source_image _ _ _ _ _ _ _ _ an]
  apply fold_agree
  unfold RankUpdate.updates
  rw [inc,len,dir,rank,pointer]
  exact update_agree (update_agree (update_agree (update_agree (update_agree (update_agree agree _ _) _ _) _ _) _ _) _ _) _ _

end
end Hierarchy.ProbeStage.Native

end OAI
