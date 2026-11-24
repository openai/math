import OAI.Computability.VPVNP.LiveHeaderPrepared
import OAI.Computability.VPVNP.LiveHeaderFieldSuffix
import OAI.Computability.VPVNP.LiveHeaderFieldFormats
import OAI.Computability.VPVNP.LiveHeaderUnique
import OAI.Computability.VPVNP.LiveHeaderResources

/-!
# Complete native recovery of the live group's headers

On compatible modes and canonically padded cuts, the one fixed template
has exactly one accepting path. The resulting external memory contains the
physical primed indices, advice, incident fields and dispatch words. The
cost estimate includes room for an enclosing native stage linker.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderWidths LiveHeaderDescriptors
open LiveHeader PrimedInputRAM ChainAssignments

variable {w d : ℕ}

theorem Prepared.sources {s : Sizes} {base : ℕ} {hw : 4 ≤ w} {advice : CutSchedule.Bits s.advice}
    {cuts : AllCuts s.h s.delta} {g : Fin (2^(s.h+1))} {tag : Mode.Tag} {m : Memory w}
    (ready : Prepared (d := d) s base hw advice cuts g tag m) : Fields.Sources s base d hw advice cuts g tag m := by
  refine ⟨ready.headers,?_,?_,ready.scalars (.flag .firstHalf),ready.scalars .firstTail⟩
  · intro side
    cases side with
    | left =>
      have hv := ready.scalars (.width .liveLeft) (Or.inr (Or.inl rfl))
      change (m (widthAddr base .liveLeft)).val = CutSchedule.width (s.h+1) s.delta g.val
      simpa only [Metadata.Field.address,index,Nat.add_sub_cancel] using hv
    | right => exact ready.scalars (.width .liveRight) (Or.inr (Or.inr rfl))
  · have htag := ready.scalars .mode
    change m (tagAddr base) = Fin.ofNat (2^w) tag.code.val at htag
    rw [htag,Fin.val_ofNat,Nat.mod_eq_of_lt]
    exact tag.code.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega : 2 ≤ w))

/-- Readback in the final memory. The intermediate memory records the initial
zero defaults used when a cut field is absent. -/
structure Output (s : Sizes) (base d : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : Mode.Tag) (m : Memory w) : Prop where
  sources : Fields.Sources s base d hw advice cuts g tag m
  scalars : ∀ f : Metadata.Field, Metadata.Correct s (g.val+1) tag f (m (f.address base))
  adviceWords : ∀ j : Fin s.advice, m (adviceBase s base+j.val) = encodeBit w (advice j)
  primedLeft : ∀ j < s.h+2, m (leftIndexBase s base+j) = encodeBit w ((2*(g.val+1)-1).testBit j)
  primedRight : ∀ j < s.h+2, m (rightIndexBase s base+j) = encodeBit w ((2*(g.val+1)).testBit j)
  fieldImage : ∃ before, (∀ a, exteriorBase s base .left ≤ a → before a = 0) ∧
    Fields.Image s base cuts g tag 8 before m

private theorem assembledOutput {s : Sizes} {base : ℕ} {hw : 4 ≤ w} {advice : CutSchedule.Bits s.advice}
    {cuts : AllCuts s.h s.delta} {g : Fin (2^(s.h+1))} {tag : Mode.Tag} {before m : Memory w}
    (ready : Prepared (d := d) s base hw advice cuts g tag before)
    (src : Fields.Sources s base d hw advice cuts g tag m) (img : Fields.Image s base cuts g tag 8 before m) :
    Output s base d hw advice cuts g tag m := by
  have frame (a : ℕ) (hb : a ≠ base) (ho : a ≠ offsetAddr base) (hc : a ≠ countAddr base)
      (h : a < adviceBase s base+s.advice) : m a = before a :=
    img.frame _ ⟨hb,ho,hc,fun side f hf => Or.inl (h.trans_le (dest_bounds s base side f hf).1)⟩
  have keep (a : ℕ) (h : base+14 < a) (hle : a < adviceBase s base+s.advice) : m a = before a :=
    frame _ (by omega) (by dsimp [offsetAddr]; omega) (by dsimp [countAddr]; omega) hle
  have hL : base+14 < leftIndexBase s base := by dsimp [leftIndexBase,populationAddr,highAddr,indexBase]; omega
  have hR : leftIndexBase s base+(s.h+2) = rightIndexBase s base := rfl
  have hA : rightIndexBase s base+(s.h+2) = adviceBase s base := rfl
  refine ⟨src,?_,?_,?_,?_,⟨before,ready.zero,img⟩⟩
  · intro f
    have hs : base < f.address base ∧ f.address base < offsetAddr base := by
      cases f with
      | width slot => cases slot <;> dsimp [Metadata.Field.address,widthAddr,offsetAddr] <;> omega
      | flag flag => cases flag <;> dsimp [Metadata.Field.address,flagAddr,offsetAddr] <;> omega
      | firstTail | mode => dsimp [Metadata.Field.address,tagAddr,firstTailAddr,offsetAddr]; omega
    rw [frame _ hs.1.ne' hs.2.ne (by dsimp [countAddr,offsetAddr] at *; omega)
      (by dsimp [offsetAddr] at hs; omega)]
    exact ready.scalars f
  · intro j
    rw [keep _ (by omega) (Nat.add_lt_add_left j.isLt _)]
    exact ready.adviceWords j
  · intro j hj
    rw [keep _ (by omega) (by omega)]
    exact ready.primedLeft j hj
  · intro j hj
    rw [keep _ (by omega) (by omega)]
    exact ready.primedRight j hj

/-- All 31 component stages run from the actual initialized processor
memory with empty choice strings. -/
theorem complete_stages (s : Sizes) (base : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : Mode.Tag)
    (bounds : Fields.Bounds s base d w) (indices : s.h+2 ≤ 2^d) (adv : s.advice ≤ 2^d)
    (hsel : physicalTag cuts g = some tag) (valid : ∀ side, Fields.ValidPadding s cuts g tag side) :
    let m := physicalMemory (d := d) hw advice cuts g
    ∃ xs out, StageRuns s base (some (⟨0,by decide⟩ : StageId)) m xs ∧
      (∀ x ∈ xs, x.Good s) ∧ finalMemory (Fin.ofNat _ base) m xs = out ∧
      Output s base d hw advice cuts g tag out := by
  obtain ⟨xs,mid,first,g₁,ready⟩ := prepared_prefix s base hw advice cuts g tag hsel indices adv
    bounds.scratch bounds.fit.le
  obtain ⟨ys,out,g₂,last,_,src,img⟩ := Fields.suffix_native bounds ready.sources valid
  have all := first.append last
  refine ⟨xs++ys,out,by simpa using all.finish (.done out),?_,all.finalMemory,assembledOutput ready src img⟩
  intro x hx
  exact (List.mem_append.mp hx).elim (g₁ x) (g₂ x)

private theorem flatten_replicates {α β : Type*} (n : α → ℕ) (v : β) (xs : List α) :
    (xs.map (fun x => List.replicate (n x) v)).flatten = List.replicate (xs.map n).sum v := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.flatten_cons,List.sum_cons,List.replicate_add,ih]

/-- The linked native interpreter has one accepting run, with precisely the
scheduled number of empty choices. Its output and cost are independent of
any external path oracle. -/
theorem valid_native (s : Sizes) (base cap : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : Mode.Tag)
    (bounds : Fields.Bounds s base d w) (indices : s.h+2 ≤ 2^d) (adv : s.advice ≤ 2^d)
    (tagFit : stages.length ≤ 2^w) (fuel : 107 ≤ cap)
    (hsel : physicalTag cuts g = some tag) (valid : ∀ side, Fields.ValidPadding s cuts g tag side) :
    let P := (program.instantiate w (publicData w s base)).program
    let m := physicalMemory (d := d) hw advice cuts g
    ∃ rs, runSegment P cap (some 0) m (List.replicate (callBound s) []) = some rs ∧
      endState (some 0) rs = none ∧ Output s base d hw advice cuts g tag (after m (eventLog rs)) ∧
      rs.length = callBound s ∧ RAMBuckets.cost Report.probes rs + 2*rs.length ≤ costBound s ∧
      (∀ x ∈ rs, x.probes ≤ 8) ∧
      ∀ bs other, runSegment P cap (some 0) m bs = some other → endState (some 0) other = none →
        bs = List.replicate (callBound s) [] ∧ other = rs := by
  let m := physicalMemory (d := d) hw advice cuts g
  obtain ⟨xs,out,full,good,hout,data⟩ := complete_stages s base hw advice cuts g tag bounds indices adv hsel valid
  have room (x : StageTrace w) (hx : x ∈ xs) : x.fuel + 2*stages.length+5 ≤ cap := by
    have h := (good x hx).1
    rw [stage_count]
    omega
  let addr : Word w := Fin.ofNat _ base
  let rs := xs.flatMap (fun x => x.output addr)
  have haddr : addr.val = base := by
    have h := bounds.fit
    rw [limit_eq] at h
    exact Nat.mod_eq_of_lt (by omega)
  have hz : m addr.val = 0 := by
    have h := bounds.scratch
    simp [m,physicalMemory,RAMMemory.initialMemory,haddr,show ¬base < 2^d by omega]
  have ids : xs.map (fun x => stage x.id) = stages := full.schedule
  have hpaths : xs.flatMap StageTrace.paths = List.replicate (callBound s) [] := by
    calc
      xs.flatMap StageTrace.paths = (xs.map (fun x => List.replicate (calls s (stage x.id)) [])).flatten := by
        rw [List.flatMap_def]
        exact congrArg List.flatten (List.map_congr_left (fun x hx => (good x hx).2.1))
      _ = List.replicate (xs.map (fun x => calls s (stage x.id))).sum [] := flatten_replicates _ _ _
      _ = List.replicate (callBound s) [] := by
        rw [← sum_calls,← ids,List.map_map,Function.comp_def]
  obtain ⟨hr,ha,hm,cost⟩ := run_of_stages s base cap tagFit full room (by rintro i ⟨⟩; exact hz)
  have len : rs.length = callBound s := by
    rw [calls_output,← sum_calls,← ids,List.map_map]
    exact congrArg List.sum (List.map_congr_left fun x hx => (good x hx).2.2.1)
  obtain ⟨_,budget⟩ := complete_budget s base full (fun x hx => (good x hx).2.2.1.le)
    (fun x hx => (good x hx).2.2.2)
  refine ⟨rs,hpaths ▸ hr,ha,hm ▸ hout ▸ data,len,?_,?_,?_⟩
  · rw [cost,calls_output]
    exact budget
  · intro y hy
    obtain ⟨x,hx,hy⟩ := List.mem_flatMap.mp hy
    obtain ⟨z,hz',rfl⟩ := List.mem_map.mp hy
    rw [LiveStageLink.linkedReport_probes]
    have h := ((good x hx).2.2.2 z hz').trans (probe_limit _)
    split <;> omega
  · intro bs other hbs hother
    obtain ⟨hb,he⟩ := BurstRAM.accepted_empty_unique (hpaths ▸ hr) ha hbs hother
    exact ⟨hb,he⟩

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
