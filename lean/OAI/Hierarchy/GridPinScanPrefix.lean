import OAI.Hierarchy.GridPinPrefixMemory
import OAI.Hierarchy.GridPinOrdinalRows
import OAI.Hierarchy.FactorPinClassOrder
import OAI.Hierarchy.FactorBucketSlots

namespace OAI
/-! # Published physical factor and bucket prefixes in the original input tape -/

namespace Hierarchy.GridPinPrefixMemory

open FactorPinIntervals
open FactorAllocation

variable {S N d T L : ℕ}

def factorKey (w : ℕ) (cost : Fin N → Fin d → ℕ) (f : Fin N) :=
  (finFunctionFinEquiv (key w cost f)).val

theorem byClass_eq_stream (w : ℕ) (cost : Fin N → Fin d → ℕ) :
    byClass (factorKey w cost) ((20*(w+1)+2)^d) = classStream w cost := by
  unfold byClass classStream
  rw [←range_from_fin ((20*(w+1)+2)^d),List.flatMap_map]
  apply congrArg (fun g => (List.finRange ((20*(w+1)+2)^d)).flatMap g)
  funext c
  apply List.filter_congr
  intro f _
  have iffTag : factorKey w cost f=c.val ↔ key w cost f=finFunctionFinEquiv.symm c :=
    ⟨fun h=>finFunctionFinEquiv.injective ((Fin.ext h).trans (Equiv.apply_symm_apply _ _).symm),
     fun h=>congrArg Fin.val ((congrArg finFunctionFinEquiv h).trans (Equiv.apply_symm_apply _ _))⟩
  have eqn : decide (factorKey w cost f=c.val)=decide (key w cost f=finFunctionFinEquiv.symm c) := by
    by_cases h : factorKey w cost f=c.val
    · simp [h,iffTag.mp h]
    · have other : key w cost f ≠ finFunctionFinEquiv.symm c := fun same=>h (iffTag.mpr same)
      simp [h,other]
  simpa only [Function.comp_apply,keyItems,group] using eqn

/-- The literal physical class loop enumerates the original occurrence stream. -/
theorem factor_ordinals (w : ℕ) (cost : Fin N → Fin d → ℕ) :
    (List.range (((20*(w+1)+2)^d)*N)).filterMap (classRow (factorKey w cost)) =
      classStream w cost := (class_rows ..).trans (byClass_eq_stream w cost)

private theorem cast_sum_map {A Row : Type*} [AddMonoidWithOne A] (rows : List Row) (size : Row → ℕ) :
    (rows.map (fun r => (size r : A))).sum = ((rows.map size).sum : ℕ) := by
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def]

variable {A : Type*} [AddMonoidWithOne A]

/-- At a selected factor, the emitted word is the tick's incoming header cursor
plus the sizes of precisely the preceding factors at that tick. -/
theorem factor_prefix (ht : 0<T) (w : ℕ) (cost : Fin N → Fin d → ℕ) (origin : Fin S → Fin N)
    (cur : Fin T→ℕ) (dst : Fin N→ℕ) (mem : ℕ→ℕ→A)
    (unique : Function.Injective cur) (ids : Function.Injective dst) (sep : ∀ t i, cur t≠dst i)
    (step : ∀ i<((20*(w+1)+2)^d)*N, mem (i+1)=(classRow (factorKey w cost) i).elim (mem i)
      (store (owner ht w cost) (fun f => ((intervalBits origin f).length:A)) cur dst (mem i)))
    (f : Fin N) (before after : List (Fin N))
    (index : factors w cost (List.finRange N) (owner ht w cost f)=before++f::after) :
    mem (((20*(w+1)+2)^d)*N) (dst f) =
      mem 0 (cur (owner ht w cost f)) + ((stream origin before).length : A) := by
  rw [iter_selected _ _ _ _ _ _ _ step,factor_ordinals]
  have nd := byClass_nodup (factorKey w cost) ((20*(w+1)+2)^d)
  rw [byClass_eq_stream] at nd
  rw [record_after_owner_split _ _ _ _ _ _ _ before after nd unique ids sep
    ((classStream_at ht w cost _).trans index),cast_sum_map]
  simp [stream,List.length_flatMap]

theorem nonempty_buckets (S span : ℕ) (pos : 0< span) (b : Fin ((S+span-1)/span)) :
    b.val*span<S := by
  have cut := (Nat.lt_div_iff_mul_lt pos).mp b.isLt
  omega

/-- Each original nonempty input bucket is represented by its first bit. The
sorted descriptors therefore agree with filtering the physical bucket order. -/
theorem lane_selection {span : ℕ} (pos : 0< span) (origin : Fin S → Fin N)
    (bucket : Fin S→Fin L) (quotient : ∀ j, (bucket j).val=j.val/span)
    (nonempty : ∀ b : Fin L, b.val*span<S) (laneOwner : Fin L→Fin N)
    (owners : ∀ j, laneOwner (bucket j)=origin j)
    (f : Fin N) (desc : List (Fin L)) (ordered : desc.Pairwise (· < ·))
    (admits : ∀ j,bucket j∈desc ↔ origin j=f) :
    (List.finRange L).filter (fun b => decide (laneOwner b=f))=desc := by
  have member (b : Fin L) : b∈desc ↔ laneOwner b=f := by
    let j : Fin S := ⟨b.val*span,nonempty b⟩
    have assigned : bucket j=b := Fin.ext ((quotient j).trans (Nat.mul_div_cancel _ pos))
    simpa only [← owners j, assigned] using admits j
  apply List.Subset.antisymm_of_pairwise ((List.pairwise_lt_finRange L).filter _) ordered
  · intro b h
    exact (member b).mpr (of_decide_eq_true (List.mem_filter.mp h).2)
  · intro b h
    exact List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true ((member b).mp h)⟩

/-- The bucket cursor is initialized to its owner's published factor base.
Each preceding bucket at that same factor contributes its clipped physical width. -/
theorem bucket_prefix {span : ℕ} (pos : 0< span) (origin : Fin S → Fin N)
    (bucket : Fin S→Fin L) (quotient : ∀ j, (bucket j).val=j.val/span)
    (nonempty : ∀ b : Fin L, b.val*span<S) (laneOwner : Fin L→Fin N)
    (owners : ∀ j, laneOwner (bucket j)=origin j)
    (cur : Fin N→ℕ) (dst : Fin L→ℕ) (mem : ℕ→ℕ→A)
    (unique : Function.Injective cur) (ids : Function.Injective dst) (sep : ∀ f b, cur f≠dst b)
    (step : ∀ i<L, mem (i+1)=(bucketRow L i).elim (mem i)
      (store laneOwner (fun b => (bucketLength S span b.val : A)) cur dst (mem i)))
    (b : Fin L) (desc before after : List (Fin L)) (ordered : desc.Pairwise (· < ·))
    (admits : ∀ j, bucket j∈desc ↔ origin j=laneOwner b)
    (index : desc=before++b::after) :
    mem L (dst b) = mem 0 (cur (laneOwner b)) +
      (((before.map (fun i => bucketLength S span i.val)).sum : ℕ) : A) := by
  rw [iter_selected _ _ _ _ _ _ _ step,bucket_rows]
  rw [record_after_owner_split _ _ _ _ _ _ _ before after (List.nodup_finRange _) unique ids sep
    ((lane_selection pos origin bucket quotient nonempty laneOwner owners (laneOwner b) desc ordered admits).trans index)]
  rw [cast_sum_map]

/-- The native loop stops after its last active bucket. All later physical
archive ordinals have different output addresses, so appending them as a
mathematical fold does not change an already published base. -/
theorem bucket_prefix_truncated {full span : ℕ} (active : L≤full)
    (laneOwner : Fin full→Fin N) (cur : Fin N→ℕ) (dst : Fin full→ℕ) (mem : ℕ→ℕ→A)
    (unique : Function.Injective cur) (ids : Function.Injective dst) (sep : ∀ f b, cur f≠dst b)
    (step : ∀ i<L, mem (i+1)=(bucketRow full i).elim (mem i)
      (store laneOwner (fun b => (bucketLength S span b.val : A)) cur dst (mem i)))
    (b : Fin full) (visited : b.val<L) (desc before after : List (Fin full))
    (ordered : desc.Pairwise (· < ·)) (fiber : ∀ s, s∈desc ↔ laneOwner s=laneOwner b)
    (index : desc=before++b::after) :
    mem L (dst b) = mem 0 (cur (laneOwner b)) +
      (((before.map (fun i => bucketLength S span i.val)).sum : ℕ) : A) := by
  let cost : Fin full → A := fun f => (bucketLength S span f.val : A)
  let later := ((List.range (full-L)).map (L+·)).filterMap (bucketRow full)
  have allRows : List.finRange full=(List.range L).filterMap (bucketRow full)++later := by
    rw [←bucket_rows full]
    have splitN : List.range full=List.range L++(List.range (full-L)).map (L+·) := by
      simpa only [Nat.add_sub_of_le active] using (List.range_add (n:=L) (m:=full-L))
    rw [splitN,List.filterMap_append]
  have keep : run laneOwner cost cur dst (mem L) later (dst b)=mem L (dst b) := by
    apply unchanged
    intro s hs
    obtain ⟨k,hk,hit⟩ := List.mem_filterMap.mp hs
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hk
    have hv : L+u=s.val := by
      dsimp only [bucketRow] at hit
      split at hit
      · exact congrArg Fin.val (Option.some.inj hit)
      · contradiction
    exact ⟨fun eqn => by have h := congrArg Fin.val (ids eqn); omega,(sep _ _).symm⟩
  have first := iter_selected laneOwner cost cur dst mem (bucketRow full) L step
  have frame : run laneOwner cost cur dst (mem 0) (List.finRange full) (dst b)=mem L (dst b) := by
    rw [allRows]
    unfold run
    rw [List.foldl_append]
    change run _ _ _ _ (run laneOwner cost cur dst (mem 0) _) later (dst b)=_
    rw [←first]
    exact keep
  have sel : (List.finRange full).filter (fun s=>decide (laneOwner s=laneOwner b))=desc := by
    apply List.Subset.antisymm_of_pairwise ((List.pairwise_lt_finRange full).filter _) ordered
    · intro s h
      exact (fiber s).mpr (of_decide_eq_true (List.mem_filter.mp h).2)
    · intro s h
      exact List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true ((fiber s).mp h)⟩
  rw [←frame,record_after_owner_split _ _ _ _ _ _ _ before after
    (List.nodup_finRange full) unique ids sep (sel.trans index)]
  exact congrArg (mem 0 (cur (laneOwner b)) + ·) (cast_sum_map before _)


end Hierarchy.GridPinPrefixMemory

end OAI
