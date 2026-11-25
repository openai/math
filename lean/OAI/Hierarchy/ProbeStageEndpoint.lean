import OAI.Hierarchy.ProbeStageRankRefinement

namespace OAI
/-! # The observable physical counter, rank and masks after an endpoint update -/

namespace Hierarchy.ProbeStage.RankUpdate
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

/-- The list at an endpoint's directory is visited only on the record that reaches its quota. -/
noncomputable def edits {B ℓ : ℕ} (str : MaskIndex B → Fin ℓ → Fin B) (c : Fin B) (r q : ℕ) :=
  if r+1=q then PackedMask.occurrences str c else []

theorem edits_length {B ℓ w : ℕ} (s : Layout) (m : Memory w) (sep : Distinct s m)
    (r : ℕ) (rank : (m (counter s m).val).val=r) (quotaFit : s.quota<2^w) (rankFit : r+1<2^w)
    (strings : MaskIndex B → Fin ℓ → Fin B) (c : Fin B)
    (length : (dirWord s.lengths s.chosen m).val=(PackedMask.occurrences strings c).length) :
    occurrenceCount s m=(edits strings c r s.quota).length := by
  rw [occurrenceCount_spec s m sep r rank quotaFit rankFit,length]
  by_cases h : r+1=s.quota <;> simp [edits,h]

theorem prepared_rank {w : ℕ} (s : Layout) (m : Memory w) (sep : Distinct s m) :
    prepared s m s.rank=m (counter s m).val ∧ prepared s m (counter s m).val=newCount s m := by
  have nd := sep.nodup
  simp only [touched,List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,
    List.nodup_nil,and_true] at nd
  rw [prepared_eq _ _ sep]
  simp_all (config:={contextual:=true}) only [updates,Function.update_self,Function.update_of_ne,ne_eq,not_false_eq_true,true_and]

theorem prepared_head {w : ℕ} (s : Layout) (m : Memory w) (sep : Distinct s m) :
    prepared s m s.head=dirWord s.heads s.chosen m := by
  have nd := sep.nodup
  simp only [touched,List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,
    List.nodup_nil,and_true] at nd
  rw [prepared_eq _ _ sep]
  simp_all (config:={contextual:=true}) only [updates,Function.update_self,Function.update_of_ne,ne_eq,not_false_eq_true]

/-- This contains just the *input read and write addresses* for the native descriptor table.
In particular `frozen` can be the full complement of the chosen block's writable mask bank. -/
structure Directory {w B ℓ : ℕ} (s : Layout) (m : Memory w) (ps : List (PackedMask.Pos B ℓ))
    (width : ℕ) (place : MaskIndex B → ℕ → Word w) (frozen : ℕ → Prop) : Prop where
  pointers : frozen ((page w s) 1).val ∧ frozen ((page w s) 2).val
  slots : ∀ i<ps.length,
    frozen ((page w s) 3+ScatterRefinement.index (page w s) (prepared s m) i).val ∧
    frozen ((page w s) 4+ScatterRefinement.index (page w s) (prepared s m) i).val
  entry : ∀ i (hi : i<ps.length), ScatterRefinement.read (page w s) (prepared s m) i=
    ScatterRefinement.event width place ps[i]
  disjoint : ∀ p∈ps, ¬frozen (place p.1 (p.2.val/width)).val

theorem directory_frame {w B ℓ : ℕ} (s : Layout) (m : Memory w) (ps : List (PackedMask.Pos B ℓ))
    (width : ℕ) (place : MaskIndex B → ℕ → Word w) (frozen : ℕ → Prop)
    (valid : Directory s m ps width place frozen) (count : occurrenceCount s m=ps.length) :
    ∀ x, frozen x → image s m x=prepared s m x := by
  let L := ps.map (ScatterRefinement.event width place)
  have done := ScatterRefinement.image_eq (page w s) (prepared s m) L frozen valid.pointers
    (by simpa [L] using valid.slots) (fun i hi=> by simpa [L] using valid.entry i (by simpa [L] using hi))
    (by
      intro e he
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
      exact valid.disjoint p hp)
  simp only [L,List.length_map] at done
  simpa only [image,count] using done.2

theorem committed {w B ℓ : ℕ} (s : Layout) (m : Memory w) (sep : Distinct s m) (r : ℕ)
    (rank : (m (counter s m).val).val=r) (quotaFit : s.quota<2^w) (rankFit : r+1<2^w)
    (strings : MaskIndex B → Fin ℓ → Fin B) (c : Fin B)
    (length : (dirWord s.lengths s.chosen m).val=(PackedMask.occurrences strings c).length)
    (width : ℕ) (place : MaskIndex B → ℕ → Word w) (frozen : ℕ → Prop)
    (valid : Directory s m (edits strings c r s.quota) width place frozen)
    (rankAddr : frozen s.rank) (counterAddr : frozen (counter s m).val) :
    (image s m s.rank).val=r ∧ (image s m (counter s m).val).val=r+1 ∧
    occurrenceCount s m=(edits strings c r s.quota).length ∧
    ∀ x, frozen x → x∉touched s m → image s m x=m x := by
  have cnt := edits_length s m sep r rank quotaFit rankFit strings c length
  have fr := directory_frame s m _ width place frozen valid cnt
  have inc : (newCount s m).val =r+1 := by
    have original : m (counter s m).val=(r:Word w) := Fin.ext (by rw [Fin.val_cast_of_lt (by omega : r<2^w)];exact rank)
    simp only [newCount,original,←Nat.cast_one (R:=Word w),←Nat.cast_add,Fin.val_cast_of_lt rankFit]
  refine ⟨by rw [fr _ rankAddr,(prepared_rank _ _ sep).1,rank],
    by rw [fr _ counterAddr,(prepared_rank _ _ sep).2,inc],cnt,?_⟩
  exact fun x hx hn => (fr x hx).trans (updates_elsewhere s m sep x hn)

theorem mask_after {w B ℓ : ℕ} (s : Layout) (m : Memory w) (r : ℕ)
    (strings : MaskIndex B → Fin ℓ → Fin B) (c : Fin B) (full : Finset (Fin B))
    (width : ℕ) (pos : 0<width) (fits : width≤w) (place : MaskIndex B → ℕ → Word w) (frozen : ℕ → Prop)
    (valid : Directory s m (edits strings c r s.quota) width place frozen)
    (cnt : occurrenceCount s m=(edits strings c r s.quota).length)
    (idx : MaskIndex B) (chunk : ℕ)
    (original : (prepared s m (place idx chunk).val).val=PackedMask.word (strings idx) full width chunk)
    (apart : ∀ p ∈ PackedMask.occurrences strings c,
      place p.1 (p.2.val/width)=place idx chunk ↔ p.1=idx ∧ p.2.val/width=chunk) :
    (image s m (place idx chunk).val).val =
      PackedMask.word (strings idx) (if r+1=s.quota then insert c full else full) width chunk := by
  by_cases sat : r+1=s.quota
  · simp only [edits,ite_eq_left sat] at valid cnt ⊢
    rw [image,cnt]
    exact ScatterRefinement.row_after _ _ width pos fits place strings full c idx chunk original apart frozen
      valid.pointers valid.slots valid.entry valid.disjoint
  · simpa [image,cnt,edits,sat,MaskUpdate.image] using original

end Hierarchy.ProbeStage.RankUpdate

end OAI
