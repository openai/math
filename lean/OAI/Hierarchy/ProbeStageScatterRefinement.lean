import OAI.Hierarchy.ProbeStageMaskUpdate
import OAI.Hierarchy.ProbeStagePackedMasks

namespace OAI
/-! # The native scatter preserves its descriptors and updates exactly the packed bits -/

namespace Hierarchy.ProbeStage.ScatterRefinement
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing

structure Edit (w : ℕ) where
  dst : Word w
  keep : Word w

def Edit.apply {w : ℕ} (m : Memory w) (d : Edit w) :=
  writeMemory m d.dst (BinaryOp.bitAnd.eval (m d.dst.val) d.keep)

def index {w : ℕ} (v : MaskUpdate.Parameters w) (m : Memory w) (i : ℕ) := m (v 1).val + (i:Word w)

def read {w : ℕ} (v : MaskUpdate.Parameters w) (m : Memory w) (i : ℕ) : Edit w :=
  let j := index v m i
  ⟨m (v 2).val+m (v 3+j).val, m (v 4+j).val⟩

theorem step_eq {w : ℕ} (v : MaskUpdate.Parameters w) (m : Memory w) (i : ℕ) :
    MaskUpdate.step v (i:Word w) m = (read v m i).apply m := rfl

/-- `fixed` contains the two scratch pointers and occurrence descriptor cells. The actual
contents are read once from the original memory and remain valid even if a word is hit twice. -/
theorem image_eq {w : ℕ} (v : MaskUpdate.Parameters w) (m : Memory w) (ds : List (Edit w))
    (fixed : ℕ → Prop) (pointers : fixed (v 1).val ∧ fixed (v 2).val)
    (slots : ∀ i < ds.length, fixed (v 3+index v m i).val ∧ fixed (v 4+index v m i).val)
    (reads : ∀ i (hi : i<ds.length), read v m i=ds[i]) (separate : ∀ d ∈ ds, ¬ fixed d.dst.val) :
    MaskUpdate.image v m ds.length = ds.foldl Edit.apply m ∧
    ∀ a, fixed a → MaskUpdate.image v m ds.length a=m a := by
  have inv (i : ℕ) (hi : i≤ds.length) :
      MaskUpdate.image v m i = (ds.take i).foldl Edit.apply m ∧
      ∀ a, fixed a → MaskUpdate.image v m i a=m a := by
    induction i with
    | zero => exact ⟨rfl,fun _ _=>rfl⟩
    | succ i ih =>
      have live : i<ds.length := by omega
      obtain ⟨fold,frame⟩ := ih live.le
      have j : index v (MaskUpdate.image v m i) i=index v m i := by
        simp only [index,frame _ pointers.1]
      have actual : read v (MaskUpdate.image v m i) i=ds[i] := by
        rw [← reads i live]
        simp only [read,j,frame _ pointers.2,frame _ (slots i live).1,frame _ (slots i live).2]
      rw [MaskUpdate.image,step_eq,actual,List.take_succ_eq_append_getElem live,List.foldl_append]
      refine ⟨by simp [fold],?_⟩
      intro x hx
      have ne : x≠ds[i].dst.val := fun e => separate _ (List.getElem_mem live) (e ▸ hx)
      simpa only [Edit.apply,writeMemory,ite_eq_right ne] using frame x hx
  simpa using inv ds.length le_rfl

def event {B ℓ w : ℕ} (width : ℕ) (place : MaskIndex B → ℕ → Word w) (p : PackedMask.Pos B ℓ) : Edit w :=
  ⟨place p.1 (p.2.val/width),(PackedMask.keep width (p.2.val%width):Word w)⟩

theorem keep_lt {width off : ℕ} (ho : off<width) : PackedMask.keep width off < 2^width := by
  by_contra! h
  obtain ⟨i,le_,ht⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow h
  simp only [PackedMask.keep_test ho,decide_eq_true_eq] at ht
  omega

theorem fold_word {B ℓ w : ℕ} (width : ℕ) (positive : 0<width) (fits : width≤w)
    (place : MaskIndex B → ℕ → Word w) (r : MaskIndex B) (chunk : ℕ) (L : List (PackedMask.Pos B ℓ))
    (space : ∀ p ∈ L, place p.1 (p.2.val/width)=place r chunk ↔ p.1=r ∧ p.2.val/width=chunk)
    (m : Memory w) :
    (((L.map (event width place)).foldl Edit.apply m) (place r chunk).val).val =
      L.foldl (PackedMask.scatterBit width r chunk) (m (place r chunk).val).val := by
  induction L generalizing m with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [ih (fun q hq=>space q (by simp [hq]))]
    congr 1
    have q := space p (by simp)
    by_cases h : p.1=r ∧ p.2.val/width=chunk
    · have eqn := q.mpr h
      have small := (keep_lt (Nat.mod_lt p.2.val positive)).trans_le (Nat.pow_le_pow_right (by decide) fits)
      simp only [event,Edit.apply,writeMemory,eqn,ite_true,BinaryOp.eval,Fin.val_ofNat,
        Fin.val_cast_of_lt small,Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ small),PackedMask.scatterBit,ite_eq_left h]
    · have ne : (place r chunk).val ≠ (place p.1 (p.2.val/width)).val := fun e => h (q.mp (Fin.ext e.symm))
      simp [event,Edit.apply,writeMemory,ne,PackedMask.scatterBit,h]

/-- The reflected physical memory contains the complement of the updated forbidden-color set. -/
theorem row_after {B ℓ w : ℕ} (v : MaskUpdate.Parameters w) (m : Memory w) (width : ℕ)
    (positive : 0<width) (fits : width≤w) (place : MaskIndex B → ℕ → Word w)
    (strings : MaskIndex B → Fin ℓ → Fin B) (full : Finset (Fin B)) (color : Fin B)
    (r : MaskIndex B) (chunk : ℕ) (initial : (m (place r chunk).val).val=PackedMask.word (strings r) full width chunk)
    (space : ∀ p ∈ PackedMask.occurrences strings color,
      place p.1 (p.2.val/width)=place r chunk ↔ p.1=r ∧ p.2.val/width=chunk)
    (fixed : ℕ → Prop) (pointers : fixed (v 1).val ∧ fixed (v 2).val)
    (slots : ∀ i < (PackedMask.occurrences strings color).length, fixed (v 3+index v m i).val ∧ fixed (v 4+index v m i).val)
    (reads : ∀ i (hi : i < (PackedMask.occurrences strings color).length),
      read v m i=event width place (PackedMask.occurrences strings color)[i])
    (apart : ∀ p ∈ PackedMask.occurrences strings color, ¬ fixed (place p.1 (p.2.val/width)).val) :
    (MaskUpdate.image v m (PackedMask.occurrences strings color).length (place r chunk).val).val =
      PackedMask.word (strings r) (insert color full) width chunk := by
  let L := PackedMask.occurrences strings color
  have move := image_eq v m (L.map (event width place)) fixed pointers (by simpa using slots)
    (fun i hi => by simpa [L] using reads i (by simpa using hi)) (by
      intro e he
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
      exact apart p hp)
  rw [List.length_map] at move
  rw [move.1,fold_word _ positive fits _ _ _ _ space,initial,PackedMask.scatter_saturation _ positive]

end Hierarchy.ProbeStage.ScatterRefinement

end OAI
