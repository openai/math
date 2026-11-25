import OAI.Computability.BorderVNP.CellPacketGeometryRanges

/-! # Public marker and data rows in a power-of-two geometry rectangle

The start and end markers have fixed addresses, independently of the owners of
the intervening sparse rows. Padding receives a distinct key. The exact source
filter between a cell's markers contains precisely its live payload words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.Markers

open PackedHistogram ParseBatchSort
open private key_stable from OAI.Computability.BorderVNP.CellPacketGeometryRanges

/-- Source rows before the key/ordinal Batcher sort. -/
inductive Row (C N : ℕ) where
  | start (cell : Fin C)
  | data (word : Fin N)
  | stop (cell : Fin C)
  | pad

/-- The order is all left markers, all public payload words in ordinal order,
all right markers, and the remaining holes of the power-of-two rectangle. -/
def row (C N i : ℕ) : Row C N :=
  if h₁ : i < C then .start ⟨i,h₁⟩
  else if h₂ : i-C < N then .data ⟨i-C,h₂⟩
  else if h₃ : i-(C+N) < C then .stop ⟨i-(C+N),h₃⟩ else .pad

/-- Marker keys are fixed, data keys come from the current public site locations,
and padding belongs to the spare bucket just above the real cells. -/
def key {C N : ℕ} (owner : Fin N → Fin C) : Row C N → ℕ
  | .start c | .stop c => c.val
  | .data j => (owner j).val
  | .pad => C

/-- Only data rows contribute public payload. The marker values themselves are
skipped by the native section-address calculation. -/
def word {C N : ℕ} (data : Fin N → ℕ) : Row C N → ℕ
  | .data j => data j
  | _ => 0

variable {C N b : ℕ} (fit : C+N+C ≤ 2^b)

/-- Hardwired source ordinal of the cell's left marker. -/
def start (c : Fin C) : Fin (2^b) := ⟨c.val,by have := c.isLt; omega⟩

/-- Hardwired source ordinal of the cell's right marker. -/
def stop (c : Fin C) : Fin (2^b) := ⟨C+N+c.val,by have := c.isLt; omega⟩

/-- Source ordinal of a physical payload word, independent of its cell. -/
def dataRow (j : Fin N) : Fin (2^b) := ⟨C+j.val,by have := j.isLt; omega⟩

@[simp] theorem row_start (c : Fin C) : row C N (start fit c).val = .start c := by simp [start,row,c.isLt]

@[simp] theorem row_stop (c : Fin C) : row C N (stop fit c).val = .stop c := by
  simp [stop,row,Nat.not_lt.mpr (by omega : C ≤ C+N+c.val),
    Nat.not_lt.mpr (by omega : N ≤ C+N+c.val-C),c.isLt]

@[simp] theorem row_data (j : Fin N) : row C N (dataRow fit j).val = .data j := by
  simp [dataRow,row,Nat.not_lt.mpr (Nat.le_add_right _ _),j.isLt]

/-- The compact source list for a cell, before translating any payload values. -/
theorem inside_rows (owner : Fin N → Fin C) (c : Fin C) :
    inside (fun i => key owner (row C N i.val)) (start fit c) (stop fit c) =
      ((List.finRange N).filter fun j => decide (owner j = c)).map (dataRow fit) := by
  let src := inside (fun i : Fin (2^b) => key owner (row C N i.val)) (start fit c) (stop fit c)
  let inCell := (List.finRange N).filter fun j => decide (owner j = c)
  have inj : Function.Injective (dataRow fit) := fun a z hz => Fin.ext (by
    have h := congrArg Fin.val hz; simp only [dataRow,Nat.add_right_inj] at h; exact h)
  have sortedFin (n : ℕ) : (List.finRange n).Pairwise (· ≤ ·) :=
    List.ofFn_id n ▸ (monotone_id : Monotone (id : Fin n → Fin n)).sortedLE_ofFn.pairwise
  have hpair : (inCell.map (dataRow fit)).Pairwise (· ≤ ·) := by
    apply List.Pairwise.map
    · intro i j hij
      exact Nat.add_le_add_left hij _
    · exact (sortedFin N).filter _
  have mem (i : Fin (2^b)) : i ∈ src ↔ i ∈ inCell.map (dataRow fit) := by
    simp only [src,inside,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,row_start,key,
      inCell,List.mem_map]
    constructor
    · rintro ⟨hkey,hl,hr⟩
      change c.val < i.val at hl
      change i.val < C+N+c.val at hr
      by_cases a : i.val < C
      · simp [row,a] at hkey; omega
      · by_cases z : i.val-C < N
        · let j : Fin N := ⟨i.val-C,z⟩
          have eqn : owner j = c := Fin.ext (by simpa [row,a,z,j] using hkey)
          exact ⟨j,eqn,Fin.ext (by change C+(i.val-C) = i.val; omega)⟩
        · have stopBound : i.val-(C+N) < C := by have := c.isLt; omega
          simp [row,a,z,stopBound] at hkey
          omega
    · rintro ⟨j,hj,rfl⟩
      simp only [row_data,Fin.val_inj]
      exact ⟨hj,by change c.val < C+j.val; have := c.isLt; omega,
        by change C+j.val < C+N+c.val; have := j.isLt; omega⟩
  have hp := (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _)
    (((List.nodup_finRange _).filter _).map inj)).mpr mem
  exact hp.eq_of_pairwise' ((sortedFin _).filter _) hpair

/-- Payloads inside the physical cell markers have exactly the filtered order of
the original sparse words. No reserved word of an unrelated cell is included. -/
theorem inside_words (owner : Fin N → Fin C) (data : Fin N → ℕ) (c : Fin C) :
    (inside (fun i => key owner (row C N i.val)) (start fit c) (stop fit c)).map
      (fun i => word data (row C N i.val)) =
    ((List.finRange N).filter fun j => decide (owner j = c)).map data := by
  rw [inside_rows, List.map_map]
  simp only [Function.comp_def,row_data,word]

/-- The real returned rank of a payload word is the start marker's rank plus one
and the word's ordinal among the cell's source rows. -/
theorem rank_payload (owner : Fin N → Fin C) (c : Fin C) (π : Equiv.Perm (Fin (2^b)))
    (ordered : Monotone fun i => 2*key owner (row C N (π i).val)*2^b+(π i).val)
    (j : Fin ((List.finRange N).filter (fun t => decide (owner t = c))).length) :
    (π.symm (dataRow fit (((List.finRange N).filter fun t => decide (owner t = c))[j.val]))).val =
      (π.symm (start fit c)).val+1+j.val := by
  let lo := start fit c
  let hi := stop fit c
  let keys := fun i : Fin (2^b) => key owner (row C N i.val)
  have equal : keys lo = keys hi := by simp [keys,lo,hi,key]
  have hs := (inside_sorted keys π ordered lo hi equal).trans (inside_rows fit owner c)
  have hcount := congrArg List.length hs
  simp only [List.length_ofFn,List.length_map] at hcount
  let pos : Fin ((π.symm hi).val-(π.symm lo).val-1) := ⟨j.val,hcount.symm ▸ j.isLt⟩
  have h := congrArg (fun xs : List (Fin (2^b)) => xs[j.val]?) hs
  simp only [List.getElem?_ofFn,List.getElem?_map,List.getElem?_eq_getElem j.isLt, Option.map_some] at h
  rw [dite_eq_left pos.isLt] at h
  have he := Option.some.inj h
  have hp := congrArg (fun v => (π.symm v).val) he.symm
  simpa [innerIndex,lo] using hp

/-- The returned position of a specified source word is the cell base plus the
number of preceding source words with the same cell key. -/
theorem rank_prefix (owner : Fin N → Fin C) (c : Fin C) (π : Equiv.Perm (Fin (2^b)))
    (ordered : Monotone fun i => 2*key owner (row C N (π i).val)*2^b+(π i).val)
    (i : Fin N) (belongs : owner i = c) :
    (π.symm (dataRow fit i)).val = (π.symm (start fit c)).val+1+
      (((List.finRange N).take i.val).filter fun t => decide (owner t = c)).length := by
  let xs := List.finRange N
  let f := fun t => decide (owner t = c)
  have h : xs.take i.val ++ i :: xs.drop (i.val+1) = xs := by
    have fit' : i.val < xs.length := by simp [xs]
    have eqn : xs[i.val] = i := by simp [xs]
    have split := List.drop_eq_getElem_cons fit'
    rw [eqn] at split
    rw [← split, List.take_append_drop]
  have split : (xs.take i.val).filter f ++ i :: (xs.drop (i.val+1)).filter f = xs.filter f := by
    simpa only [List.filter_append,List.filter_cons,show f i = true by simp [f,belongs],ite_true] using
      congrArg (List.filter f) h
  let n := ((xs.take i.val).filter f).length
  have bound : n < (xs.filter f).length := by rw [←split]; simp [n]
  have value : (xs.filter f)[n] = i := by
    have atN := congrArg (fun ls : List (Fin N) => ls[n]?) split
    rw [List.getElem?_eq_getElem bound] at atN
    simpa [n,List.getElem?_append_right] using atN.symm
  have pos := rank_payload fit owner c π ordered ⟨n,bound⟩
  change (π.symm (dataRow fit (xs.filter f)[n])).val = (π.symm (start fit c)).val+1+n at pos
  rwa [value] at pos

/-- The end marker follows the start marker even when a cell has no payload.
Consequently the exclusive end address is exactly the returned stop address. -/
theorem start_lt_stop (owner : Fin N → Fin C) (c : Fin C) (π : Equiv.Perm (Fin (2^b)))
    (ordered : Monotone fun i => 2*key owner (row C N (π i).val)*2^b+(π i).val) :
    π.symm (start fit c) < π.symm (stop fit c) := by
  apply (key_stable (fun i => key owner (row C N i.val)) π ordered (by simp [key])).mpr
  simp only [Equiv.apply_symm_apply]
  change c.val < C+N+c.val
  have := c.isLt
  omega

end CellPacketGeometry.Markers

end BorderVNP
end Computability
end OAI
