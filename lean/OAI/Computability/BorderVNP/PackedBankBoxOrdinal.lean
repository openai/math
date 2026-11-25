import OAI.Computability.BorderVNP.PackedStableOffsets
import OAI.Computability.BorderVNP.PackedLookup

/-! # Stable box numbers inside a merged cell

A site contributes its one-copy box list once, independently of the number of
invocations. A stable same-owner scan of these list lengths gives the site's
first box number in the cell packet. Both inherited lists and empty sites use
the same allocation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankBoxOrdinal

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open scoped BigOperators

variable {s k w : ℕ} {α : Type*}

private def entries (owner : Fin s → ℕ) (boxes : Fin s → List α) (cell : ℕ) :=
  List.ofFn fun i => if owner i = cell then boxes i else []

/-- One cell's merged box table in increasing public site-row order. -/
def table (owner : Fin s → ℕ) (boxes : Fin s → List α) (cell : ℕ) : List α :=
  (entries owner boxes cell).flatten

/-- The first merged ordinal reserved for a site. -/
def base (owner count : Fin s → ℕ) (v : Fin s) : ℕ :=
  ∑ i, if owner i = owner v ∧ i < v then count i else 0

/-- The stable table is the concatenation of the sites owned by this cell. -/
theorem table_eq_filtered (owner : Fin s → ℕ) (boxes : Fin s → List α) (cell : ℕ) :
    table owner boxes cell = ((List.finRange s).filter fun i => owner i = cell).flatMap boxes := by
  unfold table entries
  rw [List.ofFn_eq_map]
  generalize List.finRange s = xs
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    by_cases he : owner i = cell <;> simp [he,ih]

/-- The directory's public count includes all local list entries, even unused ones. -/
theorem table_length (owner : Fin s → ℕ) (boxes : Fin s → List α) (cell : ℕ) :
    (table owner boxes cell).length = ∑ i, if owner i = cell then (boxes i).length else 0 := by
  simp only [table,entries,List.length_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  apply Finset.sum_congr rfl
  intro i _
  split <;> rfl

private theorem before_length (owner : Fin s → ℕ) (boxes : Fin s → List α) (v : Fin s) :
    ((entries owner boxes (owner v)).take v.val).flatten.length =
      base owner (fun i => (boxes i).length) v := by
  rw [entries,List.length_flatten,List.map_take,List.map_ofFn,List.sum_take_ofFn,Finset.sum_filter,base]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i < v <;> by_cases he : owner i = owner v <;> simp [h,he]

private theorem split_table (owner : Fin s → ℕ) (boxes : Fin s → List α) (v : Fin s) :
    let rows := entries owner boxes (owner v)
    table owner boxes (owner v) = (rows.take v.val).flatten ++
      (boxes v ++ (rows.drop (v.val+1)).flatten) := by
  intro rows
  have h : v.val < rows.length := by simp [rows,entries]
  have hv : rows[v.val] = boxes v := by simp [rows,entries]
  rw [← hv,← List.flatten_cons,← List.drop_eq_getElem_cons h,← List.flatten_append,List.take_append_drop]
  rfl

/-- Every local ordinal, relocated by the site prefix, lies in the merged table. -/
theorem index_lt (owner : Fin s → ℕ) (boxes : Fin s → List α) (v : Fin s) (j : Fin (boxes v).length) :
    base owner (fun i => (boxes i).length) v + j.val < (table owner boxes (owner v)).length := by
  rw [split_table,List.length_append,List.length_append,← before_length]
  have := j.isLt
  omega

/-- Reading the relocated number in the cell retrieves exactly the site's original entry. -/
theorem table_get (owner : Fin s → ℕ) (boxes : Fin s → List α) (v : Fin s) (j : Fin (boxes v).length) :
    (table owner boxes (owner v))[base owner (fun i => (boxes i).length) v + j.val]? =
      some ((boxes v).get j) := by
  rw [split_table,← before_length,List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left,List.getElem?_append_left j.isLt]
  exact getElem?_pos (boxes v) j.val j.isLt

/-- Input bit rows carry the owning cell and the number of one-copy box entries. -/
abbrev Input (s k w : ℕ) := Fin s × (Fin k ⊕ Fin w)

private def slot (s : ℕ) : Fin s ↪ Fin (2^Nat.clog 2 s) :=
  Fin.castLEEmb (Nat.le_pow_clog (by decide) _)

private def pad (u : Stable.Input (Nat.clog 2 s) k w) : Input s k w ⊕ Unit :=
  if h : u.1.val < s then .inl (⟨u.1.val,h⟩,u.2) else .inr ()

private noncomputable def source (s k w : ℕ) : Frame (Input s k w) (Stable.Input (Nat.clog 2 s) k w) :=
  (((Frame.initial id).step (fun _ : Unit => .const false)).withInput).select pad

/-- Public Boolean circuit returning a base box number at each real site row. -/
noncomputable def frame (s k w : ℕ) : Frame (Input s k w) (Fin s × Fin w) :=
  ((Stable.frame (Nat.clog 2 s) k w).subst (source s k w)).select fun ij => (slot s ij.1,ij.2)

/-- Stable-sort and scan gates per padded site. -/
def laneCost (b k w : ℕ) : ℕ :=
  ((w+b)+1+k) + b^2*(24*((w+b)+1+k)+1) + w*(60*k+40*w+63) + b^2*(24*(w+b)+1)

/-- The number of gates is linear in sites times a polynomial in the binary word widths. -/
theorem frame_size (s k w : ℕ) :
    (frame s k w).size ≤ 2 + 2*(s+1)*laneCost (Nat.clog 2 s) k w := by
  have h := Frame.step_size_le (Frame.initial (id : Input s k w → _)) (fun _ : Unit => .const false) 1 (fun _ => le_rfl)
  have hs : (source s k w).size ≤ 1 := by simpa [source] using h
  have hp : 2^Nat.clog 2 s ≤ 2*(s+1) := by
    by_cases hn : s = 0
    · simp [hn]
    · have hlt := layout_size (Fin s) (Fin 0) (by simpa using Nat.pos_of_ne_zero hn)
      simp only [Fintype.card_fin,Nat.add_zero] at hlt
      omega
  have hf : (Stable.frame (Nat.clog 2 s) k w).size ≤ 1 + 2^Nat.clog 2 s*laneCost (Nat.clog 2 s) k w :=
    Stable.frame_size _ _ _
  simp only [frame,Frame.select_size,Frame.subst_size]
  have hm := Nat.mul_le_mul_right (laneCost (Nat.clog 2 s) k w) hp
  omega

/-- Decoded owner word of one real input row. -/
def ownerWord (x : Input s k w → Bool) (i : Fin s) := value fun j => x (i,.inl j)

/-- Decoded one-copy box count, independent of the multiplicity of the local tensor. -/
def countWord (x : Input s k w → Bool) (i : Fin s) := value fun j => x (i,.inr j)

private theorem source_key (x : Input s k w → Bool) (i : Fin s) :
    Stable.key ((source s k w).eval x) (slot s i) = ownerWord x i := by
  simp [Stable.key,source,slot,pad,ownerWord,i.isLt]

private theorem source_count (x : Input s k w → Bool) (i : Fin s) :
    Stable.weight ((source s k w).eval x) (slot s i) = countWord x i := by
  simp [Stable.weight,source,slot,pad,countWord,i.isLt]

private theorem selected_sum (x : Input s k w → Bool) (pick : Fin (2^Nat.clog 2 s) → Prop) [DecidablePred pick] :
    (∑ i, if pick i then Stable.weight ((source s k w).eval x) i else 0) =
      ∑ u, if pick (slot s u) then countWord x u else 0 := by
  symm
  apply Fintype.sum_of_injective (slot s) (slot s).injective
  · intro i hi
    have hn : ¬ i.val < s := fun h => hi ⟨⟨i.val,h⟩,Fin.ext rfl⟩
    have hzero : ∀ a, value (fun _ : Fin a => false) = 0 := by
      intro a
      induction a with
      | zero => rfl
      | succ a ih => simp [value,ih]
    simp [Stable.weight,source,pad,hn,StatementCircuit.Expr.eval,hzero]
  · intro u
    rw [source_count]

/-- Two stable sorts and a segmented scan give the first ordinal of each input site. -/
theorem frame_value (x : Input s k w → Bool)
    (fits : ∀ c, (∑ i, if ownerWord x i = c then countWord x i else 0) < 2^w) (v : Fin s) :
    value (fun j => (frame s k w).eval x (v,j)) = base (ownerWord x) (countWord x) v := by
  let y := (source s k w).eval x
  have hfit (c : ℕ) : bucket (Stable.key y) (Stable.weight y) c < 2^w := by
    unfold bucket
    rw [selected_sum x (fun i => Stable.key y i = c)]
    simpa only [y,source_key] using fits c
  simp only [frame,Frame.select_eval,Frame.subst_eval]
  rw [Stable.frame_value y hfit,selected_sum x (fun i => Stable.key y i = Stable.key y (slot s v) ∧ i < slot s v)]
  simp only [y,source_key]
  rfl

/-- The actual public frame's number selects the intended box in the merged packet. -/
theorem frame_getD (x : Input s k w → Bool) (owner : Fin s → ℕ) (boxes : Fin s → List α)
    (ho : ∀ i, ownerWord x i = owner i) (hc : ∀ i, countWord x i = (boxes i).length)
    (room : ∀ c, (table owner boxes c).length < 2^w) (v : Fin s) (j : Fin (boxes v).length) (d : α) :
    (table owner boxes (owner v)).getD (value (fun b => (frame s k w).eval x (v,b)) + j.val) d =
      (boxes v).get j := by
  have hfit (c : ℕ) : (∑ i, if ownerWord x i = c then countWord x i else 0) < 2^w := by
    simpa only [ho,hc,table_length] using room c
  rw [frame_value x hfit,funext ho,funext hc,List.getD_eq_getElem?_getD,table_get,Option.getD_some]

end Packing.BankBoxOrdinal

end BorderVNP
end Computability
end OAI
