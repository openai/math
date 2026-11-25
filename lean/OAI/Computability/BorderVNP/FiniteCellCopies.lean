import OAI.Computability.BorderVNP.FiniteCellEvaluation
import OAI.Computability.BorderVNP.CrossingCellBoxRecords

/-! # Sharing one finite-field cell directory across a bottom bundle

The public box record visits every copy at a stride equal to the number of
original lanes. Only one private list of literal site tables is stored.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldDirectory.Copies

open Crossing CellSparse
open scoped BigOperators Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {F : Type*} [Fintype F]

/-- The first bank region contains the independent original lanes for every copy. -/
noncomputable def width (copies : ℕ) : ℕ := copies * Fintype.card (Wire N)

/-- Subtotal bits follow the last copy, in bit and then scalar order. -/
noncomputable def claimAddress (copies w : ℕ) (v : Fin (Fintype.card F)) (i : Fin w) : ℕ :=
  width N copies + (finProdFinEquiv (i,v)).val

/-- One box directory and one public repeat instruction, independent of the
number of site visits. -/
noncomputable def directory (sites : List N.Site) (table : N.Tables F) (copies w : ℕ) : Directory where
  boxes := [sites.map (factor N table)]
  records := [.box 0 0 copies (Fintype.card (Wire N))]
  reportedCounts := List.ofFn fun j : Fin (Fintype.card F) => List.ofFn (claimAddress N copies w j)

/-- The physical bank containing every copy and an arbitrary suffix. -/
noncomputable def bank {copies : ℕ} (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits)
    (extra : ℕ → Bool) (j : ℕ) : Bool :=
  if h : j < width N copies then
    let ix := finProdFinEquiv.symm (⟨j,h⟩ : Fin (copies*Fintype.card (Wire N)))
    FieldDirectory.bank N (a ix.1) (x ix.1) (fun _ => false) ix.2.val
  else extra (j - width N copies)

omit [Fintype F] in
private theorem bank_read {copies : ℕ} (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits)
    (extra : ℕ → Bool) (c : Fin copies) (lane : Fin (Fintype.card (Wire N))) :
    bank N a x extra (c.val * Fintype.card (Wire N) + lane.val) =
      FieldDirectory.bank N (a c) (x c) (fun _ => false) lane.val := by
  have he : c.val * Fintype.card (Wire N) + lane.val = (finProdFinEquiv (c,lane)).val := by simp [Nat.add_comm,Nat.mul_comm]
  rw [he]
  simp only [bank,width,(finProdFinEquiv (c,lane)).isLt,dite_true,Fin.eta,Equiv.symm_apply_apply]

omit [Fintype F] in
private theorem read_word {copies : ℕ} (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits)
    (extra : ℕ → Bool) (c : Fin copies) (lanes : List ℕ) (fit : ∀ j ∈ lanes, j < Fintype.card (Wire N)) :
    word (bank N a x extra) (lanes.map (c.val * Fintype.card (Wire N) + ·)) =
    word (FieldDirectory.bank N (a c) (x c) (fun _ => false)) lanes := by
  induction lanes with
  | nil => rfl
  | cons j js ih =>
    have h := bank_read N a x extra c ⟨j,fit j (by simp)⟩
    simp only [List.map_cons,word,h,ih (fun k hk => fit k (by simp [hk]))]

/-- A visit at its physical offset observes the original entry of that copy. -/
theorem observe_site {copies : ℕ} (table : N.Tables F) (s : N.Site) (a : Fin copies → N.Assignment)
    (x : Fin copies → Ports bits) (extra : ℕ → Bool) (c : Fin copies) :
    (factor N table s).observe (bank N a x extra) (c.val*Fintype.card (Wire N)) c.val =
      some (false,some (Fintype.equivFin F (N.read table (a c) (x c) s)).val) := by
  have fit : ∀ j ∈ addresses N s, j < Fintype.card (Wire N) := by
    intro j hj
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
    exact Fin.isLt _
  have eq := FieldDirectory.observe_factor N table s (a c) (x c) (fun _ => false) c.val
  simp only [factor,Factor.observe,Nat.zero_add] at eq ⊢
  rw [read_word N a x extra c _ fit]
  simpa only [show (fun z : ℕ => z) = id from rfl,List.map_id] using eq

/-- Ordered visits made by the repeat instruction. This is its expanded execution,
with one stored row directory for all its visits. -/
def visits {S : Type} (copies : ℕ) (sites : List S) : List (Fin copies × S) :=
  (List.finRange copies).flatMap fun c => sites.map (Prod.mk c)

private theorem range_eq (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

/-- Occurrences of the real sparse directory have the exact copy number and stride. -/
theorem occurrences (sites : List N.Site) (table : N.Tables F) (copies w : ℕ) :
    (directory N sites table copies w).occurrences = (visits copies sites).map
      fun cs => (⟨factor N table cs.2,cs.1.val * Fintype.card (Wire N),cs.1.val⟩ : Occurrence) := by
  simp only [Directory.occurrences,directory,visits,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.getD_cons_zero,Nat.zero_add,List.map_flatMap,List.map_map,Function.comp_def]
  rw [range_eq,List.flatMap_map]

/-- All actual scalars, in copy, site order. -/
def entries {copies : ℕ} (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) : List F :=
  (visits copies sites).map fun cs => N.read table (a cs.1) (x cs.1) cs.2

/-- Literal positions of the entries visited by all copies of a box. -/
noncomputable def ids {copies : ℕ} (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) : List ℕ :=
  (entries N sites table a x).map fun v => (Fintype.equivFin F v).val

/-- The sparse box observations are exactly the positions selected by all copies,
including repeats and zero scalar values. -/
theorem observations {copies : ℕ} (sites : List N.Site) (table : N.Tables F) (w : ℕ)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) (extra : ℕ → Bool) :
    (directory N sites table copies w).observations (bank N a x extra) =
      some ((ids N sites table a x).map fun j => (false,some j)) := by
  rw [Directory.observations,occurrences,ids,entries,List.map_map,List.map_map]
  induction visits copies sites with
  | nil => rfl
  | cons cs rest ih =>
    simp only [List.map_cons,List.mapM_cons,observe_site,ih,Option.pure_def,Option.bind_eq_bind,Option.bind_some,Function.comp_apply]

omit [Fintype P] in
/-- The total number of reported factors is the number of copies times the number of sites. -/
theorem ids_length {copies : ℕ} (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) :
    (ids N sites table a x).length = copies * sites.length := by
  simp [ids,entries,visits,List.length_flatMap,Function.comp_def]

omit [Fintype P] [Fintype F] in
/-- Multiplying the observed scalar entries recovers all independent copies' site products. -/
theorem entries_prod [CommMonoid F] {copies : ℕ} (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (x : Fin copies → Ports bits) :
    (entries N sites table a x).prod = ∏ c : Fin copies, (sites.map (N.read table (a c) (x c))).prod := by
  simp only [entries,visits,List.map_flatMap,List.map_map,Function.comp_def]
  rw [List.flatMap_def,List.prod_flatten,← List.ofFn_id,List.map_ofFn,List.map_ofFn,List.prod_ofFn]
  rfl

end FieldDirectory.Copies

end BorderVNP
end Computability
end OAI
