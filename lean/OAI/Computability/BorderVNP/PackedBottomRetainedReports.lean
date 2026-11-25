import OAI.Computability.BorderVNP.PackedBottomNativeNames
import OAI.Computability.BorderVNP.PackedRetainedWork
import OAI.Computability.BorderVNP.PackedInheritedMergeRows

/-! # Physical offsets and retained prefixes of bottom report operands

The supplemental equalities have one translated base for the staged reports
and another for the compact cursor. The old site's private bits retain their
addresses through every shortening layer. Final placement appends incoming
words and puts the whole site at its real prefix within the cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse Inherited

private theorem links_shift (off base stride copies cursor : ℕ) (ps : List (Port × ℕ)) :
    (links base stride copies cursor ps).map (fun r => r.shift off) =
      links (off+base) stride copies (off+cursor) ps := by
  induction ps generalizing cursor with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨tag,k⟩
    simp only [links,List.map_cons]
    rw [ih]
    simp only [Record.shift,stagedPort,usePort,Port.shift,Nat.add_assoc]

/-- Relocating a complete supplemental block shifts both bank addresses and
preserves all strided copy/width fields and the final zero-padding command. -/
theorem reportRows_shift (off base orig cap copies cursor : ℕ) (fs : List Factor) :
    (reportRows base orig cap copies cursor fs).map (fun r => r.shift off) =
      reportRows (off+base) orig cap copies (off+cursor) fs := by
  simp only [reportRows,List.map_append,links_shift,List.map_cons,List.map_nil]
  simp only [padding,Record.shift,stagedPort,Port.shift,Nat.add_assoc]

/-- The actual translated supplemental block checks the original private
coordinates against the translated bank, including the unused suffix. -/
theorem reportRows_valid_shift (bank : ℕ → Bool) (boxes : List (List Factor))
    (off base orig cap copies cursor : ℕ) (fs : List Factor) :
    (∀ r ∈ reportRows (off+base) orig cap copies (off+cursor) fs,r.Valid boxes bank) ↔
      ∀ r ∈ reportRows base orig cap copies cursor fs, r.Valid boxes (fun k => bank (off+k)) := by
  rw [← reportRows_shift]
  simp only [List.forall_mem_map,Record.valid_shift]

/-- Source-major name lookup commutes with a translated use cursor. -/
theorem namedAt_shift (bank : ℕ → Bool) (use : Port → Bool) (off copies copy cursor : ℕ) (ps : List (Port × ℕ)) :
    NamedAt bank use copies copy (off+cursor) ps ↔
      NamedAt (fun k => bank (off+k)) use copies copy cursor ps := by
  rw [namedAt_iff,namedAt_iff]
  simp only [Nat.add_assoc]

open private bits_left from OAI.Computability.BorderVNP.PackedInheritedStaging

/-- The original complete work tape is read unchanged from any intrinsic
retained bank; input staging added at later cuts lies after that tape. -/
theorem complete_read {a s : Site} (p : a.Retention s) (x : Fin s.incoming → Bool)
    (g : Fin a.work → Bool) (k : ℕ) (hk : k < a.work) :
    bits (p.complete x g) x k = bits g (p.readInput x) k :=
  (bits_left (p.complete x g) x (Fin.castLE p.work_le ⟨k,hk⟩)).trans
    ((p.complete_prefix x g ⟨k,hk⟩).trans (bits_left g (p.readInput x) ⟨k,hk⟩).symm)

private theorem copyLane_lt {copies stride : ℕ} (i : Fin copies) (k : Fin stride) :
    i.val*stride+k.val < copies*stride := by
  have h := Nat.mul_le_mul_right stride i.isLt
  rw [Nat.succ_mul] at h
  have := k.isLt
  omega

/-- For a passing physical site, simultaneously recover a passing birth tape
and every selected/staged relative lane of every original copy. -/
theorem accepted_copy_reads {a s : Site} (p : a.Retention s) (loc : a.Local)
    (x : Fin s.incoming → Bool) (raw : Fin s.work → Bool) (obs : List (Bool × Option ℕ))
    (ok : s.observe (bits raw x) = some obs) (copies stride : ℕ) (room : copies*stride ≤ a.work) :
    ∃ g : Fin a.work → Bool, a.observe (bits g (p.readInput x)) = some obs ∧ p.complete x g = raw ∧
      ∀ (i : Fin copies) (k : Fin stride), bits raw x (i.val*stride+k.val) =
        bits g (p.readInput x) (i.val*stride+k.val) := by
  obtain ⟨g,hg,eq⟩ := (p.observe_iff loc x obs raw).mp ok
  refine ⟨g,hg,eq,?_⟩
  intro i k
  rw [← eq]
  exact complete_read p x g _ ((copyLane_lt i k).trans_le room)

end Packing.BottomReports

namespace Packing.Inherited.Placement

open Crossing CellSparse CellAddresses BottomReports
open CellMacro
open private sizes off capacity region read_prefix off_fits from OAI.Computability.BorderVNP.PackedInheritedMergeRows
open scoped Classical

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {ext : P → ℕ} (N : Network D P ext)
    {C : Type} (cell : N.Site → C) (c : C) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin M)
    (portID : P ↪ Fin np) (state : N.Site → Site) (hs : ∀ v,(state v).incoming = incoming N v)
    (g : Fin (guessedSize N cell c) → Bool) (x : Fin (suppliedSize N cell c) → Bool)
    (work : Work N cell c state)

local notation "installed₀" => install N cell c siteID edgeID portID state hs g x work
local notation "bank₀" => bank N cell c (Site.size ∘ state) g installed₀ x

/-- Read any private retained lane from the actual merged cell, with an
arbitrary supplemental bit suffix after the supplied inputs. -/
theorem installed_work_at (v : {v : N.Site // cell v = c}) (k : Fin (state v.val).work) (tail : List Bool) :
    lookup (bank₀++tail) (siteBase N cell c siteID (fun u => (state u).size) v+k.val) = work v k := by
  let j : Fin (state v.val).size := k.castAdd (state v.val).incoming
  have bound := (Nat.add_lt_add_left j.isLt (off N cell c siteID state v)).trans_le
    (off_fits N cell c siteID state v)
  have pre := read_prefix N cell c state g installed₀ x tail _ bound
  apply pre.trans
  apply (site_at N cell c (fun u => (state u).size) siteID g installed₀ x v j).trans
  have read := congrFun (read_install N cell c siteID edgeID portID state hs g x work v) j
  exact read.trans (Fin.append_left ..)

/-- The physical cell address of any original selected or staged bit after
installation reads exactly the same birth work bit, at its old relative address. -/
theorem installed_birth_at (v : {v : N.Site // cell v = c}) {a : Site} (p : a.Retention (state v.val))
    (input : Fin (state v.val).incoming → Bool) (birth : Fin a.work → Bool)
    (completed : work v = p.complete input birth) (k : Fin a.work) (tail : List Bool) :
    lookup (bank₀++tail) (siteBase N cell c siteID (fun u => (state u).size) v+k.val) = birth k := by
  apply (installed_work_at N cell c siteID edgeID portID state hs g x work v (k.castLE p.work_le) tail).trans
  rw [completed]
  exact p.complete_prefix input birth k

open private bits_left from OAI.Computability.BorderVNP.PackedInheritedStaging

/-- A passing staged birth row and the actual supplemental equality force the
final compact use, final staged bit and final selected fine wire to equal the
same original private bit. The compact cursor can lie anywhere in the owning
cell's report area, independently of the retained site's work base. -/
theorem installed_selected_report (v : {v : N.Site // cell v = c}) {a : Site}
    (p : a.Retention (state v.val)) (input : Fin (state v.val).incoming → Bool) (birth : Fin a.work → Bool)
    (completed : work v = p.complete input birth) (original : List Factor) (orig cap copies cursor : ℕ)
    (room : copies*bottomStride orig cap ≤ a.work) (marksFit : count original ≤ cap)
    (i : Fin copies) (r : Fin (count original)) (tail : List Bool) (boxes : List (List Factor))
    (wireFits : (selectedWires original)[r.val]'(by simpa only [selectedWires_length] using r.isLt) < bottomStride orig cap)
    (stagePass : ∀ f ∈ stage orig original, (f.observe (bits birth (p.readInput input))
      (i.val*bottomStride orig cap) i.val).isSome = true)
    (suppPass : ∀ row ∈ reportRows (siteBase N cell c siteID (fun u => (state u).size) v)
      orig cap copies cursor original, row.Valid boxes (lookup (bank₀++tail))) :
    let off := siteBase N cell c siteID (fun u => (state u).size) v
    let bank := lookup (bank₀++tail)
    let stride := bottomStride orig cap
    let wire := (selectedWires original)[r.val]'(by simpa only [selectedWires_length] using r.isLt)
    bank (cursor+r.val*copies+i.val) = bits birth (p.readInput input) (i.val*stride+wire) ∧
      bank (off+i.val*stride+orig+r.val) = bank (off+i.val*stride+wire) := by
  intro off bank stride wire
  have hr : orig+r.val < stride := by
    have h := r.isLt
    dsimp only [stride,bottomStride]
    omega
  have lane (k : Fin stride) : bank (off+i.val*stride+k.val) =
      bits birth (p.readInput input) (i.val*stride+k.val) := by
    let t : Fin a.work := ⟨i.val*stride+k.val,(BottomReports.copyLane_lt i k).trans_le room⟩
    rw [Nat.add_assoc]
    exact (installed_birth_at N cell c siteID edgeID portID state hs g x work v p input birth completed t tail).trans
      (bits_left birth (p.readInput input) t).symm
  have staged := lane ⟨orig+r.val,hr⟩
  have selected := lane ⟨wire,wireFits⟩
  have originalEq := ((stage_pass (bits birth (p.readInput input)) _ i.val orig original).mp stagePass).2 r
  have eq : bank (off+i.val*stride+orig+r.val) = bits birth (p.readInput input) (i.val*stride+wire) := by
    rw [Nat.add_assoc (off+i.val*stride)]
    apply staged.trans
    simpa only [Nat.add_assoc] using originalEq
  have linked := (reportRows_valid bank boxes off orig cap copies cursor original marksFit).mp suppPass
    i.val i.isLt r.val (r.isLt.trans_le marksFit)
  rw [stageValue,ite_eq_left r.isLt] at linked
  exact ⟨linked.symm.trans eq,eq.trans selected.symm⟩

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI
