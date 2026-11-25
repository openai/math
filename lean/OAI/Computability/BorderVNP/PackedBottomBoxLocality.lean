import OAI.Computability.BorderVNP.PackedBottomBoxInterpreter
import OAI.Computability.BorderVNP.PackedInheritedStaging

/-! # Locality of the original repeated grid boxes

The public records access the private copy slabs and the following cable words.
Inside each immutable box, the original tests, selected-bit reports, relocation
checks and padding tests read relative lanes within the very same copy.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomRepeat

open Crossing Inherited CellSparse
open scoped Classical

variable {D qe qa : ℕ} {A : Type} [Fintype A] {width : A → ℕ}
variable (N : Network D A width) (edges : N.Edge ↪ Fin qe) (ports : A ↪ Fin qa) (v : N.Site)

private theorem rowEnd (r : Row N v) :
    oneStart N edges ports v r + rowWidth N v r ≤ incoming N v := by
  cases r with
  | inl z => exact wireEnd_le N edges ports v z
  | inr z => exact portEnd_le N edges ports v z

private theorem wideEnd (copies : ℕ) (r : Row N v) :
    wideStart N edges ports v copies r + copies * rowWidth N v r ≤ incoming (wide N copies) v := by
  cases r with
  | inl z => exact wireEnd_le (wide N copies) edges ports v z
  | inr z => exact portEnd_le (wide N copies) edges ports v z

private theorem copyBit_lt {copies stride i k : ℕ} (hi : i < copies) (hk : k < stride) :
    i*stride+k < copies*stride := by
  have h := Nat.mul_le_mul_right stride hi
  rw [Nat.succ_mul] at h
  omega

private theorem mapM_same {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ a ∈ xs, f a = g a) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.mapM_cons,h a List.mem_cons_self,ih fun b hb => h b (.tail _ hb)]

/-- Both sides of every strided incidence equality, and the complete ordered
list of observations from the repeated box, depend only on this site's bank. -/
theorem bornWith_local (copies capFine stride : ℕ) (box : List Factor)
    (fits : capFine + incoming N v ≤ stride) (localReads : ∀ f ∈ box, FactorWithin stride f) :
    (bornWith N edges ports v copies capFine stride box).Local := by
  let s := bornWith N edges ports v copies capFine stride box
  intro x y h
  have same (k) (hk : k < copies*stride+incoming (wide N copies) v) := h k hk
  have tiesEq : (∀ r ∈ s.rows,r.Valid s.boxes x) ↔ ∀ r ∈ s.rows,r.Valid s.boxes y := by
    have pass (b : ℕ → Bool) := (bornWith_rows_valid N edges ports v copies capFine stride box b).trans
      (ties_valid N edges ports v copies capFine stride [box] b)
    apply (pass x).trans
    apply Iff.trans _ (pass y).symm
    apply forall_congr'; intro r
    apply forall_congr'; intro i
    apply forall_congr'; intro k
    have he := rowEnd N edges ports v r
    have ha := copyBit_lt i.isLt (show capFine+oneStart N edges ports v r+k.val < stride by omega)
    have hw := wideEnd N edges ports v copies r
    have hb := copyBit_lt i.isLt k.isLt
    rw [same (i.val*stride+capFine+oneStart N edges ports v r+k.val) (by omega),
      same (copies*stride+wideStart N edges ports v copies r+i.val*rowWidth N v r+k.val) (by omega)]
  have obsEq : s.directory.observations x = s.directory.observations y := by
    unfold Directory.observations
    apply mapM_same
    intro occ ho
    rw [bornWith_occurrences] at ho
    obtain ⟨i,hi,hocc⟩ := List.mem_flatMap.mp ho
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hocc
    apply factor_agrees stride f (localReads f hf)
    intro k hk
    exact same _ ((copyBit_lt (List.mem_range.mp hi) hk).trans_le (Nat.le_add_right _ _))
  change s.observe x = s.observe y
  rw [Site.observe,Site.observe]
  by_cases hx : ∀ r ∈ s.rows,r.Valid s.boxes x
  · rw [ite_eq_left hx,ite_eq_left (tiesEq.mp hx),obsEq]
  · rw [ite_eq_right hx,ite_eq_right (mt tiesEq.mpr hx)]

/-- Relative reads below a smaller stride remain inside any containing stride. -/
theorem FactorWithin.mono {n m : ℕ} {f : Factor} (h : FactorWithin n f) (le : n ≤ m) :
    FactorWithin m f := by
  cases f with
  | truth | sign | gadget => exact fun k hk => (h k hk).trans_le le
  | unary => exact h.elim

end Packing.BottomRepeat

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports BottomRepeat Inherited
open scoped Classical

private theorem compare_within {n wire rel : ℕ} (hw : wire < n) (hr : rel < n) :
    FactorWithin n (compareUse wire rel) := by
  simp [FactorWithin,compareUse,hw,hr]

private theorem zero_within {n addr : ℕ} (h : addr < n) : FactorWithin n (GridPadding.zeroFactor addr) := by
  simp [FactorWithin,GridPadding.zeroFactor,h]

private theorem stage_within (n next : ℕ) (fs : List Factor) (room : next+count fs ≤ n)
    (fits : ∀ f ∈ fs, match f with | .unary wire _ => wire < n | _ => FactorWithin n f) :
    ∀ f ∈ stage next fs, FactorWithin n f := by
  induction fs generalizing next with
  | nil => simp [stage]
  | cons f fs ih =>
    obtain ⟨hhead,htail⟩ := List.forall_mem_cons.mp fits
    cases f with
    | unary wire tag =>
      simp only [count] at room
      exact List.forall_mem_cons.mpr ⟨compare_within hhead (by omega),ih _ (by omega) htail⟩
    | truth | sign | gadget =>
      exact List.forall_mem_cons.mpr ⟨hhead,ih _ room htail⟩

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ u : {u : N.Site // cell u = v}, Rule N u.val)
variable (capFine capReport : ℕ)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "fs" => GridBoxes.factors N cell v siteID edgeID portID rules
local notation "sz" => bottomStride (capFine+incoming G v) capReport
local notation "box" => stored N cell position pack width owner lane aligned siteID edgeID portID channelID
  groupID v rules capFine capReport

/-- The relocation and zero-padding checks alone use only the fine storage
and grouped inputs. A scalar bottom box can use this bound with no report slab. -/
theorem wiring_within (hf : GridBoxes.stride N cell v ≤ capFine) :
    ∀ f ∈ wiring N cell position pack width owner lane aligned edgeID portID channelID groupID v capFine,
      FactorWithin (capFine+incoming G v) f := by
  simp only [wiring,List.forall_mem_append]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro f h
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp h
    have hk := (publicIndex N cell position pack width owner lane aligned edgeID portID channelID groupID v k).isLt
    apply compare_within
    · exact (Nat.add_lt_add_left k.isLt _).trans_le (hf.trans (Nat.le_add_right _ _))
    · omega
  · intro f h
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    have hlt := List.mem_range.mp hk
    apply zero_within
    omega
  · intro f h
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp h
    apply zero_within
    unfold channelAddress
    have hlt := (sourceOrder G channelID groupID v (.inl ⟨l.1,l.2⟩)).isLt
    omega

/-- Every actual immutable factor, including padding at privately unused
cable lanes, is relative and reads below the declared copy stride. -/
theorem stored_within (hf : GridBoxes.stride N cell v ≤ capFine) (hr : count fs ≤ capReport) :
    ∀ f ∈ box, FactorWithin sz f := by
  simp only [stored,List.forall_mem_append]
  have hspan : GridBoxes.stride N cell v ≤ sz := hf.trans (by unfold bottomStride; omega)
  refine ⟨⟨stage_within _ _ _ (by unfold bottomStride; omega) ?_,?_⟩,?_⟩
  · intro f h
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp h
    cases hru : rules u with
    | truth t =>
      change ∀ k ∈ List.ofFn (fun i => (GridBoxes.lane N cell v edgeID portID u
        ((Fintype.equivFin _).symm i)).val), k < sz
      intro k hk
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
      exact Fin.isLt _ |>.trans_le hspan
    | unary k tag => exact (GridBoxes.lane N cell v edgeID portID u k).isLt.trans_le hspan
  · intro f h
    exact (wiring_within N cell position pack width owner lane aligned edgeID portID channelID groupID
      v capFine hf f h).mono (Nat.le_add_right _ _)
  · intro f h
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
    have hlt := List.mem_range.mp hk
    apply zero_within
    unfold bottomStride
    omega

/-- The full program at a real routed bottom cell is an intrinsic local site
for every copy multiplicity, including an empty bundle. -/
theorem born_local (copies : ℕ) (hf : GridBoxes.stride N cell v ≤ capFine) (hr : count fs ≤ capReport) :
    (born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
      copies capFine capReport).Local :=
  bornWith_local G channelID groupID v copies capFine sz box (Nat.le_add_right _ _) <|
    stored_within N cell position pack width owner lane aligned siteID edgeID portID channelID groupID
      v rules capFine capReport hf hr

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
