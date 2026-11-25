import OAI.Computability.BorderVNP.TeamContractionWiresSort
import OAI.Computability.BorderVNP.TeamTapeHandoffFrame
import OAI.Computability.BorderVNP.TeamTapeInputRouteDispatch
import OAI.Computability.BorderVNP.TeamSorting

/-! # One team's exact fixed interior wire layout

Real processors read any existing incoming and outgoing handoff frames first, followed
by their own virtual sorter block and, if assigned, one padding block. Unused positions
are pinned zero. Each freely summed wire is an actual frame bit, boundary bit or Batcher
send bit; endpoint clamps and padding never introduce a summation index.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.Wires

open VPVNP BurstRAM RAMLayout RAMTape TeamTapeInputRoute
open TeamTapeSorting (Fields)

/-- One word for the program counter and one for the cumulative clock in addition to the
register file; the separate status bit canonically encodes an accepted halt. -/
abbrev frameWidth (k w : ℕ) := 1+(k+2)*w

/-- Interior edge names of one team. The actual RAM width and physical sort word width
are separate parameters, allowing an extra address-phase bit in the sorter. -/
abbrev Edge (r k w e W : ℕ) :=
  (Fin (r-1) × Fin (frameWidth k w)) ⊕ SortEdge (Nat.clog 2 r) e W

variable {r k w e W : ℕ}

/-- All raw shared bits, without duplicate endpoint copies, are in bijection with the
raw register frames and the sorter fields. -/
def edgeEquiv : (Edge r k w e W → Bool) ≃
    (Fin (r-1) → Fin (frameWidth k w) → Bool) × Fields (Nat.clog 2 r) e W :=
  (Equiv.sumArrowEquivProdArrow _ _ _).trans
    ((Equiv.curry _ _ _).prodCongr sortEquiv)

/-- Primary virtual index of a real processor. -/
def primary (j : Fin r) : Word (Nat.clog 2 r) := j.castLE (Nat.le_pow_clog (by decide) r)

/-- At most one additional padded virtual index belongs to the same real owner. -/
def secondary (j : Fin r) : Option (Word (Nat.clog 2 r)) :=
  if h : j.val+r < 2^Nat.clog 2 r then some ⟨j.val+r,h⟩ else none

/-- All virtual blocks are assigned once, under the same owner map as the Batcher verifier. -/
theorem owned_iff (hr : 0 < r) (j : Fin r) (v : Word (Nat.clog 2 r)) :
    TeamSorting.owner hr v = j ↔ v = primary j ∨ secondary j = some v := by
  by_cases hv : v.val < r
  · simp only [TeamSorting.owner,dite_eq_left hv]
    constructor
    · intro h; left; apply Fin.ext; exact congrArg (Fin.val (n := r)) h
    · rintro (rfl|he)
      · rfl
      · unfold secondary at he
        split at he
        · cases he; change j.val+r < r at hv; omega
        · contradiction
  · simp only [TeamSorting.owner,dite_eq_right hv]
    constructor
    · intro h
      have he := congrArg Fin.val h
      change v.val-r = j.val at he
      have add : j.val+r = v.val := by omega
      right; simp [secondary,add,v.isLt]
    · rintro (rfl|he)
      · exact (hv j.isLt).elim
      · unfold secondary at he
        split at he
        · cases he; apply Fin.ext; change j.val+r-r = j.val; omega
        · contradiction

/-- Existing boundary index for a received or transmitted register frame. At either
missing endpoint the physical processor obtains no interior bytes from this field. -/
def frameIndex (receive : Bool) (j : Fin r) : Option (Fin (r-1)) :=
  if receive then
    if h : 0 < j.val then some ⟨j.val-1,by have := j.isLt; omega⟩ else none
  else if h : j.val+1 < r then some ⟨j.val,by omega⟩ else none

/-- The frame received by processor `j+1` is exactly the frame sent by processor `j`. -/
theorem adjacent_frame (j : Fin (r-1)) :
    frameIndex false (⟨j.val, by have := j.isLt; omega⟩ : Fin r) =
      frameIndex true ⟨j.val+1,by have := j.isLt; omega⟩ := by
  have hj := j.isLt
  simp [frameIndex,show j.val+1 < r by omega]

/-- Shared bit positions of one existing register frame, or no positions at an absent
boundary. -/
def frameSlots (receive : Bool) (j : Fin r) : List (Option (Edge r k w e W)) :=
  (frameIndex receive j).elim [] (fun i => List.ofFn (fun t => some (.inl (i,t))))

/-- Read a sender-indexed raw register frame at one real site. -/
def frameInput (fs : Fin (r-1) → Fin (frameWidth k w) → Bool) (receive : Bool) (j : Fin r) : List Bool :=
  (frameIndex receive j).elim [] (fun i => List.ofFn (fs i))

private theorem frames_read (f : Edge r k w e W → Bool) (receive : Bool) (j : Fin r) :
    (frameSlots receive j).map (fun i => i.elim false f) = frameInput (edgeEquiv f).1 receive j := by
  cases h : frameIndex receive j <;> simp [frameSlots,frameInput,h,List.map_ofFn,Function.comp_def]
  rfl

/-- Interior fields before padding, in physical read order for the site compiler. -/
def activeSlots (j : Fin r) : List (Option (Edge r k w e W)) :=
  frameSlots true j ++ frameSlots false j ++
    ((sortSlots (primary j)) ++ (secondary j).elim [] sortSlots).map (Option.map Sum.inr)

/-- Fixed common number of interior positions sufficient for every real processor. -/
def innerWidth (r k w e W : ℕ) :=
  2*frameWidth k w + 2*(10*W + comparisonSize (Nat.clog 2 r) e W)

private theorem frameSlots_le (receive : Bool) (j : Fin r) :
    (frameSlots receive j : List (Option (Edge r k w e W))).length ≤ frameWidth k w := by
  cases h : frameIndex receive j <;> simp [frameSlots,h]

/-- Both endpoint payloads and at most two virtual routing chunks fit the declared
fixed-width interior field. -/
theorem activeSlots_le (j : Fin r) :
    (activeSlots j : List (Option (Edge r k w e W))).length ≤ innerWidth r k w e W := by
  have h₁ := frameSlots_le (k := k) (w := w) (e := e) (W := W) true j
  have h₂ := frameSlots_le (k := k) (w := w) (e := e) (W := W) false j
  cases h : secondary j <;> simp only [activeSlots,List.length_append,List.length_map,h,
    Option.elim_none,Option.elim_some,List.length_nil,sortSlots_length,innerWidth] <;> omega

/-- The interior layout argument to the actual `Diagonal.Layout.slots`. Reading beyond the
active local fields supplies only pinned zeros. -/
def ownerSlots (j : Fin r) (i : Fin (innerWidth r k w e W)) : Option (Edge r k w e W) :=
  ((activeSlots j)[i.val]?).join

private theorem ownerList (j : Fin r) : List.ofFn (ownerSlots (k := k) (w := w) (e := e) (W := W) j) =
    activeSlots j ++ List.replicate (innerWidth r k w e W - (activeSlots j : List (Option (Edge r k w e W))).length) none := by
  have h := activeSlots_le (k := k) (w := w) (e := e) (W := W) j
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_append,List.length_replicate]; omega
  · intro i hi hj
    rw [List.getElem_ofFn]
    by_cases hx : i < (activeSlots j : List (Option (Edge r k w e W))).length
    · rw [List.getElem_append_left hx]
      simp [ownerSlots,List.getElem?_eq_getElem hx]
    · rw [List.getElem_append_right (by omega),List.getElem_replicate]
      simp [ownerSlots,List.getElem?_eq_none (Nat.le_of_not_gt hx)]

private theorem sortRead (f : Edge r k w e W → Bool) (v : Word (Nat.clog 2 r)) :
    (sortSlots v).map (fun i : Option (SortEdge (Nat.clog 2 r) e W) => (i.map Sum.inr).elim false f) =
      rowBits (edgeEquiv f).2 v := by
  have he (i : Option (SortEdge (Nat.clog 2 r) e W)) :
      (i.map Sum.inr).elim false f = i.elim false (fun z => f (.inr z)) := by cases i <;> rfl
  simp only [he]
  exact sortSlots_read (fun z => f (.inr z)) v

/-- Exact bits consumed by the handoff and sorting parsers, including the common
trailing zero-clamp padding. Interior variables are never used to supply these clamps. -/
theorem ownerSlots_read (f : Edge r k w e W → Bool) (j : Fin r) :
    List.ofFn (fun i => (ownerSlots j i).elim false f) =
      frameInput (edgeEquiv f).1 true j ++ frameInput (edgeEquiv f).1 false j ++
      ownerBits (edgeEquiv f).2 (primary j) (secondary j) ++
      List.replicate (innerWidth r k w e W - (activeSlots j : List (Option (Edge r k w e W))).length) false := by
  change List.ofFn ((fun i : Option (Edge r k w e W) => i.elim false f) ∘ ownerSlots j) = _
  rw [← List.map_ofFn,ownerList,List.map_append,List.map_replicate]
  cases h : secondary j <;> simp only [activeSlots,List.map_append,List.map_map,Function.comp_def,frames_read,
    h,Option.elim_some,Option.elim_none,sortRead,ownerBits,List.append_nil]

end TeamContraction.Wires

end BorderVNP
end Computability
end OAI
