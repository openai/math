import OAI.Hierarchy.DescentBundleHistory
import OAI.Hierarchy.DescentGranularBitHistory

namespace OAI
/-! # Aligned payloads through the two native cable-splitting operations -/

namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentKernelHistory DescentSixParty DescentSixParty.MarkedWorld
open scoped Classical
noncomputable section
set_option quotPrecheck false

private def coarse {p t q w m : ℕ} (hp : 0<p) (ht : 0<t) (hq : q=t*p) (cut : w=m*q)
    (b : ℕ) (fits : (b+1)*p≤w) : Fin m :=
  ⟨b/t,by
    have bound : (b+1)*p≤(m*t)*p := by simpa only [cut,hq,Nat.mul_assoc] using fits
    exact (Nat.div_lt_iff_lt_mul ht).mpr (Nat.le_of_mul_le_mul_right bound hp)⟩

private theorem fine_fit {p t q : ℕ} (ht : 0<t) (hq : q=t*p) (b : ℕ) :
    (b%t+1)*p≤q := by
  rw [hq]
  exact Nat.mul_le_mul_right p (Nat.mod_lt b ht)

/-- Dividing a row-major bit address by the enclosing grain preserves the entire low payload. -/
private theorem split_digit {p t q w m : ℕ} (hp : 0<p) (ht : 0<t) (hq : q=t*p)
    (cut : w=m*q) (b : ℕ) (fits : (b+1)*p≤w) (d : Fin p) :
    finProdFinEquiv.symm (Fin.cast cut ⟨b*p+d.val,
      (Nat.add_lt_add_left d.isLt _).trans_le (by simpa [Nat.succ_mul] using fits)⟩) =
    (coarse hp ht hq cut b fits,
      ⟨b%t*p+d.val,(Nat.add_lt_add_left d.isLt _).trans_le (by simpa [Nat.succ_mul] using fine_fit ht hq b)⟩) := by
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change b*p+d.val=(b%t*p+d.val)+q*(b/t)
  rw [hq]
  calc
    b*p+d.val=(b%t+t*(b/t))*p+d.val := by rw [Nat.mod_add_div]
    _ = _ := by ring

section Pieces
variable {D : ℕ} {P : Type} {bits : P→ℕ} (N : Network D P bits)
variable (core : Finset N.Edge) (m : N.Edge→ℕ) (q : ℕ) (cut : ∀e∈core,N.width e=m e*q)
variable {p t : ℕ} (hp : 0<p) (ht : 0<t) (hq : q=t*p) (v : N.Site)
include hp ht hq
local notation "Q" => DescentCableUnbundling.network N core m q

private def pieceRef : BlockRef p (boundaryWidth N v) → BlockRef p (boundaryWidth Q v)
  | ⟨.inr pin,b,fit⟩ => ⟨.inr pin,b,fit⟩
  | ⟨.inl e,b,fit⟩ =>
    if keep : e.val∈core then
      ⟨.inl ⟨.inr ⟨⟨e.val,keep⟩,coarse hp ht hq (cut e.val keep) b fit⟩,e.property⟩,
       b%t,fine_fit ht hq b⟩
    else ⟨.inl ⟨.inl ⟨e.val,keep⟩,e.property⟩,b,fit⟩

private theorem pieceRef_marked (e : Incident N v) (b : ℕ) (fit : (b+1)*p ≤ N.width e.val)
    (mark : e.val ∈ core) :
    pieceRef N core m q cut hp ht hq v ⟨.inl e,b,fit⟩ =
      ⟨.inl ⟨.inr ⟨⟨e.val,mark⟩,coarse hp ht hq (cut e.val mark) b fit⟩,e.property⟩,
        b%t,fine_fit ht hq b⟩ :=
  dite_eq_left mark

private theorem pieceRef_unmarked (e : Incident N v) (b : ℕ) (fit : (b+1)*p ≤ N.width e.val)
    (keep : e.val ∉ core) :
    pieceRef N core m q cut hp ht hq v ⟨.inl e,b,fit⟩ =
      ⟨.inl ⟨.inl ⟨e.val,keep⟩,e.property⟩,b,fit⟩ :=
  dite_eq_right keep

/-- Only marked edges split. Pins and unmarked incident edges keep their bit address. -/
def pieceMap : BlockMap p (boundaryWidth N v) (boundaryWidth Q v) (pieceBit N core m q cut v) where
  map := pieceRef N core m q cut hp ht hq v
  read := by
    rintro ⟨e|pin,b,fit⟩ d
    · by_cases keep : e.val∈core
      · let emit (z : Fin (m e.val) × Fin q) : BitRef (boundaryWidth Q v) :=
          ⟨.inl ⟨.inr ⟨⟨e.val,keep⟩,z.1⟩,e.property⟩,z.2⟩
        have route (j : Fin (N.width e.val)) :
            pieceBit N core m q cut v ⟨.inl e,j⟩ =
              emit (finProdFinEquiv.symm (Fin.cast (cut e.val keep) j)) := dite_eq_left keep
        rw [pieceRef_marked N core m q cut hp ht hq v e b fit keep]
        exact (congrArg emit (split_digit hp ht hq (cut e.val keep) b fit d).symm).trans
          (route _).symm
      · have route (j : Fin (N.width e.val)) :
            pieceBit N core m q cut v ⟨.inl e,j⟩ = ⟨.inl ⟨.inl ⟨e.val,keep⟩,e.property⟩,j⟩ :=
          dite_eq_right keep
        rw [pieceRef_unmarked N core m q cut hp ht hq v e b fit keep]
        exact (route _).symm
    · rfl

variable (e : Incident N v) (word : ℕ) (fits : (word+1)*p≤N.width e.val)
local notation "oldWord" => (⟨.inl e,word,fits⟩ : BlockRef p (boundaryWidth N v))
local notation "child" => (pieceMap N core m q cut hp ht hq v).map oldWord

/-- Splitting a marked operand selects this exact subwire and remainder. -/
theorem pieceMap_marked (mark : e.val∈core) (unit : Fin (m e.val)) (atUnit : unit.val=word/t) :
    (child).port=.inl ⟨.inr ⟨⟨e.val,mark⟩,unit⟩,e.property⟩ ∧ (child).block=word%t :=by
  have index : coarse hp ht hq (cut e.val mark) word fits=unit:=Fin.ext atUnit.symm
  change (pieceRef N core m q cut hp ht hq v oldWord).port = _ ∧
    (pieceRef N core m q cut hp ht hq v oldWord).block = _
  rw [pieceRef_marked N core m q cut hp ht hq v e word fits mark, index]
  exact ⟨rfl,rfl⟩

/-- An unmarked operand keeps its original wire and full block number. -/
theorem pieceMap_unmarked (keep : e.val∉core) :
    (child).port=.inl ⟨.inl ⟨e.val,keep⟩,e.property⟩ ∧ (child).block=word :=by
  change (pieceRef N core m q cut hp ht hq v oldWord).port = _ ∧
    (pieceRef N core m q cut hp ht hq v oldWord).block = _
  rw [pieceRef_unmarked N core m q cut hp ht hq v e word fits keep]
  exact ⟨rfl,rfl⟩

end Pieces

section Whole
variable {F P : Type} [Field F] {D : ℕ} {bits : P→ℕ} (W : MarkedWorld F D P bits)
variable (m : W.graph.Edge→ℕ) (q : ℕ) (cut : ∀e,W.graph.width e=m e*q)
variable {p t : ℕ} (hp : 0<p) (ht : 0<t) (hq : q=t*p) (v : W.graph.Site)
include hp ht hq
local notation "M" => grains W m q

private def grainRef : BlockRef p (boundaryWidth W.graph v) → BlockRef p (boundaryWidth M v)
  | ⟨.inr pin,b,fit⟩ => ⟨.inr pin,b,fit⟩
  | ⟨.inl e,b,fit⟩ =>
    ⟨.inl ⟨⟨e.val,coarse hp ht hq (cut e.val) b fit⟩,e.property⟩,b%t,fine_fit ht hq b⟩

/-- Splitting all incident cables uses the same quotient and remainder at every site. -/
def grainMap : BlockMap p (boundaryWidth W.graph v) (boundaryWidth M v)
    (BitDescription.grainBit W m q cut v) where
  map := grainRef W m q cut hp ht hq v
  read := by
    rintro ⟨e|pin,b,fit⟩ d
    · let emit (z : Fin (m e.val) × Fin q) : BitRef (boundaryWidth M v) :=
        ⟨.inl ⟨⟨e.val,z.1⟩,e.property⟩,z.2⟩
      exact congrArg emit (split_digit hp ht hq (cut e.val) b fit d).symm
    · rfl

/-- All local recipes retain their payload shape under the actual whole-grain operation. -/
def Shape.granular {B : BitDescription W} (s : Shape p (B.recipe v)) :
    Shape p ((BitDescription.granular W m q cut B).recipe v) :=
  s.reroute (grainMap W m q cut hp ht hq v)

/-- All local recipes retain their payload shape when only the marked core splits. -/
def Shape.pieces {B : BitDescription W} (split : ∀e∈W.core,W.graph.width e=m e*q)
    (s : Shape p (B.recipe v)) : Shape p ((B.pieces m q split).recipe v) :=
  s.reroute (pieceMap W.graph W.core m q split hp ht hq v)

end Whole
end
end Hierarchy.DescentBundleHistory

end OAI
