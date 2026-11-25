import OAI.Hierarchy.TaggedWirePacketScan
import OAI.Hierarchy.TaggedWirePacketFaces

namespace OAI
/-! # Actual primary/mate menu expressions for ordinary, retained, tree, and catalyst wires -/

noncomputable section
namespace Hierarchy.WireTelescope.StripPaths
open LinearAlgebra.SpectralBooks ChordGraph Probe AdaptiveProbe AdaptiveProbe.Strip
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM Calendar.CatalogueRows
open scoped Fin.CommRing Classical

variable {n k K N : ℕ} {C H E Ball : Type}
local notation "R" => ColumnWires.Role C H E k

def widthKind : R→Bool
  | .catalyst _ _=>true
  | _=>false

def menuLen (r : R⊕TreeLink n k) : ℕ := r.elim (fun e=>if widthKind e then 2 else 1) (fun _=>1)

/-- Only the two real radius roles have two chronological occurrences. -/
theorem length_menu (horizontal : H→DistinctPair C) (extra : E→DistinctPair (ColumnSite C k))
    (place : Ball×ColumnSite C k↪Fin K) (u : Ball) (primary : R→Fin N)
    (mate : C→Fin k→Fin N) (tree : TreeLink n k→Fin N) (r : R⊕TreeLink n k) :
    (Sum.elim (links horizontal extra place u primary mate) (fun j=>[tree j]) r).length=menuLen r := by
  rcases r with r|j
  · change (links _ _ _ _ _ _ r).length=_
    dsimp only [links]
    split <;> cases r <;> simp [forward,menuLen,widthKind]
  · rfl

def orderedWord (a b : Expr) (right : Bool) (x y : Expr) : Expr :=
  .branch .lt a b (if right then y else x) (if right then x else y)

theorem ordered_eval {W : ℕ} (a b x y : Expr) (m : Memory W) (r : Word W) {l h : Fin K}
    (la : a.eval m r=(l.val : Word W)) (hb : b.eval m r=(h.val : Word W)) (room : K≤2^W)
    (right : Bool) : (orderedWord a b right x y).eval m r=
      (if l<h then (if right then y else x) else (if right then x else y)).eval m r := by
  have bound : ((l.val : Word W)<(h.val : Word W))↔l<h := by
    change (l.val : Word W).val<(h.val : Word W).val ↔ l.val<h.val
    rw [Fin.val_cast_of_lt (l.isLt.trans_le room),Fin.val_cast_of_lt (h.isLt.trans_le room)]
  by_cases order : l<h <;> simp [orderedWord,Expr.eval,Comparison.test,la,hb,bound,order]

/-- The source and target of each local site are revealed by one genuine
mounted-site expression. Reversing a sorted catalyst flips its two
actual RAM rows; every other shape uses only its primary row. -/
def hopWord (horizontal : H→DistinctPair C) (extra : E→DistinctPair (ColumnSite C k))
    (site : ColumnSite C k→Expr) (primary : R→Expr) (mate : C→Fin k→Expr) :
    R→ℕ→Expr
  | .catalyst c a,j=>
    let endp:=ColumnWires.ends horizontal extra (.catalyst c a)
    orderedWord (site endp.left) (site endp.right) (decide (j≠0)) (primary (.catalyst c a)) (mate c a)
  | r,_=>primary r

theorem hop_eval {W : ℕ} (horizontal : H→DistinctPair C) (extra : E→DistinctPair (ColumnSite C k))
    (place : Ball×ColumnSite C k↪Fin K) (u : Ball) (site : ColumnSite C k→Expr)
    (pr : R→Fin N) (ma : C→Fin k→Fin N) (primary : R→Expr) (mate : C→Fin k→Expr)
    (val : Fin N→Word W) (m : Memory W) (z : Word W) (room : K≤2^W)
    (placed : ∀x,(site x).eval m z=((place (u,x)).val : Word W))
    (read : ∀e,(primary e).eval m z=val (pr e)) (mateRead : ∀c a,(mate c a).eval m z=val (ma c a))
    (r : R) (q : Fin (links horizontal extra place u pr ma r).length) :
    (hopWord horizontal extra site primary mate r q.val).eval m z=
      val ((links horizontal extra place u pr ma r).get q) := by
  have bounded (r : R) : (links horizontal extra place u pr ma r).length=(if widthKind r then 2 else 1) :=
    length_menu (n:=0) horizontal extra place u pr ma (fun _=>pr r) (.inl r)
  have lookup (xs : List (Fin N)) (i : Fin xs.length) (fallback : Fin N) :
      xs.get i=xs[i.val]?.getD fallback := by
    simp only [List.getElem?_eq_getElem i.isLt,Option.getD_some,List.get_eq_getElem]
  have small : q.val<(if widthKind r then 2 else 1) := q.isLt.trans_le (bounded r).le
  rw [lookup _ q (pr r)]
  generalize q.val = i at small ⊢
  have single (rr : R) (one : forward pr ma rr=[pr rr]) :
      (links horizontal extra place u pr ma rr)[0]?.getD (pr rr)=pr rr := by
    dsimp only [links]
    split <;> simp [one]
  cases r with
  | catalyst c a =>
    have two : i=0 ∨ i=1 := by simp only [widthKind,ite_true] at small;omega
    let ep:=ColumnWires.ends horizontal extra (.catalyst c a)
    have actual : links horizontal extra place u pr ma (.catalyst c a)=
        if place (u,ep.left)<place (u,ep.right) then [pr (.catalyst c a),ma c a]
        else [ma c a,pr (.catalyst c a)] := by
      dsimp only [links,ep,forward]
      split <;> rfl
    change (orderedWord (site ep.left) (site ep.right) _ _ _).eval m z=_
    rw [ordered_eval _ _ _ _ m z (placed ep.left) (placed ep.right) room,actual]
    by_cases cmp : place (u,ep.left)<place (u,ep.right)
    all_goals rcases two with h|h <;> simp [h,cmp,read,mateRead]
  | radius | cross | horizontal | extra =>
    have zero : i=0 := by simp only [widthKind,Bool.false_eq_true,ite_false] at small;omega
    rw [zero,single _ rfl]
    exact read _

variable {B A : Type} [Fintype A] [Fintype B]
local notation "PR" => ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k

/-- The retained input bypasses the paid-row chart. All paid rows use
their actual global ID, offset by the retained-bank length. -/
def readPrimary (stored : A→Expr) (shift : ℕ) (paid : PR→Expr) : PR→Expr
  | .extra (.inl a)=>stored a
  | r=>PacketScan.add (.lit shift) (paid r)

omit [Fintype A] [Fintype B] in
theorem read_primary {w : ℕ} (b : Board) (shift : ℕ) (stored : A→Expr) (paid : PR→Expr)
    (old : A→Fin (shift+b.rows)) (idx : PR→Fin b.rows) (m : Memory w) (reg : Word w)
    (former : ∀a,(stored a).eval m reg=((old a).val : Word w))
    (actual : ∀r,paidRole r→(paid r).eval m reg=((idx r).val : Word w)) (r : PR) :
    (readPrimary stored shift paid r).eval m reg=
      ((primaryRow (b:=b) old (Fin.natAdd shift) idx r).val : Word w) := by
  have atPaid (rr : PR) (good : paidRole rr) :
      (PacketScan.add (.lit shift) (paid rr)).eval m reg=((Fin.natAdd shift (idx rr)).val : Word w) := by
    rw [PacketScan.add_eval,actual rr good]
    simp [Expr.eval,Nat.cast_add,Fin.natAdd]
  cases r with
  | catalyst c j=>exact atPaid _ trivial
  | radius c j a=>exact atPaid _ trivial
  | horizontal x l=>exact atPaid _ trivial
  | cross c a l r=>exact atPaid _ trivial
  | extra e=>cases e with
    | inl a=>exact former a
    | inr b=>exact atPaid _ trivial

end Hierarchy.WireTelescope.StripPaths

end
end OAI
