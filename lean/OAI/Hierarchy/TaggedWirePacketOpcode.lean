import OAI.Hierarchy.TaggedWirePacketOperands
import OAI.Hierarchy.TaggedWirePacketCodes
import OAI.Hierarchy.TaggedWirePacketTurnRows
import OAI.Hierarchy.TaggedWirePacketScan
import Mathlib.Data.List.Forall2

namespace OAI
/-! # Native header expressions for one fixed-shape strip packet -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM TurnShelf ChosenPackets.RowRouting
open scoped Fin.CommRing Classical

variable {n t S m W : ℕ}

namespace Operands
variable {len : Fin n→ℕ} (o : Operands len)

def site (i : Fin n) (j : ℕ) : Expr :=
  if j=0 then o.oldSite i false else if j=len i then o.oldSite i true else
    if h:0<len i then .branch .eq (o.endSite i ⟨0,h⟩ false) (o.oldSite i false)
      (o.endSite i ⟨0,h⟩ true) (o.endSite i ⟨0,h⟩ false) else o.oldSite i false

def key (order : Fin t≃Σi,Fin (len i)) (u : Fin t) := o.edge (order u).1 (order u).2

def sector (order : Fin t≃Σi,Fin (len i)) (i : Fin n) (q : Fin (len i)) (b : Bool) : Expr :=
  let x:=PacketScan.first (o.edge i q) (List.ofFn (o.key order))
  PacketScan.add (.lit (n*2)) (PacketScan.add (PacketScan.add x x) (.lit b.toNat))

def offset (order : Fin t≃Σi,Fin (len i)) (i : Fin n) (q : Fin (len i)) :=
  PacketScan.earlier (o.key order) (fun j=>o.width (order j).1) (o.edge i q) (order.symm ⟨i,q⟩).val

/-- Both edge signs are read using the current geometric site. -/
def linked (order : Fin t≃Σi,Fin (len i)) (i : Fin n) (q : Fin (len i)) (here : Expr) (start : Bool) : Expr :=
  if start then o.offset order i q else
    .branch .eq (o.endSite i q false) here (o.sector order i q false) (o.sector order i q true)

def sideWord (order : Fin t≃Σi,Fin (len i)) (i : Fin n) (j : ℕ) (right start : Bool) : Expr :=
  let atOld (b : Bool) := .lit (if start then 0 else (halfCode i b).val)
  if right then
    if q:j<len i then o.linked order i ⟨j,q⟩ (o.site i j) start else atOld true
  else
    if j=0 then atOld false else
      if q:j-1<len i then o.linked order i ⟨j-1,q⟩ (o.site i j) start else atOld false

def words (order : Fin t≃Σi,Fin (len i)) (i : Fin n) (j : ℕ) : Fin 7→Expr :=
  ![o.sideWord order i j false false,o.sideWord order i j true false,o.sideWord order i j false true,
    o.sideWord order i j true true,o.width i,o.site i j,.lit (3*i.val+j)]

end Operands

variable (old : Fin n→Chord S) (edge : Fin m→Chord S) (route : Fin n→List (Fin m))
    (bits : Fin n→ℕ) (order : Fin t≃Σi,Fin (route i).length)
    (o : Operands fun i=>(route i).length) (mem : Memory W) (row : Word W)
local notation "ids" => NativeSlot.edge route order
local notation "before" => fun (i : Fin n) (b : Bool)=>(halfCode i b).val
local notation "after" => PostCode.after ids n

variable (read : Reads old edge route bits o mem row) (sites : S≤2^W) (room : m≤2^W)
include read

include sites in
theorem site_eval (i : Fin n) (j : ℕ) : (o.site i j).eval mem row =
    ((ShortWalk.site (rowGraph edge) (old i).1.1 (old i).1.2 (route i) j).val : Word W) := by
  by_cases zero : j=0
  · simpa [Operands.site,ShortWalk.site,zero] using read.oldLo i
  by_cases last : j=(route i).length
  · simpa only [Operands.site,ShortWalk.site,ite_eq_right zero,ite_eq_left last] using read.oldHi i
  by_cases h:0<(route i).length
  · let q : Fin (route i).length:=⟨0,h⟩
    simp only [Operands.site,ShortWalk.site,ite_eq_right zero,ite_eq_right last,dite_eq_left h]
    have eq:=PacketScan.eq_select mem row (o.endSite i q false) (o.oldSite i false)
      (o.endSite i q true) (o.endSite i q false) (read.low i q) (read.oldLo i)
      ((edge ((route i).get q)).1.1.isLt.trans_le sites) ((old i).1.1.isLt.trans_le sites)
    rw [eq]
    let lo := (edge ((route i).get q)).1.1
    let hi := (edge ((route i).get q)).1.2
    let src := (old i).1.1
    change (if lo.val=src.val then (o.endSite i q true).eval mem row else (o.endSite i q false).eval mem row)=
      ((if lo=src then hi else lo).val : Word W)
    by_cases hit : lo=src
    · rw [ite_eq_left (congrArg Fin.val hit),ite_eq_left hit]
      exact read.high i q
    · rw [ite_eq_right (fun eq=>hit (Fin.ext eq)),ite_eq_right hit]
      exact read.low i q
  · simpa [Operands.site,ShortWalk.site,zero,last,h] using read.oldLo i

omit read in
private theorem occurrence_key (i : Fin n) (q : Fin (route i).length) :
    ids (order.symm ⟨i,q⟩)=(route i).get q :=
  congrArg (fun z : Σi,Fin (route i).length => (route z.1).get z.2)
    (order.apply_symm_apply ⟨i,q⟩)

include room in
theorem sector_eval (i : Fin n) (q : Fin (route i).length) (b : Bool) :
    (o.sector order i q b).eval mem row=(after ((route i).get q) b : Word W) := by
  let actual:=NativeSlot.edge route order
  let key:=(route i).get q
  have seen : ∃u,actual u=key := ⟨order.symm ⟨i,q⟩,occurrence_key route order i q⟩
  have inputs : (List.ofFn (o.key order)).Forall₂ (fun (a : Expr) (id : ℕ)=>a.eval mem row=(id : Word W) ∧ id<2^W)
      (List.ofFn (fun u=>(actual u).val)) := by
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro j bound other
    simpa [Operands.key,actual,NativeSlot.edge] using
      (show ∀v : Fin t,(o.key order v).eval mem row=((actual v).val : Word W) ∧ (actual v).val<2^W from
        fun v=>⟨read.key _ _,(actual v).isLt.trans_le room⟩) ⟨j,by simpa using bound⟩
  have first:=PacketScan.first_eval mem row (o.edge i q) (read.key i q) (key.isLt.trans_le room) _ _ inputs
  simp only [Operands.sector,PacketScan.add_eval,first,PostCode.after,halfCode_val,
    Nat.cast_add,Expr.eval,Nat.cast_mul,two_mul]
  exact congrArg (fun z : ℕ => (n : Word W)*2+((z : Word W)+z+b.toNat))
    (PostCode.first_live ids ((route i).get q) seen).symm

include room in
theorem offset_eval (i : Fin n) (q : Fin (route i).length) :
    (o.offset order i q).eval mem row=(NativeSlot.start route bits order i q : Word W) := by
  change (PacketScan.earlier (o.key order) (fun j=>o.width (order j).1) (o.edge i q)
    (order.symm ⟨i,q⟩).val).eval mem row=(TaggedShorterCommonScan.earlier ids
    (NativeSlot.amount route bits order) (order.symm ⟨i,q⟩).val (ids (order.symm ⟨i,q⟩)) : Word W)
  rw [occurrence_key route order i q]
  exact PacketScan.earlier_eval mem row _ _ _ ids _ _ room (fun u=>read.key _ _) (fun u=>read.width _)
    (read.key i q) _

include sites room

theorem linked_eval (i : Fin n) (q : Fin (route i).length) (j : ℕ) (start : Bool) :
    let v:=ShortWalk.site (rowGraph edge) (old i).1.1 (old i).1.2 (route i) j
    (o.linked order i q (o.site i j) start).eval mem row=
      ((if start then NativeSlot.start route bits order i q else
        after ((route i).get q) (decide ((edge ((route i).get q)).1.1≠v))) : Word W) := by
  let v:=ShortWalk.site (rowGraph edge) (old i).1.1 (old i).1.2 (route i) j
  cases start
  · change (.branch .eq _ _ _ _ : Expr).eval mem row=_
    rw [PacketScan.eq_select mem row _ _ _ _ (read.low i q) (site_eval old edge route bits o mem row read sites i j)
      ((edge ((route i).get q)).1.1.isLt.trans_le sites) (v.isLt.trans_le sites)]
    let lo := (edge ((route i).get q)).1.1
    change (if lo.val=v.val then (o.sector order i q false).eval mem row
      else (o.sector order i q true).eval mem row)=(after ((route i).get q) (decide (lo≠v)) : Word W)
    by_cases h : lo=v
    · have sign : decide (lo≠v)=false := by simp [h]
      rw [ite_eq_left (congrArg Fin.val h),sign]
      exact sector_eval old edge route bits order o mem row read room i q false
    · have sign : decide (lo≠v)=true := decide_eq_true h
      rw [ite_eq_right (fun eq=>h (Fin.ext eq)),sign]
      exact sector_eval old edge route bits order o mem row read room i q true
  · exact offset_eval old edge route bits order o mem row read room i q

theorem side_eval (i : Fin n) (j : Fin ((route i).length+1)) (right start : Bool) :
    (o.sideWord order i j.val right start).eval mem row=
      ((if start then refStart route bits order i (side old edge route ⟨i,j⟩ right)
        else refRole route before after i (side old edge route ⟨i,j⟩ right)) : Word W) := by
  have hop (q : Fin (route i).length):=linked_eval old edge route bits order o mem row read sites room i q j.val start
  cases right <;> simp only [Operands.sideWord,side,vertex,Bool.false_eq_true,ite_false,ite_true]
  · by_cases lo:j.val=0
    · simp [lo,ShortWalk.left,refRole,refStart,Expr.eval]
    · have h : j.val-1<(route i).length := by have := j.isLt;omega
      let q : Fin (route i).length := ⟨j.val-1,h⟩
      by_cases face : (edge ((route i).get q)).1.1 =
          ShortWalk.site (rowGraph edge) (old i).1.1 (old i).1.2 (route i) j.val
      all_goals
        have eq := hop q
        simp only [q,List.get_eq_getElem,rowGraph] at face eq
        cases start <;> simpa [lo,h,ShortWalk.left,refStart,refRole,rowGraph,face,List.get_eq_getElem] using eq
  · by_cases h:j.val<(route i).length
    · let q : Fin (route i).length := ⟨j.val,h⟩
      by_cases face : (edge ((route i).get q)).1.1 =
          ShortWalk.site (rowGraph edge) (old i).1.1 (old i).1.2 (route i) j.val
      all_goals
        have eq := hop q
        simp only [q,List.get_eq_getElem,rowGraph] at face eq
        cases start <;> simpa [h,ShortWalk.right,refStart,refRole,rowGraph,face,List.get_eq_getElem] using eq
    · simp [h,ShortWalk.right,refStart,refRole,Expr.eval]

theorem words_eval {count : ℕ} (short : ∀i,(route i).length≤2) (turns : Fin count≃Positions route)
    (r : Fin count) (f : Fin 7) :
    ((o.words order (turns r).1 (turns r).2.val) f).eval mem row=
      (fields old edge route bits order before after short turns r f : Word W) := by
  rcases eqn:turns r with ⟨i,j⟩
  have sides (a b : Bool):=side_eval old edge route bits order o mem row read sites room i j a b
  fin_cases f <;> simp only [Operands.words,fields,eqn] <;>
    first | exact sides false false | exact sides true false | exact sides false true | exact sides true true | exact read.width i | exact site_eval old edge route bits o mem row read sites i j.val |
      simp [StripPaths.positionSeat_apply,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm,Expr.eval]

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
