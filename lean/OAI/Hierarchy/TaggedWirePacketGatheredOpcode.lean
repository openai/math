import OAI.Hierarchy.TaggedWirePacketShiftScan
import OAI.Hierarchy.TaggedWirePacketNeighbor
import OAI.Hierarchy.TaggedWirePacketShiftedRows
import OAI.Hierarchy.TaggedWirePacketSiteFields

namespace OAI
/-! # The real candidate program for shifted two-radius apertures at one public participant -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM TurnShelf ChosenPackets.RowRouting Tagged
open scoped Fin.CommRing Classical
variable {n t S m W D K : ℕ}

namespace Operands
variable {len : Fin n→ℕ} (o : Operands len)

def neighborSector (n : ℕ) (width nbr : Fin D→Expr) (seek : Expr) : Expr :=
  PacketScan.add (.lit (n*2)) (PacketNeighbor.selectExpr width nbr seek)

def gatheredLink (order : Fin t≃Σi,Fin (len i)) (width nbr : Fin D→Expr)
    (i : Fin n) (q : Fin (len i)) (here : Expr) (start : Bool) : Expr :=
  if start then PacketScan.add (o.aggregateStart order i q) (o.offset order i q) else
    .branch .eq (o.endSite i q false) here (neighborSector n width nbr (o.endSite i q true))
      (neighborSector n width nbr (o.endSite i q false))

def gatheredSide (order : Fin t≃Σi,Fin (len i)) (width nbr : Fin D→Expr) (i : Fin n) (j : ℕ) (right start : Bool) : Expr :=
  let atOld (b : Bool) := .lit (if start then 0 else (halfCode i b).val)
  if right then
    if q:j<len i then o.gatheredLink order width nbr i ⟨j,q⟩ (o.site i j) start else atOld true
  else
    if j=0 then atOld false else
      if q:j-1<len i then o.gatheredLink order width nbr i ⟨j-1,q⟩ (o.site i j) start else atOld false

def gatheredWords (order : Fin t≃Σi,Fin (len i)) (width nbr : Fin D→Expr) (i : Fin n) (j : ℕ) : Fin 7→Expr :=
  ![o.gatheredSide order width nbr i j false false,o.gatheredSide order width nbr i j true false,o.gatheredSide order width nbr i j false true,
    o.gatheredSide order width nbr i j true true,o.width i,o.site i j,.lit (3*i.val+j)]

end Operands

variable (old : Fin n→Chord S) (edge : Fin m→Chord S) (route : Fin n→List (Fin m))
    (bits : Fin n→ℕ) (order : Fin t≃Σi,Fin (route i).length)
    (o : Operands fun i=>(route i).length) (mem : Memory W) (row : Word W)
    (read : Reads old edge route bits o mem row) (sites : S≤2^W) (room : m≤2^W)
    {s : Fin S} {total : (portGraph S).Port s→ℕ}
    (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total) (width nbr : Fin D→Expr)

variable (mounted : NeighborReads mem row parts width nbr)
local notation "before" => fun (i : Fin n) (b : Bool)=>(halfCode i b).val
local notation "after" => fun (e : Fin m) (b : Bool)=>n*2+PacketNeighbor.index parts ((rowGraph edge).vertex e (!b))
local notation "shift" => AggregatePrefix.paidShift route bits order edge

include sites mounted in
theorem sector_gathered (seek : Expr) (target : Fin S) (atTarget : seek.eval mem row=(target.val:Word W)) :
    (Operands.neighborSector n width nbr seek).eval mem row=((n*2+PacketNeighbor.index parts target : ℕ):Word W) := by
  simp only [Operands.neighborSector,PacketScan.add_eval,PacketNeighbor.select_eval parts width nbr seek target
    mem row mounted.one sites atTarget mounted.fits mounted.widthAt mounted.siteAt,Expr.eval,Nat.cast_add]

include read sites room mounted

theorem gathered_link (i : Fin n) (q : Fin (route i).length) (j : ℕ) (start : Bool) :
    let v:=ShortWalk.site (rowGraph edge) (old i).1.1 (old i).1.2 (route i) j
    (o.gatheredLink order width nbr i q (o.site i j) start).eval mem row=
      ((if start then shift ((route i).get q)+NativeSlot.start route bits order i q else
        after ((route i).get q) (decide ((edge ((route i).get q)).1.1≠v))) : Word W) := by
  let v:=ShortWalk.site (rowGraph edge) (old i).1.1 (old i).1.2 (route i) j
  cases start
  · change (.branch .eq _ _ _ _ : Expr).eval mem row=_
    rw [PacketScan.eq_select mem row _ _ _ _ (read.low i q) (site_eval old edge route bits o mem row read sites i j)
      ((edge ((route i).get q)).1.1.isLt.trans_le sites) (v.isLt.trans_le sites)]
    let id := (route i).get q
    let lo := (edge id).1.1
    change (if lo.val=v.val then (Operands.neighborSector n width nbr (o.endSite i q true)).eval mem row
      else (Operands.neighborSector n width nbr (o.endSite i q false)).eval mem row)=
        ((n*2+PacketNeighbor.index parts ((rowGraph edge).vertex id (!decide (lo≠v))) : ℕ) : Word W)
    by_cases h : lo=v
    · have sign : decide (lo≠v)=false := by simp [h]
      rw [ite_eq_left (congrArg Fin.val h),sign]
      exact sector_gathered (n:=n) mem row sites parts width nbr mounted _ _ (read.high i q)
    · have sign : decide (lo≠v)=true := decide_eq_true h
      rw [ite_eq_right (fun eq=>h (Fin.ext eq)),sign]
      exact sector_gathered (n:=n) mem row sites parts width nbr mounted _ _ (read.low i q)
  · simp only [Operands.gatheredLink,ite_true,PacketScan.add_eval,
      aggregate_eval old edge route bits order o mem row read sites room,
      offset_eval old edge route bits order o mem row read room,Nat.cast_add]

theorem gathered_side (i : Fin n) (j : Fin ((route i).length+1)) (right start : Bool) :
    (o.gatheredSide order width nbr i j.val right start).eval mem row=
      ((if start then shiftedStart route bits order shift i (side old edge route ⟨i,j⟩ right)
        else refRole route before after i (side old edge route ⟨i,j⟩ right)) : Word W) := by
  have hop (q : Fin (route i).length):=gathered_link old edge route bits order o mem row read sites room parts width nbr mounted i q j.val start
  cases right <;> simp only [Operands.gatheredSide,side,vertex,Bool.false_eq_true,ite_false,ite_true]
  · by_cases lo:j.val=0
    · simp [lo,ShortWalk.left,refRole,shiftedStart,Expr.eval]
    · have h : j.val-1<(route i).length := by have := j.isLt;omega
      let q : Fin (route i).length := ⟨j.val-1,h⟩
      by_cases face : (edge ((route i).get q)).1.1 =
          ShortWalk.site (rowGraph edge) (old i).1.1 (old i).1.2 (route i) j.val
      all_goals
        have eq := hop q
        simp only [q,List.get_eq_getElem,rowGraph] at face eq
        cases start <;> simpa [lo,h,ShortWalk.left,shiftedStart,refRole,rowGraph,face,List.get_eq_getElem] using eq
  · by_cases h:j.val<(route i).length
    · let q : Fin (route i).length := ⟨j.val,h⟩
      by_cases face : (edge ((route i).get q)).1.1 =
          ShortWalk.site (rowGraph edge) (old i).1.1 (old i).1.2 (route i) j.val
      all_goals
        have eq := hop q
        simp only [q,List.get_eq_getElem,rowGraph] at face eq
        cases start <;> simpa [h,ShortWalk.right,shiftedStart,refRole,rowGraph,face,List.get_eq_getElem] using eq
    · simp [h,ShortWalk.right,shiftedStart,refRole,Expr.eval]

theorem gathered_words {count : ℕ} (short : ∀i,(route i).length≤2) (turns : Fin count≃Positions route)
    (r : Fin count) (f : Fin 7) :
    ((o.gatheredWords order width nbr (turns r).1 (turns r).2.val) f).eval mem row=
      (shiftedFields old edge route bits order shift before after short turns r f : Word W) := by
  rcases eqn:turns r with ⟨i,j⟩
  have sides (a b : Bool):=gathered_side old edge route bits order o mem row read sites room parts width nbr mounted i j a b
  fin_cases f <;> simp only [Operands.gatheredWords,shiftedFields,eqn] <;>
    first | exact sides false false | exact sides true false | exact sides false true | exact sides true true | exact read.width i | exact site_eval old edge route bits o mem row read sites i j.val |
      simp [StripPaths.positionSeat_apply,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm,Expr.eval]

theorem gathered_column {count : ℕ} (short : ∀i,(route i).length≤2) (turns : Fin count≃Positions route)
    (party : Expr) (real : party.eval mem row=(s.val : Word W)) (wide : ∀i,bits i<2^W) (slot : Fin (n*3)) (f : Fin 5) :
    (o.column (o.gatheredWords order width nbr) party (finProdFinEquiv (slot,f))).eval mem row=
      ProtocolRAMTurnShelf.entry (shiftedFields old edge route bits order shift before after short turns)
        (put old edge route bits order before after short turns) f (s,slot) := by
  apply column_eval old edge route bits short turns o mem row _ _ _ (fun _=>rfl) (fun _=>rfl) _ party s real read sites wide
  exact gathered_words old edge route bits order o mem row read sites room parts width nbr mounted short turns

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
