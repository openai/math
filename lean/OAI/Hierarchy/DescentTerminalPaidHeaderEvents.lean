import OAI.Hierarchy.DescentTerminalSocketWidths
import OAI.Hierarchy.DescentTerminalSpanRead

namespace OAI
/-! # Deciding one header event on each paid row using genuine endpoint intervals -/
namespace Hierarchy.DescentTerminalPaidHeaderEvents
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalHeaderSockets
open scoped Classical Fin.CommRing
noncomputable section

inductive Column where | active | mode | source
  deriving DecidableEq
def locate {I : Type} (size:I→ℕ) : List I→ℕ→Option (I×ℕ)
  | [],_=>none
  | j::rest,r=>if r<size j then some (j,r) else locate size rest (r-size j)
def number {d:ℕ} (c:Column) (first:Fin d→ℕ) (hit:Option (Fin d×ℕ)) : ℕ := hit.elim 0 fun x=>
  match c with | .active=>1 | .mode=>if x.1.val=0 then 1 else 0 | .source=>first x.1+x.2

def choose {d:ℕ} (c:Column) (width begin_:Fin d→Expr) : List (Fin d)→Expr→Expr
  | [],_=>.lit 0
  | j::js,r=>
      let hit:=match c with | .active=>.lit 1 | .mode=>.lit (if j.val=0 then 1 else 0)
                            | .source=>.op .add (begin_ j) r
      .branch .lt r (width j) hit (choose c width begin_ js (.op .sub r (width j)))

theorem choose_read {d w:ℕ} (c:Column) (width begin_:Fin d→Expr) (size first:Fin d→ℕ) (m:Memory w) (i:Word w)
    (sw:∀j,size j<2^w) (earned:∀j,(width j).eval m i=(size j:Word w) ∧ (begin_ j).eval m i=(first j:Word w))
    (ls:List (Fin d)) (r:Expr) (k:ℕ) (rk:r.eval m i=(k:Word w)) (kw:k<2^w) :
    (choose c width begin_ ls r).eval m i=(number c first (locate size ls k):Word w) := by
  induction ls generalizing r k with
  | nil=>rfl
  | cons j js ih=>
    by_cases hit:k<size j
    · cases c <;> simp [choose,locate,hit,number,Expr.eval,RowOp.opcode,BinaryOp.eval,DescriptorExpr.Comparison.test,rk,
        (earned j).1,(earned j).2,Fin.lt_def,Fin.val_cast_of_lt kw,Fin.val_cast_of_lt (sw j),Nat.cast_add]
    · have ge:size j≤k:=Nat.le_of_not_gt hit
      have diff:(Expr.op .sub r (width j)).eval m i=((k-size j:ℕ):Word w):=by
        simp [Expr.eval,RowOp.opcode,BinaryOp.eval,rk,(earned j).1,Nat.cast_sub ge]
      change (if DescriptorExpr.Comparison.lt.test (r.eval m i) ((width j).eval m i) then _ else
        (choose c width begin_ js (.op .sub r (width j))).eval m i)=_
      simp [DescriptorExpr.Comparison.test,Fin.lt_def,rk,(earned j).1,Fin.val_cast_of_lt kw,Fin.val_cast_of_lt (sw j),hit,
        locate,ih _ _ diff ((Nat.sub_le ..).trans_lt kw)]

structure Inputs where
  sockets : Layout
  alive : Bank
  owner : Bank
  localRow : Bank

def expr (I:Inputs) (H D:ℕ) (c:Column) : Expr :=
  let v:=Expr.lookup I.owner .row
  .branch .eq (.lookup I.alive .row) (.lit 0) (.lit 0)
    (choose c (amount I.sockets H D v) (head I.sockets H D v) (List.finRange (D+1)) (.lookup I.localRow .row))

variable {H D W w n : ℕ} (I:Inputs) (R:Fin H→Fin D→Option (Fin H))
    (m:Memory w) (pos:2<2^w) (high:H<2^w) (area:H*D<2^w)
    (roster:∀(v:Fin H) (j:Fin D),I.sockets.roster.read m ((v.val*D+j.val:ℕ):Word w)=(DescentPackedColony.target (R v j):Word w))
    (cf pf:ℕ→ℕ) (c₀:cf 0=0) (p₀:pf 0=0) (cm:Monotone cf) (pm:Monotone pf)
    (cable:∀j:Fin (H*D),I.sockets.cablePrefix.read m (j.val:Word w)=(cf (j.val+1):Word w))
    (ext:∀j:Fin H,I.sockets.publicPrefix.read m (j.val:Word w)=(pf (j.val+1):Word w))
local notation "width" v => fun j=>endAt R v cf pf j-origin R v cf pf j
def picked (v:Fin H) (r:ℕ) := locate (width v) (List.finRange (D+1)) r
def result (c:Column) (span:Option (Fin H×Fin W)) := span.elim 0 fun vr=>
  number c (origin R vr.1 cf pf) (picked R cf pf vr.1 vr.2.val)

include pos high area roster c₀ p₀ cm pm cable ext in
theorem expr_read (c:Column) (s:Option (Fin H×Fin W)) (wFit:W≤2^w)
    (small:∀v j,endAt R v cf pf j-origin R v cf pf j<2^w)
    (i:Fin n) (alive:I.alive.read m (i.val:Word w)=((if s.isSome then 1 else 0:ℕ):Word w))
    (whereAt:∀(v:Fin H) (r:Fin W),s=some (v,r)→
      I.owner.read m (i.val:Word w)=(v.val:Word w) ∧ I.localRow.read m (i.val:Word w)=(r.val:Word w)) :
    (expr I H D c).eval m (i.val:Word w)=(result R cf pf c s:Word w) := by
  cases s with
  | none=>simp [expr,Expr.eval,alive,DescriptorExpr.Comparison.test,result]
  | some vr=>
    obtain ⟨v,r⟩:=vr
    obtain ⟨h,rk⟩:=whereAt v r rfl
    let x:=Expr.lookup I.owner .row
    have hv:x.eval m (i.val:Word w)=(v.val:Word w):=h
    have bytes (j:Fin (D+1)):=read_socket m (i.val:Word w) pos I.sockets R v x hv high area roster cf pf c₀ p₀ cable ext j cm pm
    have ne:(1:Word w)≠0:=by
      let : Nontrivial (Word w) := Fin.nontrivial_iff_two_le.mpr pos.le
      exact one_ne_zero
    change (if DescriptorExpr.Comparison.eq.test (I.alive.read m (i.val:Word w)) 0 then 0 else
      (choose c (amount I.sockets H D x) (head I.sockets H D x) (List.finRange (D+1)) (.lookup I.localRow .row)).eval m _)=_
    rw [alive]
    simp only [Option.isSome_some,ite_true,Nat.cast_one,DescriptorExpr.Comparison.test,beq_iff_eq,ite_eq_right ne]
    exact choose_read c _ _ (width v) _ m _ (small v) (fun j=>⟨(bytes j).2,(bytes j).1⟩) _ _ _ rk (r.isLt.trans_le wFit)

end
end Hierarchy.DescentTerminalPaidHeaderEvents

end OAI
