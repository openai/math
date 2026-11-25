import OAI.Hierarchy.DescentMeasuredPortTapes
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Constant instruction passes for the live/depth/gain reset measurement rows -/
namespace Hierarchy.DescentMeasuredHeader
open DescentMeasuredWeights DescentPackedExchange DescentGL ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {H k Δ w : ℕ}
local notation "R" => Rows H k Δ
local notation "N" => H*(k+1)+H*Δ
local notation "ord" => rowOrd H k Δ

inductive Field | live | depth | gain
structure Tape where
  tag : Bank
  owner : Bank
  offset : Bank
  tariff : Bank
  depth : Bank
  neighbor : Bank

def owner : R→Fin H := Sum.elim Prod.fst Prod.fst
def tag : R→ℕ := Sum.elim (fun _=>0) (fun _=>1)
def arg : R→ℕ := Sum.elim (fun s=>s.2.val) (fun p=>(slot H Δ p).val)
def tariff (f B K : ℕ) : R→ℕ := Sum.elim (fun s=>2^f*B*(4*2^((s.2.val+7)/8))) (fun _=>2^f*B*K^2)

def isLive (b : Fin H→ℕ) (next : Port H Δ→Option (Fin H)) : R→ℕ
  | .inl (v,q)=>if b v+q.val≤k then 1 else 0
  | .inr p=>if (next p).isSome then 1 else 0

def value (b : Fin H→ℕ) (next : Port H Δ→Option (Fin H)) (f B K : ℕ) : Field→R→ℕ
  | .depth=>realDepth b next
  | .gain=>realGain b next f B K
  | .live=>isLive b next

def contents (L : Tape) (b : Fin H→ℕ) (next : Port H Δ→Option (Fin H)) (f B K : ℕ)
    (m : Memory w) : Prop :=
  (∀i:R,m (L.tag.base+(ord i).val)=(tag i:Word w)) ∧
  (∀i:R,m (L.owner.base+(ord i).val)=((owner i).val:Word w)) ∧
  (∀i:R,m (L.offset.base+(ord i).val)=(arg i:Word w)) ∧
  (∀i:R,m (L.tariff.base+(ord i).val)=(tariff f B K i:Word w)) ∧
  (∀v:Fin H,m (L.depth.base+v.val)=(b v:Word w)) ∧
  (∀p:Port H Δ,m (L.neighbor.base+(slot H Δ p).val)=(target (next p):Word w))

def Tape.banks (L : Tape) := [L.tag,L.owner,L.offset,L.tariff,L.depth,L.neighbor]
def Tape.fixed (L : Tape) := [L.tag,L.owner,L.offset,L.tariff]
structure Fits (L : Tape) (w H k Δ out : ℕ) : Prop where
  fits : ∀z∈L.banks,z.Fits w out
  fixed : ∀z∈L.fixed,H*(k+1)+H*Δ≤z.size
  sites : H≤L.depth.size
  ports : H*Δ≤L.neighbor.size

def column (L : Tape) (H k : ℕ) (f : Field) : Expr :=
  let atRow := fun z=>Expr.lookup z .row
  let own:=Expr.lookup L.depth (atRow L.owner)
  let arg:=atRow L.offset
  let age:=Expr.op .add own arg
  let dst:=Expr.lookup L.neighbor arg
  let peer:=Expr.lookup L.depth dst
  let award:=atRow L.tariff
  let site:=match f with | .live=>.lit 1| .depth=>age| .gain=>award
  let contact:=match f with | .live=>.lit 1| .depth=>.branch .lt own peer peer own| .gain=>award
  .branch .eq (atRow L.tag) (.lit 0)
    (.branch .lt age (.lit (k+1)) site (.lit 0))
    (.branch .lt dst (.lit H) contact (.lit 0))

private theorem atBank {w out : ℕ} (b : Bank) (m : Memory w) (a : ℕ) (small : a<b.size)
    (fit : b.Fits w out) : b.read m (a:Word w)=m (b.base+a) := by
  simp [Bank.read,Fin.val_cast_of_lt (small.trans fit.2.1),Nat.mod_eq_of_lt small]

private theorem lt_cast {a b : ℕ} (ha : a<2^w) (hb : b<2^w) :
    (a:Word w)<(b:Word w) ↔ a<b := by
  change ((a:Word w).val<(b:Word w).val) ↔_
  rw [Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb]

theorem column_read (out : ℕ) (L : Tape) (safe : Fits L w H k Δ out)
    (b : Fin H→ℕ) (next : Port H Δ→Option (Fin H)) (f B K : ℕ) (m : Memory w)
    (head : contents (k := k) L b next f B K m) (size : H<2^w) (wide : 2*k+1<2^w)
    (bounded : ∀v,b v≤k) (field : Field) (i : R) :
    (column L H k field).eval m ((ord i).val:Word w)=(value b next f B K field i:Word w) := by
  obtain ⟨tg,ow,off,price,depth,peer⟩:=head
  have fixed (z) (hz : z∈L.fixed) : z.read m ((ord i).val:Word w)=m (z.base+(ord i).val) := by
    apply atBank z m _ ((ord i).isLt.trans_le (safe.fixed z hz))
    exact safe.fits _ (by simp only [Tape.fixed,List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with rfl|rfl|rfl|rfl <;>simp [Tape.banks])
  have source (v:Fin H) : L.depth.read m (v.val:Word w)=(b v:Word w) :=
    (atBank _ m _ (v.isLt.trans_le safe.sites) (safe.fits _ (by simp [Tape.banks]))).trans (depth v)
  have endpoint (p:Port H Δ) : L.neighbor.read m ((slot H Δ p).val:Word w)=(target (next p):Word w) :=
    (atBank _ m _ ((slot H Δ p).isLt.trans_le safe.ports) (safe.fits _ (by simp [Tape.banks]))).trans (peer p)
  have zeroOne : (0:Word w)≠1 := by
    intro he
    have hu:=congrArg Fin.val he
    have small : 1<2^w:=by omega
    have v : (1:Word w).val=1 := Fin.val_cast_of_lt small
    simp only [Fin.val_zero,v] at hu
    omega
  have fixedTag := (fixed L.tag (by simp [Tape.fixed])).trans (tg i)
  have fixedHome := (fixed L.owner (by simp [Tape.fixed])).trans (ow i)
  have fixedArg := (fixed L.offset (by simp [Tape.fixed])).trans (off i)
  have fixedPrice := (fixed L.tariff (by simp [Tape.fixed])).trans (price i)
  cases i with
  | inl s=>
    rcases s with ⟨v,q⟩
    have plus : b v+q.val<2^w:=by have:=bounded v;have:=q.isLt;omega
    have cmp:=lt_cast plus (show k+1<2^w by omega)
    by_cases active : b v+q.val≤k
    · cases field <;> simp [column,Expr.eval,RowOp.opcode,BinaryOp.eval,fixedTag,fixedHome,
        fixedArg,fixedPrice,tag,owner,arg,tariff,source,Comparison.test,←Nat.cast_add,cmp,
        active,value,realDepth,realGain,isLive]
    · cases field <;> simp [column,Expr.eval,RowOp.opcode,BinaryOp.eval,fixedTag,fixedHome,
        fixedArg,tag,owner,arg,source,Comparison.test,←Nat.cast_add,cmp,
        active,value,realDepth,realGain,isLive]
  | inr p=>
    cases h : next p with
    | none=>
      cases field <;> simp [column,Expr.eval,Comparison.test,fixedTag,fixedArg,tag,arg,endpoint,h,target,value,realDepth,realGain,isLive,Ne.symm zeroOne]
    | some u=>
      have cmp:=lt_cast (u.isLt.trans size) size
      have l : b p.1<2^w:=by have:=bounded p.1;omega
      have t : b u<2^w:=by have:=bounded u;omega
      by_cases order : b p.1<b u
      · cases field <;>simp [column,Expr.eval,Comparison.test,fixedTag,fixedHome,fixedArg,fixedPrice,
          tag,owner,arg,tariff,endpoint,h,target,value,realDepth,realGain,isLive,source,Ne.symm zeroOne,
          cmp,u.isLt,lt_cast l t,order,max_eq_right order.le]
      · cases field <;>simp [column,Expr.eval,Comparison.test,fixedTag,fixedHome,fixedArg,fixedPrice,
          tag,owner,arg,tariff,endpoint,h,target,value,realDepth,realGain,isLive,source,Ne.symm zeroOne,
          cmp,u.isLt,lt_cast l t,order,max_eq_left (le_of_not_gt order)]

theorem column_fits {out : ℕ} (L : Tape) (safe : Fits L w H k Δ out) (f : Field) : (column L H k f).Fits w out := by
  cases f <;> simp only [column,Expr.Fits]
  all_goals repeat' first | exact safe.fits _ (by simp [Tape.banks]) | trivial | constructor

theorem column_cost (L : Tape) (H k : ℕ) (f : Field) : (column L H k f).work≤128 := by
  cases f <;> simp only [column, Expr.work] <;> decide

end
end Hierarchy.DescentMeasuredHeader

end OAI
