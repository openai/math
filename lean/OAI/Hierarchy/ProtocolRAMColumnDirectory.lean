import OAI.Hierarchy.ProbeSiteAddress
import OAI.Hierarchy.ProtocolRAMBinarySpan
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Public conversion from physical sites and exterior ports to global columns -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets.ColumnROM
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {w h d k : ℕ}

def number (x : CoreBoard.Columns h d) := (Fintype.equivFin _ x).val
def exterior (h d : ℕ) (s : Bool) (p : Fin (2^h)) : CoreBoard.Columns h d :=
  if s then .inr (.inr p) else .inl p
def sites (base h d k : ℕ) : Bank := ⟨base,ProtocolRAMPurchaseSampler.bits (siteLast h d k+1)⟩
def outer (base h d k : ℕ) (s : Bool) : Bank :=
  ⟨base+(sites base h d k).size+(if s then 2^h else 0),h⟩
def words (h d k : ℕ) := (sites 0 h d k).size+2*2^h

private def colData (h d k : ℕ) (index : ℕ) : ℕ :=
  if fit : index< siteLast h d k+1 then number (((siteNumber h d k).symm ⟨index,fit⟩).1) else 0

private def put (b : Bank) (f : ℕ→ℕ) (m : Memory w) :=
  fillSegment b.base b.size (fun a=>(f (a-b.base):Word w)) m

private def exteriorData (h d : ℕ) (s : Bool) (a : ℕ) :=
  if inside : a<2^h then number (exterior h d s ⟨a,inside⟩) else 0

def load (base h d k : ℕ) (m : Memory w) : Memory w :=
  put (outer base h d k true) (exteriorData h d true)
    (put (outer base h d k false) (exteriorData h d false) (put (sites base h d k) (colData h d k) m))

private theorem put_at (b : Bank) (f : ℕ→ℕ) (m : Memory w) (i : ℕ) (hi : i<b.size) :
    put b f m (b.base+i)=(f i:Word w) := by
  have inside : b.base≤b.base+i ∧ b.base+i<b.base+b.size := ⟨Nat.le_add_right ..,Nat.add_lt_add_left hi _⟩
  simp only [put,fillSegment,ite_eq_left inside,Nat.add_sub_cancel_left]

private theorem put_outside (b : Bank) (f : ℕ→ℕ) (m : Memory w) (a : ℕ)
    (away : a<b.base ∨ b.base+b.size≤a) : put b f m a=m a := by
  have off : ¬(b.base≤a ∧ a<b.base+b.size):=by omega
  simp only [put,fillSegment,ite_eq_right off]

structure Resident (base h d k : ℕ) (m : Memory w) : Prop where
  site : ∀x : Site h d k,(sites base h d k).read m ((siteNumber h d k x).val:Word w)=(number x.1:Word w)
  port : ∀s (p : Fin (2^h)),(outer base h d k s).read m (p.val:Word w)=(number (exterior h d s p):Word w)

set_option maxHeartbeats 500000 in
theorem resident (base h d k : ℕ) (m : Memory w) (fit : siteLast h d k+1≤2^w) (root : 2^h≤2^w) :
    Resident base h d k (load base h d k m) := by
  let s:=sites base h d k
  let left:=outer base h d k false
  let right:=outer base h d k true
  have next : s.base+s.size=left.base:=by
    change base+s.size=base+s.size+(if false then 2^h else 0)
    simp
  have last : left.base+left.size=right.base:=by
    change (base+s.size+(if false then 2^h else 0))+2^h=base+s.size+(if true then 2^h else 0)
    simp
  constructor
  · intro x
    let u:=siteNumber h d k x
    have small : u.val<s.size:=u.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)
    have addr : s.base+u.val<left.base:=(Nat.add_lt_add_left small s.base).trans_le next.le
    have after : left.base≤right.base:=(Nat.le_add_right left.base left.size).trans last.le
    change load base h d k m (s.base+(u.val:Word w).val%s.size)=_
    rw [Fin.val_cast_of_lt (u.isLt.trans_le fit),Nat.mod_eq_of_lt small,load,
      put_outside right _ _ _ (.inl (addr.trans_le after)),
      put_outside left _ _ _ (.inl addr),put_at s _ _ _ small]
    have decoded : colData h d k u.val=number x.1:=by
      simp only [colData,dite_eq_left u.isLt]
      exact congrArg (fun v : Site h d k=>number v.1) ((siteNumber h d k).symm_apply_apply x)
    exact congrArg (fun v : ℕ=>(v:Word w)) decoded
  · intro side p
    have room:=p.isLt.trans_le root
    cases side
    · change load base h d k m (left.base+(p.val:Word w).val%left.size)=_
      have small : p.val<left.size:=p.isLt
      have addr : left.base+p.val<right.base:=(Nat.add_lt_add_left small left.base).trans_le last.le
      rw [Fin.val_cast_of_lt room,Nat.mod_eq_of_lt small,load,
        put_outside right _ _ _ (.inl addr),put_at left _ _ _ small]
      simp only [exteriorData,dite_eq_left p.isLt]
    · change load base h d k m (right.base+(p.val:Word w).val%right.size)=_
      have small : p.val<right.size:=p.isLt
      rw [Fin.val_cast_of_lt room,Nat.mod_eq_of_lt small,load,put_at right _ _ _ small]
      simp only [exteriorData,dite_eq_left p.isLt]

theorem frame (base h d k : ℕ) (m : Memory w) (a : ℕ) (outside : a< base ∨ base+words h d k≤ a) :
    load base h d k m a=m a := by
  let s:=sites base h d k
  let left:=outer base h d k false
  let right:=outer base h d k true
  have next : s.base+s.size=left.base:=by
    change base+s.size=base+s.size+(if false then 2^h else 0)
    simp
  have last : left.base+left.size=right.base:=by
    change (base+s.size+(if false then 2^h else 0))+2^h=base+s.size+(if true then 2^h else 0)
    simp
  have upper : right.base+right.size=base+words h d k := by
    change base+(sites 0 h d k).size+2^h+2^h=base+((sites 0 h d k).size+2*2^h)
    rw [two_mul];ac_rfl
  change a<s.base ∨ base+words h d k≤a at outside
  have hors (b : Bank) (lo : s.base≤b.base) (hi : b.base+b.size≤base+words h d k) :
      a<b.base ∨ b.base+b.size≤a :=outside.imp (fun x=>x.trans_le lo) (fun x=>hi.trans x)
  have l : s.base≤left.base:=(Nat.le_add_right s.base s.size).trans next.le
  have r : left.base≤right.base:=(Nat.le_add_right left.base left.size).trans last.le
  have e : right.base≤base+words h d k:=(Nat.le_add_right right.base right.size).trans upper.le
  rw [load,put_outside right _ _ _ (hors right (l.trans r) upper.le),
    put_outside left _ _ _ (hors left l (last.le.trans e)),
    put_outside s _ _ _ (hors s le_rfl (next.le.trans (r.trans e)))]

theorem Resident.frame {base h d k : ℕ} {m m' : Memory w} (seen : Resident base h d k m)
    (keep : ∀x,base≤ x → x< base+words h d k → m' x=m x) : Resident base h d k m' := by
  have read (b : Bank) (low : base≤ b.base) (high : b.base+b.size≤ base+words h d k) (r : Word w) :
      b.read m' r=b.read m r := by
    have rem := Nat.mod_lt r.val (Nat.two_pow_pos b.bits)
    change r.val%b.size< b.size at rem
    exact keep _ (by omega) (by omega)
  constructor
  · intro x
    exact (read (sites base h d k) le_rfl (by dsimp [sites,words,Bank.size];omega) _).trans (seen.site x)
  · intro s p
    apply Eq.trans _ (seen.port s p)
    apply read
    · exact (Nat.le_add_right base _).trans (Nat.le_add_right _ _)
    · cases s <;> dsimp [outer,sites,words,Bank.size] <;> omega

def project (base h d k : ℕ) (site : Expr) : Expr := .lookup (sites base h d k) site
theorem project_read (base h d k : ℕ) (site : Expr) (x : Site h d k) (m : Memory w) (r : Word w)
    (table : Resident base h d k m) (atSite : site.eval m r=((siteNumber h d k x).val:Word w)) :
    (project base h d k site).eval m r=(number x.1:Word w) := by
  simp only [project,Expr.eval,atSite,table.site]

theorem linear (h d k : ℕ) (hd : 1≤ d) : words h d k ≤ (2*siteFactor d k+4)*2^h := by
  have small := site_count h d k hd
  have cap := ProtocolRAMPurchaseSampler.span_le (siteLast h d k+1)
  have nonempty : 1≤2^h := Nat.two_pow_pos _
  change ProtocolRAMPurchaseSampler.span (siteLast h d k+1)+2*2^h≤ _
  rw [Nat.add_mul,Nat.mul_assoc];omega

end Hierarchy.ProtocolRAM.BoughtSockets.ColumnROM
end

end OAI
