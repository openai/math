import OAI.Hierarchy.ProbePositiveSiteExpr
import OAI.Hierarchy.ProbeReportPortProgram
import OAI.Hierarchy.ProbeReportLabels
import OAI.Hierarchy.ProbeSiteAddress
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # A permutation-independent ROM from packed live sockets to global site ordinals -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets.SiteROM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open ProtocolRAM TaggedShorterSupergroups CoreBoard
open scoped Fin.CommRing Classical
variable {w h W k attempts H : ℕ}

def code (dir : Directory (reserved h W (copies k attempts)) H) (g : Fin dir.groups) (s : Fin H) : ℕ :=
  ((publicSite dir (g,s)).map (fun v=>(siteNumber h (2^W) k v).val)).getD 0

/-- A single offset per group avoids multiplication by H in the native CPU. The
remaining cells name every public socket without inspecting the matching or
future marked path sets. -/
def mount (dir : Directory (reserved h W (copies k attempts)) H) (base : ℕ) (mem : Memory w) : Memory w :=
  fillSegment base (footprint dir.groups H) (fun a=>
    let i := a-base
    if i<dir.groups then ((i*H:ℕ):Word w) else
      let idx := i-dir.groups
      if hg : idx/H<dir.groups then
        if hs : idx%H<H then (code dir ⟨idx/H,hg⟩ ⟨idx%H,hs⟩:Word w) else 0
      else 0) mem

structure Resident (dir : Directory (reserved h W (copies k attempts)) H) (base : ℕ) (mem : Memory w) : Prop where
  offset : ∀g : Fin dir.groups,mem (base+g.val)=((g.val*H:ℕ):Word w)
  target : ∀(g : Fin dir.groups) (s : Fin H),mem (base+dir.groups+(g.val*H+s.val))=(code dir g s : Word w)

theorem resident (dir : Directory (reserved h W (copies k attempts)) H) (base : ℕ) (m : Memory w) :
    Resident dir base (mount dir base m) := by
  constructor
  · intro g
    have hi := g.isLt
    have fit : base≤base+g.val ∧ base+g.val<base+footprint dir.groups H := by unfold footprint;omega
    simp [mount,fillSegment,fit,hi]
  · intro g s
    have hH : 0<H := Nat.zero_lt_of_lt s.isLt
    have last := Nat.mul_le_mul_right H g.isLt
    rw [Nat.succ_mul] at last
    have len : g.val*H+s.val<dir.groups*H := by have := s.isLt;omega
    have fit : base≤base+dir.groups+(g.val*H+s.val) ∧
        base+dir.groups+(g.val*H+s.val)<base+footprint dir.groups H := by unfold footprint;omega
    have div : (g.val*H+s.val)/H=g.val := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hH,Nat.div_eq_of_lt s.isLt,Nat.zero_add]
    have rem : (g.val*H+s.val)%H=s.val := Nat.mul_add_mod_of_lt s.isLt
    simp only [Nat.add_assoc] at fit
    simp only [mount,fillSegment,Nat.add_assoc,ite_eq_left fit,Nat.add_sub_cancel_left,
      show ¬dir.groups+(g.val*H+s.val)<dir.groups by omega,ite_false,div,rem,dite_eq_left g.isLt,dite_eq_left s.isLt]

theorem Resident.frame {dir : Directory (reserved h W (copies k attempts)) H} {base : ℕ} {m out : Memory w}
    (R : Resident dir base m) (same : ∀i,base ≤ i → i < base+footprint dir.groups H → out i=m i) :
    Resident dir base out := by
  constructor
  · intro g
    rw [same _ (by omega) (by unfold footprint; have := g.isLt;omega)]
    exact R.offset g
  · intro g s
    have hi:=Nat.mul_le_mul_right H g.isLt
    rw [Nat.succ_mul] at hi
    rw [same _ (by omega) (by unfold footprint;have := s.isLt;omega)]
    exact R.target g s

theorem Resident.read {dir : Directory (reserved h W (copies k attempts)) H} {base : ℕ} {m : Memory w}
    (R : Resident dir base m) (group slot : Expr) (row : Word w) (g : Fin dir.groups) (s : Fin H)
    (gFit : dir.groups≤2^w) (fit : dir.groups*H≤2^w)
    (groupAt : group.eval m row=(g.val:Word w)) (slotAt : slot.eval m row=(s.val:Word w)) :
    (siteExpr base dir.groups H group slot).eval m row=(code dir g s:Word w) := by
  have h := Nat.mul_le_mul_right H g.isLt
  rw [Nat.succ_mul] at h
  have key : g.val*H+s.val<dir.groups*H := by have := s.isLt;omega
  have header : (offsets base dir.groups).read m (g.val:Word w)=((g.val*H:ℕ):Word w) := by
    rw [Bank.read,show (offsets base dir.groups).size=ProtocolRAMPurchaseSampler.span dir.groups from rfl,
      Fin.val_cast_of_lt (g.isLt.trans_le gFit),
      Nat.mod_eq_of_lt (g.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _))]
    exact R.offset g
  change (sites base dir.groups H).read m ((.op .add (.lookup (offsets base dir.groups) group) slot : Expr).eval m row)=_
  simp only [Expr.eval,groupAt,slotAt,header,RowOp.opcode,BinaryOp.eval,←Nat.cast_add]
  rw [Bank.read,show (sites base dir.groups H).size=ProtocolRAMPurchaseSampler.span (dir.groups*H) from rfl,
    Fin.val_cast_of_lt (key.trans_le fit),
    Nat.mod_eq_of_lt (key.trans (ProtocolRAMPurchaseSampler.lt_span _))]
  exact R.target g s

/-- The input row may be a live π-dependent acquired chain. Its public decoding
table depends only on group shapes, layers and the native site numbering. -/
theorem actual (dir : Directory (reserved h W (copies k attempts)) H) (base : ℕ) (m : Memory w)
    (R : Resident dir base m) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts) (unique : Exclusive marked) (r : Row S π depth marked) (side : Bool)
    (group slot : Expr) (row : Word w) (gFit : dir.groups≤2^w) (fit : dir.groups*H≤2^w)
    (groupAt : group.eval m row=((placed S π depth marked unique dir (r,side)).1.val:Word w))
    (slotAt : slot.eval m row=((placed S π depth marked unique dir (r,side)).2.val:Word w)) :
    (siteExpr base dir.groups H group slot).eval m row=
      ((siteNumber h (2^W) k (geometry S π depth marked r side)).val:Word w) := by
  rw [R.read group slot row _ _ gFit fit groupAt slotAt]
  simp only [code,Prod.mk.eta,actual_site,Option.map_some,Option.getD_some]

/-- The input side is the public original-group number, CT input/output port, and
fixed socket tag. Both the supergroup and its packed position are evaluated by
the native key expression, without storing a per-permutation group table. -/
def atPort (base G H start oldGroups copies : ℕ) (group port tag : Expr) : Expr :=
  siteExpr base G H (.lookup (ProtocolRAMSupergroupDirectory.groupBank start oldGroups) group)
    (addressExpr copies 1 (ProtocolRAMSupergroupDirectory.offsetBank start oldGroups) group port tag)

theorem read_port {K : ℕ} (dir : Directory (reserved h W (copies k attempts)) H)
    (base start : ℕ) (numbers : Fin K ≃ AllGroups h (2^W)) (m : Memory w)
    (R : Resident dir base m) (header : ∀g,let r := ((numbers.symm g).val:Word w)
      (ProtocolRAMSupergroupDirectory.groupBank start K).read m r=((dir.group g).val:Word w) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank start K).read m r=(dir.base g:Word w))
    (x : StageColumns h (2^W) × Role k attempts) (group port tag : Expr) (row : Word w)
    (gFit : dir.groups≤2^w) (fit : dir.groups*H≤2^w)
    (grp : group.eval m row=((numbers.symm (owner x.1)).val:Word w))
    (inp : port.eval m row=((socketPort x.1).val:Word w))
    (role : tag.eval m row=((socketTag x.1 x.2).val:Word w)) :
    (atPort base dir.groups H start K (copies k attempts) group port tag).eval m row=
      ((siteNumber h (2^W) k (physicalSite x)).val:Word w) := by
  have groupAt : (Expr.lookup (ProtocolRAMSupergroupDirectory.groupBank start K) group).eval m row =
      ((packed dir x).1.val:Word w) := by
    simp only [Expr.eval,grp]
    exact (header (owner x.1)).1
  have slotAt : (addressExpr (copies k attempts) 1
      (ProtocolRAMSupergroupDirectory.offsetBank start K) group port tag).eval m row=((packed dir x).2.val:Word w) := by
    simp only [addressExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,eval_scale,grp,inp,role,(header (owner x.1)).2]
    change _=(((dir.base (owner x.1)+(offset x.1 x.2).val):ℕ):Word w)
    rw [offset_val]
    push_cast
    ring
  rw [atPort,R.read _ _ _ _ _ gFit fit groupAt slotAt]
  simp only [code,Prod.mk.eta,publicSite_packed,Option.map_some,Option.getD_some]

theorem catalogue_port {K : ℕ} (dir : Directory (reserved h W (copies k attempts)) H)
    (base start : ℕ) (numbers : Fin K≃AllGroups h (2^W)) (mem : Memory w)
    (R : Resident dir base mem) (header : ∀g,let r := ((numbers.symm g).val:Word w)
      (ProtocolRAMSupergroupDirectory.groupBank start K).read mem r=((dir.group g).val:Word w) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank start K).read mem r=(dir.base g:Word w))
    (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts) (unique : Exclusive marked) (r : Row S π depth marked) (side : Bool)
    (group port tag : Expr) (row : Word w) (gFit : dir.groups≤2^w) (fit : dir.groups*H≤2^w)
    (grp : group.eval mem row=((numbers.symm (owner (locate S π depth marked unique (r,side)).1)).val:Word w))
    (inp : port.eval mem row=((socketPort (locate S π depth marked unique (r,side)).1).val:Word w))
    (role : tag.eval mem row=((socketTag (locate S π depth marked unique (r,side)).1
      (locate S π depth marked unique (r,side)).2).val:Word w)) :
    (atPort base dir.groups H start K (copies k attempts) group port tag).eval mem row=
      ((siteNumber h (2^W) k (geometry S π depth marked r side)).val:Word w) := by
  let x := locate S π depth marked unique (r,side)
  have eq := actual_site (dir:=dir) (S:=S) (π:=π) (depth:=depth) (marked:=marked) (unique:=unique) r side
  change publicSite dir (packed dir x)=_ at eq
  rw [publicSite_packed,Option.some.injEq] at eq
  exact (read_port dir base start numbers mem R header x group port tag row gFit fit grp inp role).trans
    (congrArg (fun v=>((siteNumber h (2^W) k v).val:Word w)) eq)

theorem siteExpr_work (base G H : ℕ) (group slot : Expr) :
    (siteExpr base G H group slot).work=group.work+slot.work+11 := by
  simp only [siteExpr,Expr.work]
  omega

end Hierarchy.ProbeStage.ReportSockets.SiteROM
end

end OAI
