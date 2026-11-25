import OAI.Hierarchy.DescentRosterExpressionPrice
import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Publishing compact sorted peer and hub columns from the actual reset directory -/
namespace Hierarchy.DescentCompactVenuePeers
open DescentPackedColony DescentSortedRoster DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

structure Inputs where
  count : Bank
  inverse : Bank
  forward : Bank
  neighbor : Fin 3→Bank

def span (rows:ℕ):=2^Nat.clog 2 (rows+1)
def roots (base R:ℕ):Bank:=⟨base,Nat.clog 2 (R+1)⟩
def hosts (base R H:ℕ):Bank:=⟨base+span R,Nat.clog 2 (3*H+1)⟩
def slots (base R H:ℕ):Bank:=⟨(hosts base R H).base+span (3*H),Nat.clog 2 (3*H+1)⟩
def peers (base R H:ℕ):Bank:=⟨(slots base R H).base+span (3*H),Nat.clog 2 (3*H+1)⟩
def hubs (base R H:ℕ):Bank:=⟨(peers base R H).base+span (3*H),Nat.clog 2 (H+1)⟩
def roof (base R H:ℕ):=(hubs base R H).base+span H
theorem shift (base R H:ℕ):roof base R H=base+roof 0 R H:=by simp [roof,hubs,peers,slots,hosts,Nat.add_assoc]

def labels (R H:ℕ) (tag:ℕ→Bool)(i:ℕ):ℕ:=
  if i<span R then (tag i).toNat else if i<span R+span (3*H) then (i-span R)/3 else (i-(span R+span (3*H)))%3

def compact (B:Inputs)(R H:ℕ)(h:Expr)(j:Fin 3):Expr:=
  let x:=Expr.lookup (B.neighbor j) (.lookup B.inverse h)
  .branch .lt h (.lookup B.count (.lit 0)) (.branch .lt x (.lit R) (.lookup B.forward x) (.lit H)) (.lit H)

def entry (B:Inputs)(base R H:ℕ):Expr:=
  let h:=Expr.lookup (hosts base R H) .row
  let s:=Expr.lookup (slots base R H) .row
  let e (j:Fin 3):=pick (compact B R H h) (.lit j.val) H (List.finRange 3)
  .branch .eq s (.lit 0) (e 0) (.branch .eq s (.lit 1) (e 1) (e 2))

def flag (B:Inputs)(base R:ℕ):Expr:=
  .branch .lt .row (.lookup B.count (.lit 0)) (.lookup (roots base R) (.lookup B.inverse .row)) (.lit 0)

def book (_base R H:ℕ):=span R+2*span (3*H)

def program (B:Inputs)(base R H w:ℕ)(tag:ℕ→Bool):=
  ((DescentStaticWordColumn.program w base (labels R H tag) (book base R H)).seq
    (scan w (peers base R H).base (H*3) (entry B base R H))).seq
    (scan w (hubs base R H).base H (flag B base R))

def image (B:Inputs)(base R H:ℕ)(tag:ℕ→Bool){w:ℕ}(m:Memory w):=
  let fixed:=DescentStaticWordColumn.image base (labels R H tag) m (book base R H)
  let published:=ProtocolRAM.image (peers base R H).base (H*3) (entry B base R H) fixed
  ProtocolRAM.image (hubs base R H).base H (flag B base R) published

def ticks (B:Inputs)(base R H:ℕ):=(4+10*book base R H+(4+H*3*(2*(entry B base R H).work+4)))+
  (4+H*(2*(flag B base R).work+4))

private def staticPhase (base w n:ℕ)(label:ℕ→ℕ):NativePhase w:=
  ⟨DescentStaticWordColumn.program w base label n,4+10*n,fun m=>DescentStaticWordColumn.image base label m n,
    DescentStaticWordColumn.cheap w base label n⟩

private def scanPhase (base w n:ℕ)(e:Expr):NativePhase w:=
  ⟨scan w base n e,4+n*(2*e.work+4),ProtocolRAM.image base n e,scan_cheap w base n e⟩

def phase (B:Inputs)(base R H w:ℕ)(tag:ℕ→Bool):NativePhase w:=
  ((staticPhase base w (book base R H) (labels R H tag)).seq
    (scanPhase (peers base R H).base w (H*3) (entry B base R H))).seq
    (scanPhase (hubs base R H).base w H (flag B base R))

structure Room (B:Inputs)(base w:ℕ):Prop where
  count : B.count.Fits w base
  inverse : B.inverse.Fits w base
  forward : B.forward.Fits w base
  neighbor : ∀j,(B.neighbor j).Fits w base

private theorem length_le (n:ℕ):n ≤ span n:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
private theorem auxFits {w:ℕ} {v:Bank} {l u:ℕ} (fit:v.Fits w l)(b:l≤u):v.Fits w u:=
  ⟨fit.1,fit.2.1,fit.2.2.trans b⟩

theorem any (B:Inputs)(base R H w:ℕ)(tag:ℕ→Bool)(m:Memory w)(fit:Room B base w)
    (space:roof base R H<2^w):
    (phase B base R H w tag).Runs m ∧ ∀x,x<base ∨ roof base R H≤x→image B base R H tag m x=m x:=by
  let p:=peers base R H
  let z:=hubs base R H
  let n:=book base R H
  let current:=DescentStaticWordColumn.image base (labels R H tag) m n
  have prior:base+n=p.base:=by simp [p,n,book,peers,slots,hosts];omega
  have gap₀:p.base+H*3≤z.base:=Nat.add_le_add_left (by simpa only [Nat.mul_comm H 3] using length_le (3*H)) _
  have gap₁:z.base+H≤roof base R H:=Nat.add_le_add_left (length_le _) _
  have end₀:=gap₀.trans_lt ((Nat.le_add_right _ H).trans_lt (gap₁.trans_lt space))
  have earlier:base≤p.base:=(Nat.le_add_right ..).trans_eq prior
  have fitBank (b:Bank) (start:b.base+b.size≤p.base):b.Fits w p.base:=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (start.trans_lt ((Nat.le_add_right ..).trans_lt end₀)),start⟩
  have fitRoot:(roots base R).Fits w p.base:=fitBank _ ((Nat.le_add_right _ (span (3*H))).trans (Nat.le_add_right _ (span (3*H))))
  have fitHost:(hosts base R H).Fits w p.base:=fitBank _ (Nat.le_add_right _ (span (3*H)))
  have fitSlot:(slots base R H).Fits w p.base:=fitBank _ (by simp [span,Bank.size,p,peers,slots,hosts])
  have he:(entry B base R H).Fits w p.base:=by
    have cells (j:Fin 3):(compact B R H (.lookup (hosts base R H) .row) j).Fits w p.base:=by
      have hh:(Expr.lookup (hosts base R H) .row).Fits w p.base:=⟨fitHost,trivial⟩
      have xx:(Expr.lookup (B.neighbor j) (.lookup B.inverse (.lookup (hosts base R H) .row))).Fits w p.base:=
        ⟨auxFits (fit.neighbor j) earlier,auxFits fit.inverse earlier,hh⟩
      exact ⟨hh,⟨auxFits fit.count earlier,trivial⟩,⟨xx,trivial,⟨auxFits fit.forward earlier,xx⟩,trivial⟩,trivial⟩
    have term (i:Fin 3):=(pick_lit_fits _ cells i.val H)
    exact ⟨⟨fitSlot,trivial⟩,trivial,term 0,⟨⟨fitSlot,trivial⟩,trivial,term 1,term 2⟩⟩
  have later:p.base≤z.base:=(Nat.le_add_right ..).trans gap₀
  have hz:(flag B base R).Fits w z.base:=
    ⟨trivial,⟨auxFits fit.count (earlier.trans later),trivial⟩,⟨auxFits fitRoot later,auxFits fit.inverse (earlier.trans later),trivial⟩,trivial⟩
  let stage₀:=staticPhase base w n (labels R H tag)
  let stage₁:=scanPhase p.base w (H*3) (entry B base R H)
  let stage₂:=scanPhase z.base w H (flag B base R)
  have bookRun:stage₀.Runs m:=DescentStaticWordColumn.mount base n (labels R H tag) m (prior.le.trans_lt ((Nat.le_add_right ..).trans_lt end₀))
  have peersRun:stage₁.Runs (stage₀.image m):=scan_exec p.base (H*3) (entry B base R H) current he end₀
  have hubRun:stage₂.Runs (stage₁.image (stage₀.image m)):=scan_exec z.base H (flag B base R) (ProtocolRAM.image p.base (H*3) (entry B base R H) current) hz (gap₁.trans_lt space)
  refine ⟨(stage₀.seq stage₁).seq_runs stage₂ m (stage₀.seq_runs stage₁ m bookRun peersRun) hubRun,?_⟩
  intro x side
  have hubTop:z.base≤roof base R H:=(Nat.le_add_right ..).trans gap₁
  have peerTop:p.base+H*3≤roof base R H:=gap₀.trans hubTop
  have bookTop:base+n≤roof base R H:=prior.le.trans (later.trans hubTop)
  have hubOut:x<z.base ∨ z.base+H≤x:=side.imp (fun lo=>lo.trans_le (earlier.trans later)) (fun hi=>gap₁.trans hi)
  have peerOut:x<p.base ∨ p.base+H*3≤x:=side.imp (fun lo=>lo.trans_le earlier) (fun hi=>peerTop.trans hi)
  have fixedOut:x<base ∨ base+n≤x:=side.imp_right (fun hi=>bookTop.trans hi)
  exact (ProtocolRAMGeneratedWrite.frame_image z.base H (flag B base R)
    (stage₁.image (stage₀.image m)) x hubOut).trans
    ((ProtocolRAMGeneratedWrite.frame_image p.base (H*3) (entry B base R H) current x peerOut).trans
      (DescentStaticWordColumn.frame base n (labels R H tag) m x fixedOut))

end
end Hierarchy.DescentCompactVenuePeers

end OAI
