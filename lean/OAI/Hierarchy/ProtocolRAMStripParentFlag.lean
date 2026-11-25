import OAI.Hierarchy.ProtocolRAMStripEdgeSupport

namespace OAI
/-! # The local acquisition gate and the final catalogue read the same real saved flag -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe BoughtSockets PurchaseFrozen
open CatalogueRows StripDirectory PortPadding ReportSockets
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing Classical
variable {z W w k q depth : ℕ}
local notation "N" => Stages z (2^W)
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : Board)
variable (G : PortBanks ((c.inject+c.cool)*c.outerFuel))

theorem payload_edge_cases (p a : ℕ) (i : Fin D) (m : Memory w) (r : Word w) (room : b.rows<2^w) :
    b.CoreOrPad ((edge F (withPorts s c b G) b.rows (.outer p a) i).eval m r) := by
  let s':=withPorts s c b G
  by_cases inRange:i.val< P
  · let j : Fin P:=⟨i.val,inRange⟩
    have eq:inject (Nat.le_max_left P R) j=i:=Fin.ext rfl
    rw [←eq,payload_edge]
    exact ((payloadPortsAt s c G).primary_cases b ((Fintype.equivFin (PayloadRole N k)).symm j) m _ room).elim (fun answer=>answer)
      (fun ⟨empty,_⟩=>nomatch empty)
  · change b.CoreOrPad (((extend (s'.payloadEdge p a) (.lit b.rows) i).atRow _).eval m r)
    rw [extend_tail _ _ _ (Nat.le_of_not_gt inRange)]
    exact Or.inr (Fin.val_cast_of_lt room)

theorem purchased_edge_cases (p a j t : ℕ) (i : Fin D) (m : Memory w) (r : Word w) (room : b.rows<2^w) :
    let parent:=withPorts s c b G
    let ball:=(header F parent (.inner p a j t)).ballTerm.eval m r
    let raw:=(edge F parent b.rows (.inner p a j t) i).eval m r
    b.CoreOrPad raw ∨ raw=(b.originalProbe (G.directory.header z (2^W) k s.sampler.degree depth).ports (birth c p a) .row).eval m ball := by
  intro parent ball raw
  by_cases inRange:i.val< R
  · let v : Fin R:=⟨i.val,inRange⟩
    have eq:inject (Nat.le_max_right P R) v=i:=Fin.ext rfl
    have cooked : raw=((boughtPortsAt s c b G p a).primary b ((Fintype.equivFin (PurchasedRole depth k)).symm v)).eval m ball := by
      change (edge F parent b.rows (.inner p a j t) i).eval m r=_
      rw [←eq,purchased_edge];rfl
    rw [cooked]
    rcases (boughtPortsAt s c b G p a).primary_cases b ((Fintype.equivFin (PurchasedRole depth k)).symm v) m ball room with core|⟨origin,_,hit⟩
    · exact .inl core
    · exact .inr hit
  · left
    change b.CoreOrPad (((extend (parent.purchaseEdge p a j t) (.lit b.rows) i).atRow _).eval m r)
    rw [extend_tail _ _ _ (Nat.le_of_not_gt inRange)]
    exact Or.inr (Fin.val_cast_of_lt room)

theorem parent_flag (p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel) (j t : ℕ)
    (m out : Memory w) (r : Word w) (candidate : Fin (G.directory.header z (2^W) k s.sampler.degree depth).ports)
    (room : ((c.inject+c.cool)*c.outerFuel)≤2^w)
    (countFit : (G.directory.header z (2^W) k s.sampler.degree depth).ports≤2^w)
    (directory : (G.directory.header z (2^W) k s.sampler.degree depth).Loaded out)
    (source : b.bought.flag=G.directory.archived z (2^W) k s.sampler.degree depth G.directory.flagBase)
    (originBase : G.directory.flagBase (finProdFinEquiv (p,a))=(build F s (.outer p a) 0).board.purchaseOut)
    (size : (build F s (.outer p a) 0).market.rows=(G.directory.header z (2^W) k s.sampler.degree depth).ports)
    (ball : (header F s (.inner p a j t)).ballTerm.eval m r=(candidate.val:Word w))
    (persistent : m ((build F s (.outer p a) 0).board.purchaseOut+candidate.val)=
      out ((build F s (.outer p a) 0).board.purchaseOut+candidate.val)) :
    (retainedAt F s (.inner p a j t)).eval m r=b.bought.flag.eval out
      (((G.directory.header z (2^W) k s.sampler.degree depth).enum ⟨finProdFinEquiv (p,a),candidate⟩).val:Word w) := by
  let head:=G.directory.header z (2^W) k s.sampler.degree depth
  have live:candidate.val< head.ports:=candidate.isLt
  have read:=G.directory.archive_read z (2^W) k s.sampler.degree depth out directory room countFit G.directory.flagBase
    (finProdFinEquiv (p,a)) candidate
  rw [source,read,originBase]
  change m ((build F s (.outer p a) 0).board.purchaseOut+
    ((header F s (.inner p a j t)).ballTerm.eval m r).val%ProtocolRAMPurchaseSampler.span (build F s (.outer p a) 0).market.rows)=_
  rw [ball,Fin.val_cast_of_lt (live.trans_le countFit),size,Nat.mod_eq_of_lt (live.trans (ProtocolRAMPurchaseSampler.lt_span _))]
  exact persistent

/-- Every actual payload port, including padding, agrees with its terminal
catalogue lookup as soon as the underlying measured geometric ordinal agrees. -/
theorem outer_common (p a : ℕ) (i : Fin D) (m out : Memory w) (r r' : Word w)
    (other : Expr) (room : b.rows<2^w)
    (same : (edge F (withPorts s c b G) b.rows (.outer p a) i).eval m r=other.eval out r') :
    (id F (withPorts s c b G) b (.outer p a) i).eval m r=(b.commonID other).eval out r' :=
  congrArg (fun x=>(b.idBase:Word w)+x) (physicalEdge_core b _ _ _ m out r r' room same
    (payload_edge_cases F s c b G p a i m r room))

theorem inner_common (p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel) (j t : ℕ) (i : Fin D)
    (m out : Memory w) (r r' : Word w) (other : Expr)
    (candidate : Fin (G.directory.header z (2^W) k s.sampler.degree depth).ports)
    (recording : (G.directory.header z (2^W) k s.sampler.degree depth).count=b.boughtRows)
    (room : b.rows<2^w)
    (same : (edge F (withPorts s c b G) b.rows (.inner p a j t) i).eval m r=other.eval out r')
    (ball : (header F (withPorts s c b G) (.inner p a j t)).ballTerm.eval m r=(candidate.val:Word w))
    (archived : (retainedAt F (withPorts s c b G) (.inner p a j t)).eval m r=
      b.bought.flag.eval out (((G.directory.header z (2^W) k s.sampler.degree depth).enum
        ⟨finProdFinEquiv (p,a),candidate⟩).val:Word w)) :
    (id F (withPorts s c b G) b (.inner p a j t) i).eval m r=(b.commonID other).eval out r' := by
  apply congrArg (fun x=>(b.idBase:Word w)+x)
  rcases purchased_edge_cases F s c b G p a j t i m r room with core|birthRead
  · exact physicalEdge_core b _ _ _ m out r r' room same core
  · let head:=G.directory.header z (2^W) k s.sampler.degree depth
    let index : Fin b.boughtRows:=Fin.cast recording (head.enum ⟨finProdFinEquiv (p,a),candidate⟩)
    apply physicalEdge_birth b _ _ _ m out r r' index room same _ archived
    have offset:index.val=birth c p a*head.ports+candidate.val:=by
      change candidate.val+head.ports*(finProdFinEquiv (p,a)).val=_
      rw [birth_ordinal,Nat.mul_comm head.ports,Nat.add_comm]
    rw [birthRead, offset]
    exact b.originalProbe_read head.ports (birth c p a) .row m
      ((header F (withPorts s c b G) (.inner p a j t)).ballTerm.eval m r) candidate ball

/-- Interpret the measured ordinal itself in the terminal catalogue. This is
a readback of a stored role ID and uses no second geometric expression. -/
theorem outer_recorded_id (p a : ℕ) (i : Fin D) (m out : Memory w) (r : Word w)
    (room : b.rows<2^w) :
    let parent:=withPorts s c b G
    let raw:=(edge F parent b.rows (.outer p a) i).eval m r
    (id F parent b (.outer p a) i).eval m r=(b.commonID .row).eval out raw :=
  outer_common F s c b G p a i m out r _ .row room rfl

theorem inner_recorded_id (p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel) (j t : ℕ) (i : Fin D)
    (m out : Memory w) (r : Word w) (candidate : Fin (G.directory.header z (2^W) k s.sampler.degree depth).ports)
    (recording : (G.directory.header z (2^W) k s.sampler.degree depth).count=b.boughtRows)
    (ordinals : ((c.inject+c.cool)*c.outerFuel)≤2^w)
    (countFit : (G.directory.header z (2^W) k s.sampler.degree depth).ports≤2^w)
    (room : b.rows<2^w) (dir : (G.directory.header z (2^W) k s.sampler.degree depth).Loaded out)
    (source : b.bought.flag=G.directory.archived z (2^W) k s.sampler.degree depth G.directory.flagBase)
    (origin : G.directory.flagBase (finProdFinEquiv (p,a))=(build F (withPorts s c b G) (.outer p a) 0).board.purchaseOut)
    (size : (build F (withPorts s c b G) (.outer p a) 0).market.rows=(G.directory.header z (2^W) k s.sampler.degree depth).ports)
    (ball : (header F (withPorts s c b G) (.inner p a j t)).ballTerm.eval m r=(candidate.val:Word w))
    (saved : m ((build F (withPorts s c b G) (.outer p a) 0).board.purchaseOut+candidate.val)=
      out ((build F (withPorts s c b G) (.outer p a) 0).board.purchaseOut+candidate.val)) :
    let parent:=withPorts s c b G
    let raw:=(edge F parent b.rows (.inner p a j t) i).eval m r
    (id F parent b (.inner p a j t) i).eval m r=(b.commonID .row).eval out raw := by
  intro parent raw
  apply inner_common F s c b G p a j t i m out r raw .row candidate recording room rfl ball
  exact parent_flag F parent c b G p a j t m out r candidate ordinals countFit dir source origin size ball saved

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
