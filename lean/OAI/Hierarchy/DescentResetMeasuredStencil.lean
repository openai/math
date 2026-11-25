import OAI.Hierarchy.DescentResetPreparedOperands

namespace OAI
/-! # Native reset stencil on every genuine source cell, including empty source cells -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentGL DescentGLPacked DescentGLPacked.BankImage DescentPlainTerminal.Suffix DescentColonies DescentPackedColony
open DescentSIMDLookup DescentPackedZip DescentIssuedFallbackPanel DescentPackedFlowPair.Padded ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k H V₀ c h l n b batch w slots total levels high t : ℕ} {bits : P→ℕ}
    {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ} (A : GroupStage W G q ε J V k)
    (name : V≃Fin V₀) (digits : Block (h+l)≃J×Block k)
def stencilBook (hosts c m slots high batch b n t levels total : ℕ) : StencilBook :=
  ⟨hosts,c,m,A.degree,slots,high,batch,b,n,t,levels,total⟩

def paidProgram (S : StencilBook) (X : StencilBook.Sources) (base out f B K g cap Y w : ℕ) :=
  ((S.splitProgram base out X.roster (32*Nat.clog 2 (2*S.degree)) (2^(f+1)*B) w).seq
    (S.scalarProgram base K (2^f*B) (2^S.r*cap) w)).seq
    (Stencil.program (S.readers base) (S.inputs X base out g) S.t f B Y w)

def paidTime (S : StencilBook) (X : StencilBook.Sources) (base out f B g : ℕ) :=
  (S.splitTime base out X.roster (32*Nat.clog 2 (2*S.degree)) (2^(f+1)*B)+S.scalarTime base)+
    Stencil.time (S.readers base) (S.inputs X base out g) S.t

local notation "m" => h+l
local notation "r" => m-c
local notation "rs" => roster (D:=A.degree) A name
local notation "wt" => load (N:=H) A name digits
local notation "raw" => flow (N:=H) (D:=slots) A name digits
local notation "D₀" => (32*Nat.clog 2 (2*A.degree))

local notation "S" => stencilBook A H c m slots high batch b n t levels total
local notation "Wchip" => (fun v x=>(wt v x:Cell b))
local notation "Fchip" => (fun j v x=>(raw j v x:Cell b))
local notation "realList" => fun v:V=>(DescentPackedColony.slots A.degree).filterMap (portAt A name v)
local notation "symNear" => fun v u (hit:u∈A.near v)=>(A.symmetric v u).mp hit
local notation "portsAt" => ContactRoster.ports A.mutual (portAt A name) (actual_ports A name symNear)
  (fun v u hit=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hit).2,(Finset.mem_filter.mp hit).1⟩)

/-- The actual packed row at every padded address, together with its meaning on genuine hosts. -/
def Published (M t out : ℕ) (real : V↪Fin H) (f : V→Block c→Block r→Cell t) (mem : Memory w) : Prop :=
  ∃u : Fin H→Block c→Block r→Cell t,
    (∀p : Row H (2^c) M,mem (out+(row _ _ _ p).val)=((data (fun v hi=>encode t (2^r) (u v hi)) p).val:Word w)) ∧
    ∀v hi x,u (real v) hi x=f v hi x

theorem run_from_chips (small : c≤ m) (ph : V₀≤H) (pd : A.degree≤ slots) (L : DescentGL.Layout m)
    (f B K g cap Y : ℕ) (depth : V→ℕ) (X : StencilBook.Sources) (base out : ℕ) (mem : Memory w)
    (positive : 0<b) (pos : 0<batch) (safe : (S).endAddress base<2^w)
    (arithmetic : batch*max (n*Stencil.count r (A.degree+A.degree)) (t*2^r)≤w/2) (short : n*batch≤w)
    (room : StencilBook.Geometry S X base out w) (big : H<2^w)
    (height : m-c<2^n) (one : 1<2^n) (limit : 2^r*cap<2^n)
    (levelsFit : H*(m+1)≤X.levels.size) (hubsFit : H≤X.hubs.size)
    (spectrumFit : H*(m+1+slots)*2^high≤X.spectrum.size) (precision : X.precision≤w)
    (pairBits : levels+total≤w) (levelBits : m<2^levels)
    (bounds : ∀v,c≤depth v ∧ depth v≤ m) (totalFit : ∀v u,(∑x,A.resetFlow digits v u x)<2^total)
    (weightFit : ∀v x,wt v x<2^b) (flowFit : ∀j v x,raw j v x<2^b)
    (count : ∀p : Row H (2^c) batch,X.count.eval mem ((row _ _ _ p).val:Word w)=(V₀:Word w))
    (hubs : ∀v,mem (X.hubs.base+(name v).val)=((A.hub v).toNat:Word w))
    (smoothed : ∀v,mem (X.levels.base+(name v).val*(m+1))=(depth v:Word w))
    (paid : ∀v u (j : Fin A.degree),portAt A name v j=some u→
      (mem (X.spectrum.base+(H*(m+1)+(name v).val*slots+j.val)*2^high)).val%2^X.precision=∑x,A.resetFlow digits v u x)
    (peers : ∀v j,mem (X.roster.base+(v.val*A.degree+j.val))=(target (rs ph v j):Word w))
    (words : ∀i : Channels.Index slots m,∀p : Row H (2^c) batch,
      mem (slice out H (chunks (2^c) batch) i+(row _ _ _ p).val)=
        ((data (Channels.blockValues small (Channels.values Wchip Fchip positive i) L) p).val:Word w)) :
    ∃dst,(paidProgram S X base out f B K g cap Y w).Exec mem dst (paidTime S X base out f B g) ∧
      (∀(v : V) (hi : Block c) (x : Block r),
        digit t x.val (digit (t*2^r) (lane hi pos).val
          (dst ((S).output base+(row H (2^c) batch (position ((name v).castLE ph) hi pos)).val)).val)=
          ((Stencil.word (Stencil.measured (n:=n) small A.mutual depth L (A.resetLoad digits) (A.resetFlow digits)
             A.hub A.degree f B K g cap portsAt realList v hi) f B Y x:ℕ):Cell t).val) ∧
      (∀z,z<base ∨ (S).endAddress base≤z→dst z=mem z) ∧
      (S).OldOrder X base out g c L dst ∧
      Published (h:=h) (l:=l) batch t ((S).output base) (name.toEmbedding.trans (Fin.castLEEmb ph))
        (fun v hi x=>(Stencil.word (Stencil.measured (n:=n) small A.mutual depth L (A.resetLoad digits)
          (A.resetFlow digits) A.hub A.degree f B K g cap portsAt realList v hi) f B Y x:Cell t)) dst := by
  let C:=(S).readers base
  let Hdr:=(S).header base
  let P:=(S).inputs X base out g
  let ly:=(S).chosen base out X.roster
  let rs':=rs ph
  let weight:=fun v hi x=>wt v ((rearrange L).symm (join small hi x))
  let flow':=fun (j : Fin (A.degree+A.degree)) v hi x=>raw ((side j).castLE pd) v ((rearrange L).symm (join small hi x))
  let simulated:=fun hi=>Scan.build (incoming (DescentPackedColony.peers rs')) (fun v x=>weight v hi x) D₀ (2^(f+1)*B) r
  have start:base≤((S).layer base out X.roster).origin:=Nat.le_add_right ..
  have top:=room.old.roster
  have weights : Reads ((S).weightBank out) (Channels.blockValues small Wchip L) batch mem:=by
    have loadIndex : Channels.values Wchip Fchip positive (Channels.loadIndex slots m) = Wchip := by
      funext v x
      unfold Channels.values
      simp only [Channels.loadIndex, Equiv.symm_apply_apply, Sum.elim_inl]
    intro p
    simp only [StencilBook.weightBank,StencilBook.bankAt,StencilBook.chart_load,Channels.shortBank]
    simpa only [loadIndex,stencilBook] using words (Channels.loadIndex slots m) p
  obtain ⟨mid,prepare,_,split,issued,coords,cuts,planes,frame⟩:=(S).after_splits small base out X.roster D₀
    (2^(f+1)*B) K (2^f*B) (2^r*cap) rs' Wchip L mem room.small ⟨top.1,top.2.1,top.2.2.trans start⟩
    room.ports room.safe peers weights
  obtain ⟨pbank,dlevels,leads,_,_,_,usable,_,before⟩:=(S).banks X base out room
  have old (z : ℕ) (hz:z<base) := frame z (.inl (hz.trans_le start))
  have lifted {T:Bank} (fit:T.Fits w base) : T.Fits w ((S).afterHeader base):=⟨fit.1,fit.2.1,fit.2.2.trans before⟩
  have bdepth (v:V) : mid (X.levels.base+(name v).val*(m+1))=(depth v:Word w):=by
    have lim:=Nat.mul_le_mul_right (m+1) ((name v).isLt.trans_le ph)
    rw [Nat.succ_mul] at lim
    exact (old _ (by have lo:=room.old.levels.2.2;omega)).trans (smoothed v)
  have bhub (v:V) : mid (X.hubs.base+(name v).val)=((A.hub v).toNat:Word w) :=
    (old _ ((Nat.add_lt_add_left (((name v).isLt.trans_le ph).trans_le hubsFit) _).trans_le room.old.hubs.2.2)).trans (hubs v)
  have bpaid (v u:V) (j:Fin A.degree) (hit:portAt A name v j=some u) :
      (mid (X.spectrum.base+(H*(m+1)+(name v).val*slots+j.val)*2^high)).val%2^X.precision=∑x,A.resetFlow digits v u x:=by
    have ord:=Nat.mul_le_mul_right slots ((name v).isLt.trans_le ph)
    rw [Nat.succ_mul] at ord
    have real:H*(m+1)+(name v).val*slots+j.val<H*(m+1+slots):=by
      rw [Nat.mul_add H (m+1) slots]
      rw [Nat.add_assoc]
      exact Nat.add_lt_add_left ((Nat.add_lt_add_left (j.isLt.trans_le pd) _).trans_le ord) _
    have address:=(Nat.mul_lt_mul_of_pos_right real (Nat.two_pow_pos high)).trans_le spectrumFit
    rw [old _ ((Nat.add_lt_add_left address _).trans_le room.old.spectrum.2.2)]
    exact paid v u j hit
  have hrow:=Heads.at_host A name Hdr X.head ph c g depth ((S).afterHeader base) mid coords pbank dlevels
    (lifted room.old.levels) (lifted room.old.hubs) levelsFit hubsFit big height one bounds
    (fun p=> (eval_below _ _ mem mid room.old.count old).trans (count p)) bdepth bhub
  have prow:=Paid.at_port A name Hdr (StencilBook.Sources.paid S X base out) ph c f B K cap depth digits (ly.source (S).r)
    ((S).afterHeader base) mid coords pbank dlevels leads (lifted room.old.levels) (lifted room.old.spectrum)
    usable issued levelsFit spectrumFit pd big height precision pairBits levelBits limit bounds totalFit bdepth bpaid cuts
  have full:out+((1+slots)+m)*H*chunks (2^c) batch+2^(Nat.clog 2 (S).rows)≤(S).start base:=by
    change out+_+_≤base+_
    have endRows:=room.small
    simpa only [stencilBook,StencilBook.rows,Nat.mul_assoc] using Nat.add_le_add_right endRows (2^(Nat.clog 2 (S).rows))
  have qstart: (S).start base≤(S).afterHeader base:=by
    exact (show (S).start base ≤ Hdr.pos.base from Nat.le_add_right ..).trans
      ((Nat.le_add_right Hdr.pos.base _).trans pbank.2.2)
  have words' (i : Channels.Index slots m) (p : Row H (2^c) batch) :
      mid (slice out H (chunks (2^c) batch) i+(row _ _ _ p).val)=
        ((data (Channels.blockValues small (Channels.values Wchip Fchip positive i) L) p).val:Word w) := by
    let B:=Channels.shortBank out H (2^c) batch i
    have guard:=Channels.short_fits out i full (qstart.trans_lt room.safe)
    have hrow: (row H (2^c) batch p).val<B.size:=(row _ _ _ p).isLt.trans_le (Nat.le_pow_clog (by decide) _)
    exact (frame (B.base+(row _ _ _ p).val) (.inl ((Nat.add_lt_add_left hrow B.base).trans_le guard.2.2))).trans (words i p)
  obtain ⟨wtData,flowData,original⟩:=Channels.operands_short small Wchip Fchip positive L out ((S).afterHeader base)
    ((S).narrow base).base mid (full.trans qstart) room.safe le_rfl planes words'
  have data (j:Fin (A.degree+A.degree)) : Source (P.flows j)
      (fun v hi=>DescentPackedColony.counts b (flow' j v hi)) batch mid :=by
    simp only [P,StencilBook.inputs,StencilBook.bankAt]
    rw [(S).chart_flow pd]
    exact flowData ((side j).castLE pd)
  have origin (i:Fin m) : Source (P.planes i) (fun (_:Fin H) hi=>DescentPlainTerminal.PackedOrder.panel small L hi i) batch mid:=by
    simp only [P,StencilBook.inputs,StencilBook.bankAt]
    rw [(S).chart_plane]
    exact original i
  obtain ⟨dst,run,read,low,highFrame,ordered,allWords⟩:=Stencil.compute_packed C P t f B Y mid small L
    (hostHeader («m»:=m) (c:=c) (n:=n) A name depth g) (portHeader (c:=c) A name digits depth f B K cap)
    weight flow' simulated pos arithmetic short safe ((S).fit X base out g room) hrow prow
    (fun v hi x=>weightFit v _) (fun j v hi x=>flowFit _ v _) (by
      simp only [P,StencilBook.inputs,StencilBook.weightBank,StencilBook.bankAt]
      rw [(S).chart_load]
      exact wtData) data
    (by
      apply source_column _ ((S).afterHeader base) usable.source mid _ usable.srcRoom
      intro p
      have got := split p
      simp only [simulated,weight,Fin.val_cast_of_lt (weightFit _ _)] at got ⊢
      with_unfolding_all exact got) origin
  have eqn (j : Fin (A.degree+A.degree)) u y :
      raw ((side j).castLE pd) u y=flow A name digits (side j) u y:=by
    simp only [flow,show project A.degree ((side j).castLE pd)=some (side j) from project_cast pd _,
      show project A.degree (side j)=some (side j) from project_cast le_rfl _]
  have meaning (v:V) (hi:Block c) :=
    actor (n:=n) A name ph digits small L depth f B K g cap v hi
  refine ⟨dst,prepare.then run,?_,?_,?_,⟨_,allWords,?_⟩⟩
  · intro v hi x
    have result:=read ((name v).castLE ph) hi x
    rw [←meaning v hi]
    simp only [weight,flow',simulated,rs',eqn,rearrangedLoad] at result ⊢
    with_unfolding_all exact result
  · intro z hz
    rcases hz with below|above
    · exact (low _ (below.trans_le before)).trans (old _ below)
    · have after:C.origin≤(S).endAddress base:=by
        change C.origin ≤ (Stencil.lastChart C _ t).endAddress
        dsimp only [Stencil.lastChart,Stencil.Layout.Chart.endAddress,
          Stencil.Layout.Chart.out,Stencil.Layout.Chart.scratch,Stencil.Layout.Chart.mask,Stencil.Layout.Chart.table,
          DescentPlainTerminal.StencilTables.start,Stencil.ReaderTables.Chart.stop,Stencil.ReaderTables.Chart.planeBase,
          Stencil.ReaderTables.Chart.first]
        repeat first | exact le_rfl | apply Nat.le_trans ?_ (Nat.le_add_right _ _)
      exact (highFrame _ above).trans (frame _ (.inr (after.trans above)))

  · constructor
    · intro i x
      simp only [StencilBook.orderExpr,show (S).r=m-c from rfl,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt x.isLt]
      with_unfolding_all exact (ordered i x).1
    · intro sm i x
      simp only [StencilBook.orderExpr,show (S).r=m-c from rfl,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt x.isLt]
      with_unfolding_all exact (ordered i x).2
    · exact usable
    · intro rs₀ original
      have held (B : Bank) (f : B.Fits w ((S).afterHeader base)) (z : ℕ) (ok : z<B.size) :
          dst (B.base+z)=mid (B.base+z) := low _ ((Nat.add_lt_add_left ok _).trans_le f.2.2)
      refine ⟨fun p j=>(held _ (usable.ids j) _ ((row _ _ _ p).isLt.trans_le (usable.idsRoom j))).trans (issued.ids p j),
        fun v j=>original v j,fun v=>(held _ usable.offsets _ (v.isLt.trans_le usable.offRoom)).trans (issued.offsets v),
        fun p=>(held _ usable.chunks _ ((row _ _ _ p).isLt.trans_le usable.chunkRoom)).trans (issued.chunks p)⟩
    · have past : Hdr.stop≤(S).afterHeader base:=by
        change Hdr.stop≤Cutoff.finish Hdr.stop (S).levels (S).total+_
        unfold Cutoff.finish
        exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
      intro z inf sup
      exact (low z (sup.trans_le past)).trans (coords z inf sup)
  · intro v hi x
    dsimp only
    rw [←meaning v hi]
    simp only [weight,flow',simulated,rs',eqn,rearrangedLoad]

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
