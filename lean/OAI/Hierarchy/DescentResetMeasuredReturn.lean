import OAI.Hierarchy.DescentResetMeasuredStencil

namespace OAI
/-! # From the actual selected GL bank to every real terminal stencil digit -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentGL DescentGLPacked DescentGLPacked.BankImage DescentPlainTerminal.Suffix DescentColonies DescentPackedColony
open DescentSIMDLookup DescentPackedZip DescentIssuedFallbackPanel DescentPackedFlowPair.Padded ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k H V₀ c h l n b batch w slots total levels high t : ℕ} {bits : P→ℕ}
    {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ} (A : GroupStage W G q ε J V k)
    (name : V≃Fin V₀) (digits : Block (h+l)≃J×Block k)
def repackProgram (S : StencilBook) (chip : Bank) (first ratio : ℕ) {K₀ : ℕ}
    (factor : 2^S.c=K₀*(ratio*S.M)) (ratioPos : 0<ratio) (pos : 0<S.M) (w : ℕ) :=
  let a:=S.b*2^S.r
  let H:=((1+S.maxPorts)+S.m)*S.hosts
  let out:=Subwords.destination first a H (2^S.c) ratio S.M
  let T:=Subwords.chart first a H (2^S.c) ratio S.M
  let I:=Subwords.literals (w:=w) first H a factor ratioPos pos
  I.program.seq (scan w out (H*chunks (2^S.c) S.M) (Subwords.term T chip))

def repackTime (S : StencilBook) (chip : Bank) (first ratio : ℕ) {K₀ : ℕ}
    (factor : 2^S.c=K₀*(ratio*S.M)) (ratioPos : 0<ratio) (pos : 0<S.M) :=
  let a:=S.b*2^S.r
  let H:=((1+S.maxPorts)+S.m)*S.hosts
  let T:=Subwords.chart first a H (2^S.c) ratio S.M
  let I:=Subwords.literals (w:=0) first H a factor ratioPos pos
  (4+10*I.length)+(4+H*chunks (2^S.c) S.M*(2*(Subwords.term T chip).work+4))

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

variable (first ratio : ℕ)
local notation "out₀" => Subwords.destination first (b*2^r) (((1+slots)+m)*H) (2^c) ratio batch
local notation "base₀" => Subwords.finish first (b*2^r) (((1+slots)+m)*H) (2^c) ratio batch

theorem run_from_remix (small : c≤ m) (ph : V₀≤H) (pd : A.degree≤ slots) (L : DescentGL.Layout m)
    (f B K g cap Y : ℕ) (depth : V→ℕ) (X : StencilBook.Sources) (chip : Bank) (K₀ : ℕ) (mem : Memory w)
    (lanes : ratio*batch*2^r=2^l) (factor : 2^c=K₀*(ratio*batch)) (ratioPos : 0<ratio)
    (positive : 0<b) (pos : 0<batch) (safe : (S).endAddress base₀<2^w)
    (arithmetic : batch*max (n*Stencil.count r (A.degree+A.degree)) (t*2^r)≤w/2) (short : n*batch≤w)
    (early : X.Before w first) (chipFits : chip.Fits w first)
    (chipRows : ((1+slots)+m)*H*2^h≤chip.size) (portRows : H*A.degree≤X.roster.size)
    (headRoom : (S).afterHeader base₀<2^w) (big : H<2^w)
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
    (dense : ∀i : Channels.Index slots m,Dense (h:=h) (l:=l) (slice chip.base H (2^h) i)
      (fun v x=>Channels.values Wchip Fchip positive i v ((rearrange L).symm x)) mem) :
    ∃dst,((repackProgram S chip first ratio factor ratioPos pos w).seq (paidProgram S X base₀ out₀ f B K g cap Y w)).Exec mem dst (repackTime S chip first ratio factor ratioPos pos + paidTime S X base₀ out₀ f B g) ∧
      (∀(v : V) (hi : Block c) (x : Block r),
        digit t x.val (digit (t*2^r) (lane hi pos).val
          (dst ((S).output base₀+(row H (2^c) batch (position ((name v).castLE ph) hi pos)).val)).val)=
          ((Stencil.word (Stencil.measured (n:=n) small A.mutual depth L (A.resetLoad digits) (A.resetFlow digits)
             A.hub A.degree f B K g cap portsAt realList v hi) f B Y x:ℕ):Cell t).val) ∧
      (∀z,z<first ∨ (S).endAddress base₀≤z→dst z=mem z) ∧
      (S).OldOrder X base₀ out₀ g c L dst ∧
      Published (h:=h) (l:=l) batch t ((S).output base₀) (name.toEmbedding.trans (Fin.castLEEmb ph))
        (fun v hi x=>(Stencil.word (Stencil.measured (n:=n) small A.mutual depth L (A.resetLoad digits)
          (A.resetFlow digits) A.hub A.degree f B K g cap portsAt realList v hi) f B Y x:Cell t)) dst := by
  let NN:=((1+slots)+m)*H
  have front:first≤out₀:=Nat.le_add_right ..
  have tail:out₀≤base₀:=Nat.le_add_right ..
  have split:base₀≤(S).start base₀:=Nat.le_add_right ..
  have pg:(S).start base₀≤((S).header base₀).origin:=Nat.le_add_right ..
  have bound:((S).header base₀).origin≤(S).afterHeader base₀:=by
    dsimp [StencilBook.afterHeader,StencilBook.narrow,Cutoff.finish,PortLevels.AddressBook.stop,
      PortLevels.AddressBook.lead,PortLevels.AddressBook.depth,PortLevels.AddressBook.pos]
    repeat' first | exact Nat.le_refl _ | apply Nat.le_trans ?_ (Nat.le_add_right ..)
  have shortRoom:base₀<2^w:=(split.trans (pg.trans bound)).trans_lt headRoom
  obtain ⟨mid,repack,_,word,frame⟩:=Channels.repack small lanes factor ratioPos pos chip first L
    (Channels.values Wchip Fchip positive) mem dense chipFits chipRows shortRoom
  have old (z:ℕ) (hz:z<first):mid z=mem z:=frame _ (.inl hz)
  have earlier:first≤base₀:=front.trans tail
  have lift {B:Bank} (fit:B.Fits w first) : B.Fits w base₀:=⟨fit.1,fit.2.1,fit.2.2.trans earlier⟩
  have geometry : StencilBook.Geometry S X base₀ out₀ w:=
    ⟨⟨ProtocolRAMGeneratedWrite.fits_mono _ earlier early.count,lift early.levels,lift early.hubs,
      lift early.spectrum,lift early.roster⟩,portRows,by simp [StencilBook.rows,Subwords.finish,stencilBook,Nat.mul_assoc],headRoom⟩
  have depthWords (v:V) :
      mid (X.levels.base+(name v).val*(m+1))=(depth v:Word w):=by
    have lim:=Nat.mul_le_mul_right (m+1) ((name v).isLt.trans_le ph)
    rw [Nat.succ_mul] at lim
    exact (old _ (by have lo:=early.levels.2.2;omega)).trans (smoothed v)
  have hubWords (v:V) : mid (X.hubs.base+(name v).val)=((A.hub v).toNat:Word w):=
    (old _ ((Nat.add_lt_add_left (((name v).isLt.trans_le ph).trans_le hubsFit) _).trans_le early.hubs.2.2)).trans (hubs v)
  have paidWords (v u:V) (j:Fin A.degree) (hit:portAt A name v j=some u) :
      (mid (X.spectrum.base+(H*(m+1)+(name v).val*slots+j.val)*2^high)).val%2^X.precision=∑x,A.resetFlow digits v u x:=by
    have ord:=Nat.mul_le_mul_right slots ((name v).isLt.trans_le ph)
    rw [Nat.succ_mul] at ord
    have real:H*(m+1)+(name v).val*slots+j.val<H*(m+1+slots):=by
      rw [Nat.mul_add H (m+1) slots,Nat.add_assoc]
      exact Nat.add_lt_add_left ((Nat.add_lt_add_left (j.isLt.trans_le pd) _).trans_le ord) _
    have address:=(Nat.mul_lt_mul_of_pos_right real (Nat.two_pow_pos high)).trans_le spectrumFit
    rw [old _ ((Nat.add_lt_add_left address _).trans_le early.spectrum.2.2)]
    exact paid v u j hit
  have contacts (v:Fin H) (j:Fin A.degree):mid (X.roster.base+(v.val*A.degree+j.val))=(target (rs ph v j):Word w):=by
    have lim:=Nat.mul_le_mul_right A.degree v.isLt
    rw [Nat.succ_mul] at lim
    exact (old _ (by have lo:=early.roster.2.2;have jv:=j.isLt;omega)).trans (peers v j)
  obtain ⟨dst,run,reads,unchanged,ordered,published⟩:=run_from_chips A name digits small ph pd L f B K g cap Y depth
    X base₀ out₀ mid positive pos safe arithmetic short geometry big height one limit levelsFit hubsFit spectrumFit
    precision pairBits levelBits bounds totalFit weightFit flowFit
    (fun p=>(eval_below _ _ mem mid early.count old).trans (count p)) hubWords depthWords paidWords contacts word
  refine ⟨dst,repack.then run,reads,?_,ordered,published⟩
  intro z hz
  rcases hz with lower|upper
  · exact (unchanged _ (.inl (lower.trans_le earlier))).trans (old _ lower)
  · have floor:base₀≤(S).endAddress base₀:=by
      rw [(S).extent]
      repeat' first | exact Nat.le_refl _ | apply Nat.le_trans ?_ (Nat.le_add_right ..)
    exact (unchanged _ (.inr upper)).trans (frame _ (.inr (floor.trans upper)))

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
