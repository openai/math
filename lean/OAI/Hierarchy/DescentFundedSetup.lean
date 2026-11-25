import OAI.Hierarchy.DescentFundedSetupLayout
import OAI.Hierarchy.DescentFundedArrivals
import OAI.Hierarchy.DescentResetRetileStrip
import OAI.Hierarchy.DescentSignedGLTotal
import OAI.Hierarchy.DescentFallbackGLWindow
import OAI.Hierarchy.ProtocolRAMRunMemory
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # The preceding paid counts are rearranged by the actual saved basis -/
namespace Hierarchy.DescentFundedCensus.Setup
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM DescentPackedColony
open DescentGLPacked DescentGLPacked.BankImage DescentGLNielsen DescentGL DescentColonies
open DescentSixParty.Chronology DescentResetRetainedSetup
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

variable (s : DescentFundedCensus.Setup) {w : ℕ}
def copy (base w : ℕ) (old : Fin s.blocks→Bank) :=
  Strip.code base s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision w old
def sourceBank (base : ℕ) (b : Fin s.blocks) := Strip.bank base s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision b.val
def prior (base : ℕ) (_ : Fin 1) (b : Fin s.blocks) : Expr:=.lookup (s.sourceBank base b) .row
def plan (base : ℕ) :=SignedFields.chart (s.matrix base) 1 s.hosts s.high s.low s.precision
def selector (base : ℕ) :=SignedFields.joinOp (s.stripEnd base) s.precision s.blocks s.gatherLanes 1 (s.prior base)
def shuffle (w base : ℕ) (key : Bank) :=
  (Book.install (SignedFields.joinGate s.precision s.blocks) (SignedFields.joinWidth s.precision s.blocks)
    s.gatherLanes w (s.stripEnd base)).seq
    (SignedFields.program (s.matrix base) (s.plan base) key (s.selector base) 1 s.hosts s.high s.low s.precision w)
def shuffleTime (w base : ℕ) (key : Bank) :=
  (4+10*(s.blocks*(2*2^(SignedFields.joinWidth s.precision s.blocks*s.gatherLanes))))+
    SignedFields.duration (s.matrix base) (s.plan base) key (s.selector base) 1 s.hosts s.high s.low s.precision w
def shuffled (base : ℕ) (key : Bank) (m : Memory w) :=
  SignedFields.image (s.matrix base) (s.plan base) key (s.selector base) 1 s.hosts s.high s.low s.precision
    (Book.image (SignedFields.joinGate s.precision s.blocks) (SignedFields.joinWidth s.precision s.blocks) s.gatherLanes (s.stripEnd base) m)
def primary (base : ℕ) : Bank :=
  ⟨slice ((((s.plan base).chosen (s.high+s.low)).bank (schedule (s.high+s.low)).length).base)
    s.hosts (2^s.high) (0:Fin 1),Nat.clog 2 (s.hosts*2^s.high)⟩
def secondary (base : ℕ) (signed : Fin (2*s.capacity)→Expr) : Expr :=
  Arrivals.expr (s.signedEnd base) s.degree s.capacity s.precision s.donors s.outputLanes signed

def program (w base : ℕ) (old : Fin s.blocks→Bank) (key : Bank) :=
  (((s.copy base w old).program).seq (s.shuffle w base key)).seq
    (Arrivals.program (s.signedEnd base) s.degree s.capacity s.precision s.donors s.outputLanes w)
def ticks (w base : ℕ) (old : Fin s.blocks→Bank) (key : Bank) :=
  ((s.copy base w old).ticks+s.shuffleTime w base key)+(4+10*2^s.flagWidth)
def memory (base : ℕ) (old : Fin s.blocks→Bank) (key : Bank) (m : Memory w) :=
  Arrivals.memory (s.signedEnd base) s.degree s.capacity s.precision s.donors s.outputLanes
    (s.shuffled base key ((s.copy base w old).image m))

theorem any (base : ℕ) (old : Fin s.blocks→Bank) (key : Bank) (m : Memory w)
    (priorFit : ∀b,(old b).Fits w base) (keyFits : key.Fits w base) (space : s.roof base<2^w) :
    (s.program w base old key).Exec m (s.memory base old key m) (s.ticks w base old key) ∧
    CheapCode (s.program w base old key) ∧ ∀a,a<base ∨ s.roof base≤a→s.memory base old key m a=m a :=by
  obtain ⟨e₁,e₂,e₃,e₄⟩:=s.order base
  have stripFits:=(e₂.trans (e₃.trans e₄)).trans_lt space
  have srcFit (j : Fin 1) (b : Fin s.blocks) : (s.prior base j b).Fits w (s.stripEnd base):=
    ⟨(Strip.fits base s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision b stripFits).1,trivial⟩
  let m₁:=(s.copy base w old).image m
  let m₂:=s.shuffled base key m₁
  obtain ⟨copy_,keep₁⟩:=Strip.any base s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision old m priorFit stripFits
  obtain ⟨move,cheapM,keep₂⟩:=SignedFields.from_slots_any (D:=1) (H:=s.hosts) (h:=s.high) (l:=s.low)
    (b:=s.precision) (M:=s.gatherLanes) (s.stripEnd base) key (s.prior base) m₁ srcFit
    ⟨keyFits.1,keyFits.2.1,keyFits.2.2.trans e₁⟩ (e₄.trans_lt space)
  obtain ⟨book,cheapB,keep₃,_⟩:=Arrivals.any (s.signedEnd base) s.degree s.capacity s.precision s.donors s.outputLanes m₂ space
  refine ⟨Procedure.Exec.then (Procedure.Exec.then copy_ move) book,cheap_seq (cheap_seq (s.copy base w old).cheap cheapM) cheapB,?_⟩
  intro a ha
  exact (keep₃ a (ha.imp_left (fun l=>l.trans_le (e₁.trans (e₂.trans e₃))))).trans
    ((keep₂ a ((ha.imp_left (fun l=>l.trans_le e₁)).imp_right (fun u=>e₄.trans u))).trans
      (keep₁ a (ha.imp_right (fun u=>e₂.trans (e₃.trans (e₄.trans u))))))

theorem primary_fit (base : ℕ) (space : s.signedEnd base<2^w) : (s.primary base).Fits w (s.signedEnd base) :=by
  let C:=s.plan base
  let d:=s.high+s.low
  let n:=(schedule d).length
  let rows:=s.hosts*2^s.high
  have chart:=(SignedFields.allocation (s.matrix base) 1 s.hosts s.high s.low s.precision w space).1
  have used : rows≤C.page:=by simpa only [rows,C,plan,Nat.one_mul] using chart.rows
  have rounded : 2^Nat.clog 2 rows≤C.page:=Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow used)
  have before : C.input.base≤C.heap d:=(Nat.le_add_right ..).trans (chart.input.2.2.trans (Nat.le_add_right ..))
  have extent : (s.primary base).base+(s.primary base).size≤ s.signedEnd base:=by
    change ((C.chosen d).bank n).base+(0:Fin 1).val*s.hosts*2^s.high+2^Nat.clog 2 rows≤C.heap d+(n+1)*C.page
    simp only [Fin.val_zero,Nat.zero_mul,Nat.add_zero]
    cases n with
    | zero=>
      change C.input.base+2^Nat.clog 2 rows≤C.heap d+(0+1)*C.page
      simpa only [Nat.zero_add,Nat.one_mul] using Nat.add_le_add before rounded
    | succ i=>
      change C.heap d+i*C.page+2^Nat.clog 2 rows≤C.heap d+(i+1+1)*C.page
      rw [Nat.succ_mul,Nat.succ_mul]
      omega
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (extent.trans_lt space),extent⟩

theorem read (base : ℕ) (old : Fin s.blocks→Bank) (key : Bank) (m : Memory w)
    (keys : key.Fits w base) (fits : ∀b,(old b).Fits w base) (space : s.roof base<2^w)
    (L : DescentGL.Layout (s.high+s.low)) (stored : m key.base=((DescentExterior.matrixCode L).val:Word w))
    (size : 2^(s.high+s.low)=s.oldGroups*s.blocks) (pitch : 2^s.low=s.gatherLanes*s.blocks)
    (cut : s.cut≤ s.high+s.low) (pack : s.outputLanes*s.donors=2^s.low)
    (oldPos : 0<s.oldLanes) (gatherPos : 0<s.gatherLanes) (blocksPos : 0<s.blocks) (outPos : 0<s.outputLanes)
    (x : Fin s.blocks→Fin s.hosts→Fin s.oldGroups→Cell s.precision)
    (capacity : ∀b,s.hosts*chunks s.oldGroups s.oldLanes≤(old b).size) (actual : ∀b,Reads (old b) (x b) s.oldLanes m) :
    let value:=fun h t=>let j:=(finProdFinEquiv.symm (Fin.cast size t) : Fin s.oldGroups×Fin s.blocks); x j.2 h j.1
    Reads (s.primary base) (fun h hi=>encode s.precision s.donors (fun lo=>value h
      ((rearrange L).symm (DescentIssuedFallbackPanel.join cut hi lo)))) s.outputLanes (s.memory base old key m) :=by
  intro value
  obtain ⟨e₁,e₂,e₃,e₄⟩:=s.order base
  have room:=(e₂.trans (e₃.trans e₄)).trans_lt space
  let m₁:=(s.copy base w old).image m
  have readBank b:=Strip.read base s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision old m fits room b (x b) oldPos (capacity b) (actual b)
  have fitBank b:=Strip.fits base s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision b room
  have srcFit (j : Fin 1) (b : Fin s.blocks) : (s.prior base j b).Fits w (s.stripEnd base):=⟨(fitBank b).1,trivial⟩
  have physical (j : Fin 1) (b : Fin s.blocks) : Source (s.prior base j b) (x b) s.gatherLanes m₁:=
    source_column _ _ (fitBank b).1 m₁ _ (fitBank b).2 (readBank b)
  have keyLow : key.base<base:=by have:=keys.1;have:=keys.2.2;omega
  have smaller:=((Strip.any base s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision old m fits room).2 key.base (.inl keyLow)).trans stored
  have safe : key.Fits w (s.stripEnd base):=⟨keys.1,keys.2.1,keys.2.2.trans e₁⟩
  obtain ⟨dst,native,_,dense,_⟩:=SignedFields.from_slots (s.stripEnd base) key (s.prior base) L size pitch gatherPos blocksPos
    (fun (_ : Fin 1) h g b=>x b h g) m₁ srcFit physical safe smaller (e₄.trans_lt space)
  have real:=SignedFields.from_slots_any (D:=1) (H:=s.hosts) (h:=s.high) (l:=s.low) (b:=s.precision) (M:=s.gatherLanes)
    (s.stripEnd base) key (s.prior base) m₁ srcFit safe (e₄.trans_lt space)
  have eqn:=ProtocolRAM.exec_unique _ m₁ _ dst real.1 native
  have rows:=DescentPlainTerminal.Suffix.grouped_remix cut pack outPos (s.primary base).base value L dst (dense 0)
  have capacity' : s.hosts*chunks (2^s.cut) s.outputLanes≤(s.primary base).size:=by
    have allDim : 2^s.cut*s.donors=2^(s.high+s.low):=by unfold donors;rw [←pow_add,Nat.add_sub_of_le cut]
    have chunksEq:=DescentSIMDLookup.chunks_group (2^s.cut) s.outputLanes s.donors outPos (Nat.two_pow_pos _)
    rw [allDim,pack,DescentGLPacked.chunk_count] at chunksEq
    rw [←chunksEq]
    exact Nat.le_pow_clog (by decide) _
  have fitBank':=s.primary_fit base (e₄.trans_lt space)
  intro j
  have inside:=(Nat.add_lt_add_left ((row _ _ _ j).isLt.trans_le capacity') _).trans_le fitBank'.2.2
  have kept:=(Arrivals.any (s.signedEnd base) s.degree s.capacity s.precision s.donors s.outputLanes
    (s.shuffled base key m₁) space).2.2.1 _ (.inl inside)
  apply kept.trans
  rw [show s.shuffled base key m₁=dst from eqn]
  exact rows j

theorem secondary_read (base : ℕ) (old : Fin s.blocks→Bank) (key : Bank) (m : Memory w)
    (keys : key.Fits w base) (fits : ∀b,(old b).Fits w base) (space : s.roof base<2^w)
    (signed : Fin (2*s.capacity)→Expr)
    (digits : Fin (2*s.capacity)→Fin s.hosts→Fin (2^s.cut)→Fin s.donors→Cell (DescentSignedCableCodec.width s.degree s.capacity))
    (early : ∀j,(signed j).Fits w base)
    (stored : ∀j,Source (signed j) (fun h g=>encode _ s.donors (digits j h g)) s.outputLanes m)
    (small : 2*s.capacity<2^s.precision) :
    (s.secondary base signed).Fits w (s.roof base) ∧ Source (s.secondary base signed)
      (fun h g=>encode s.precision s.donors (fun l=>⟨_,(Arrivals.count_le digits h g l).trans_lt small⟩))
      s.outputLanes (s.memory base old key m) :=by
  obtain ⟨e₁,e₂,e₃,e₄⟩:=s.order base
  have room:=((e₂.trans e₃).trans e₄).trans_lt space
  let m₁:=(s.copy base w old).image m
  let m₂:=s.shuffled base key m₁
  have srcFit (j : Fin 1) (b : Fin s.blocks) : (s.prior base j b).Fits w (s.stripEnd base):=
    ⟨(Strip.fits base s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision b room).1,trivial⟩
  have copy_:=Strip.any base s.hosts s.oldGroups s.oldLanes s.gatherLanes s.precision old m fits room
  have move:=SignedFields.from_slots_any (D:=1) (H:=s.hosts) (h:=s.high) (l:=s.low) (b:=s.precision) (M:=s.gatherLanes)
    (s.stripEnd base) key (s.prior base) m₁ srcFit ⟨keys.1,keys.2.1,keys.2.2.trans e₁⟩ (e₄.trans_lt space)
  have prior' (j : Fin (2*s.capacity)) : Source (signed j) (fun h g=>encode _ s.donors (digits j h g)) s.outputLanes m₂ :=by
    intro rowIndex
    apply (eval_below (signed j) _ m m₂ (early j) ?_).trans (stored j rowIndex)
    intro a lt
    exact (move.2.2 a (.inl (lt.trans_le e₁))).trans (copy_.2 a (.inl lt))
  exact Arrivals.source (s.signedEnd base) s.precision s.donors m₂ signed digits
    (fun j=>ProtocolRAMGeneratedWrite.fits_mono _ (e₁.trans (e₂.trans e₃)) (early j)) prior' small space

end
end Hierarchy.DescentFundedCensus.Setup

end OAI
