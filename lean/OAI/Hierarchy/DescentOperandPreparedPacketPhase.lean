import OAI.Hierarchy.DescentOperandRootPull
import OAI.Hierarchy.DescentResetRootAllocator
import OAI.Hierarchy.DescentRotorWindowArchive

namespace OAI
/-! # Both original root-operand banks on one dated reset tape -/
namespace Hierarchy.DescentOperandRootPull
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open DescentSixParty.Chronology DescentResetHostSize DescentHostDirectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Pair where
  rootStart : ℕ
  parent : ℕ
  actors : ℕ
  receivers : ℕ
  groups : ℕ
  blocks : ℕ
  oldBits : ℕ
  beforeLanes : ℕ
  afterLanes : ℕ
  degree : ℕ
  cap : ℕ
  residual : ℕ
  rotorBits : ℕ

namespace Pair
variable (P : Pair)
def initialCode : Code P.residual:=⟨(0,0),mem_codes (Nat.zero_le _) (by decide)⟩
def page (matrix : Bool) : RootPage P.residual (2^P.rotorBits) :=
  if matrix then (false,.inl (P.initialCode,.inl false)) else (false,.inr (P.initialCode,none))
def stage (b : ℕ) (f : Bool) : Layout :=
  ⟨b,P.parent,P.actors,P.receivers,P.groups,P.blocks,P.oldBits,
    if f then DescentRotorWindowArchive.count P.degree (2^P.residual) P.cap
    else DescentFallbackPeriod.inputCount P.degree (2^P.residual) P.cap P.rotorBits P.residual,
    P.beforeLanes,P.afterLanes⟩
def packed (f : Bool) : Bank :=
  let G:=P.groups*P.blocks
  let a:=RootTemplates.arena P.rootStart P.actors G P.beforeLanes P.residual P.rotorBits P.degree
  ⟨a.middle (rootIndex P.residual (2^P.rotorBits) (P.page f)).val,Nat.clog 2 (P.actors*chunks G P.beforeLanes)⟩
def original (f : Bool) : Expr :=.lookup (P.packed f) .row
def lane (b : ℕ) (f : Bool) : Layout :=P.stage (if f then (P.stage b false).endAddress else b) f
def endAddress (b : ℕ) :=(P.lane b true).endAddress
def program (b w : ℕ) :=
  ((P.lane b false).program (P.original false) w).seq ((P.lane b true).program (P.original true) w)
def time (b w : ℕ) :=(P.lane b false).clock (P.original false) w+(P.lane b true).clock (P.original true) w
def image {w : ℕ} (b : ℕ) (m : Memory w) :=(P.lane b true).image (P.original true) ((P.lane b false).image (P.original false) m)
def src (b : ℕ) (f : Bool) (i : Fin (P.stage 0 f).fields) (x : Fin P.blocks) :=(P.lane b f).src i x
def Fits (w b : ℕ) : Prop :=(∀f,(P.original f).Fits w b) ∧ P.parent+span P.receivers≤b ∧ 0<P.afterLanes ∧ 0<P.blocks

theorem join (b : ℕ) : b≤(P.lane b false).endAddress ∧ (P.lane b false).endAddress≤P.endAddress b :=
  ⟨(P.lane b false).base_le,(P.lane b true).base_le⟩
theorem extent (b : ℕ) : P.endAddress b=b+P.endAddress 0 := by
  change (P.stage (P.stage b false).endAddress true).endAddress=b+(P.stage (P.stage 0 false).endAddress true).endAddress
  rw [(P.stage (P.stage b false).endAddress true).extent,(P.stage b false).extent,
    (P.stage (P.stage 0 false).endAddress true).extent]
  simp only [stage]
  omega

theorem any {w : ℕ} (b : ℕ) (m : Memory w) (held : P.Fits w b) (room : P.endAddress b<2^w) :
    (P.program b w).Exec m (P.image b m) (P.time b w) ∧ CheapCode (P.program b w) ∧
    ∀z,z<b ∨ P.endAddress b≤z→P.image b m z=m z := by
  have lo:=P.join b
  have a:=(P.lane b false).any (P.original false) m held.2.2.1 held.2.2.2 (held.1 false) (lo.2.trans_lt room)
  have c:=(P.lane b true).any (P.original true) ((P.lane b false).image (P.original false) m)
    held.2.2.1 held.2.2.2 (ProtocolRAMGeneratedWrite.fits_mono _ lo.1 (held.1 true)) room
  refine ⟨?_,cheap_seq a.2.1 c.2.1,?_⟩
  · intro np nr nk machine pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then a.1 c.1 machine pc reg pub exit rom advice cfg raw enter same
  · rintro z (low|high)
    · exact (c.2.2 z (.inl (low.trans_le lo.1))).trans (a.2.2 z (.inl low))
    · exact (c.2.2 z (.inr high)).trans (a.2.2 z (.inr (lo.2.trans high)))

theorem read {w : ℕ} (b : ℕ) (m : Memory w)
    (value : ∀f,Fin P.actors→Fin (P.groups*P.blocks)→Fin (P.stage 0 f).fields→Cell P.oldBits)
    (owner : Fin P.receivers→Fin P.actors) (held : P.Fits w b) (ha : 0<P.beforeLanes)
    (stored : ∀f,Source (P.original f) (fun u g=>encode P.oldBits (P.stage 0 f).fields (value f u g)) P.beforeLanes m)
    (owners : DescentResetStemKeyReindex.Directory P.parent owner m) (room : P.endAddress b<2^w) :
    ∀f i x,(P.src b f i x).Fits w (P.endAddress b) ∧ Source (P.src b f i x)
      (fun v g=>value f (owner v) (finProdFinEquiv (g,x)) i) P.afterLanes (P.image b m) := by
  have lo:=P.join b
  let start:=(P.lane b false).image (P.original false) m
  have fst_ :=(P.lane b false).run (P.original false) m (value false) owner ha held.2.2.1 held.2.2.2
    (held.1 false) (stored false) owners held.2.1 (lo.2.trans_lt room)
  have source2 : Source (P.original true) (fun v g=>encode P.oldBits _ (value true v g)) P.beforeLanes start := by
    intro row
    exact (eval_below _ _ m start (held.1 true) (fun z h=>fst_.2.2.2 z (.inl h))).trans (stored true row)
  have own2 : DescentResetStemKeyReindex.Directory P.parent owner start := by
    intro v
    rw [show start (P.parent+v.val)=m (P.parent+v.val) from fst_.2.2.2 _ (.inl
      ((Nat.add_lt_add_left (v.isLt.trans_le (span_ge _)) _).trans_le held.2.1))]
    exact owners v
  have snd_ :=(P.lane b true).run (P.original true) start (value true) owner ha held.2.2.1 held.2.2.2
    (ProtocolRAMGeneratedWrite.fits_mono _ lo.1 (held.1 true)) source2 own2 (held.2.1.trans lo.1) room
  intro f i x
  cases f
  · obtain ⟨fits,source⟩:=fst_.2.2.1 i x
    refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ lo.2 fits,?_⟩
    intro row
    exact (eval_below _ _ start _ fits (fun z h=>snd_.2.2.2 z (.inl h))).trans (source row)
  · exact snd_.2.2.1 i x

end Pair
end
end Hierarchy.DescentOperandRootPull

end OAI
