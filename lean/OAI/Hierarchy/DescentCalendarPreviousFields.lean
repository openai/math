import OAI.Hierarchy.DescentPhysicalPreviousFields
import OAI.Hierarchy.DescentPhysicalResetSignedFrame
import OAI.Hierarchy.DescentNamedResetDateInputs
import OAI.Hierarchy.DescentResetRankIntake

namespace OAI
/-! # The original public calendar on the installed candidate sheets -/
namespace Hierarchy.DescentResetRankedWindows.Layout
open ProtocolRAM
variable {X K Y J w : ℕ} (L : Layout X K) (hx : Y=X) (hj : J=K)

theorem previous_reindex : (L.reindex hx hj).Previous w ↔ L.Previous w := by
  subst Y; subst J; rfl

theorem finalRank_reindex (x : Fin Y) (a : Fin 3) (j : Fin J) :
    (L.reindex hx hj).finalRank x a j=L.finalRank (x.cast hx) a (j.cast hj) := by
  subst Y; subst J; rfl

open DescentSIMDLookup DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM

theorem tail_reindex_read {D D' C C' G G' b M H d : ℕ} (cap : C'=C) (deg : D'=D) (gg : G'=G)
    (base : ℕ) (m : Memory w) (rows : Fin X→Fin (2*C)→Fin H→Fin G→Cell d)
    (original : ∀x j,Reads (DescentResetWindowTail.page base X C b M H G x j) (rows x j) M
      (DescentResetWindowTail.memory base X D C b M H G L.header L.finalRank (L.memory m)))
    (x : Fin Y) (j : Fin (2*C')) :
    Reads (DescentResetWindowTail.page base Y C' b M H G' x j)
      (fun h g=>rows (x.cast hx) (j.cast (congrArg (2*·) cap)) h (g.cast gg)) M
      (DescentResetWindowTail.memory base Y D' C' b M H G' (L.reindex hx hj).header
        (L.reindex hx hj).finalRank ((L.reindex hx hj).memory m)) :=by
  subst Y;subst J;subst C';subst D';subst G';exact original x j

end Hierarchy.DescentResetRankedWindows.Layout

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentSharedCableNames DescentResetFieldAssembler DescentResetLocalRoster
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetRankedWindows
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentResetCandidatePair
open scoped Classical
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
variable {w : ℕ}
private theorem calendar_field_read {K H width : ℕ} (size : K=totalLocal B)
    (rack : Fin H→Option B.next.V) (host : Fin H) (grp : Fin (S.groupCount (i+1)))
    (block : Fin (2^k)) (j : Fin (2*K)) (fld : Fin 8) :
    let part : Fin 2 × Fin K := finProdFinEquiv.symm j
    (field (decide (part.1.val=1)) fld (actualMeta B rack block (part.2.cast size) host grp)
      (actualOffset (b:=width) B rack block (atField fld) (part.2.cast size) host grp).val : Cell width) =
      (DescentNextSignedWindow.Native.fields ((rack host).bind (fun z=>
        candidateRows B (fieldNames B) ((grp,z),block) (j.cast (congrArg (2*·) size)))) fld : Cell width) := by
  subst K
  intro part
  cases present : rack host with
  | none => simp [actualMeta,present,Meta.blank,field,face,DescentNextSignedWindow.Native.fields]
  | some z =>
    simp only [actualMeta,actualOffset,present,Option.bind_some,Option.elim_some]
    exact field_read (b:=width) B ((grp,z),block) j fld

/-- Relabel the reached four-rail source receipt from the shelf's finite host
and lane charts to their identical receiver sizes. -/
def rank_sources_at {H H' M M' b b' t t' st p : ℕ}
    (hosts : H'=H) (lanes : M'=M) («meta» : b'=b) (key : t'=t)
    (rack : Fin H→Option B.next.V) (ports : Ports 4) (mem : Memory w)
    (src : RankSources B («b»:=b) («t»:=t) (M:=M) rack ports
      (sheetHeader B st p) (sheetOriginal B st p) mem) :
    RankSources B (b:=b') (t:=t') (M:=M') (fun h=>rack (h.cast hosts)) ports
      (sheetHeader B st p) (sheetOriginal B st p) mem :=by
  subst H';subst M';subst b';subst t';exact src

private theorem num_source {a b H M k w : ℕ} (e : Expr) (v : Fin H→Fin b→Cell k)
    (m : Memory w) (h : a=b) (old : Source e v M m) : Source e (fun x g=>v x (g.cast h)) M m :=by
  subst a;exact old

local notation "N" => totalLocal B
local notation "X" => 2^k
local notation "gs" => S.groupCount (i+1)
local notation "ht" => GroupStage.depthBound D n f g
variable {a : PhysicalReset} {floor : ℕ} (I : a.DateInputs floor w)
local notation "v" => a.successor
local notation "base" => a.rebased floor
local notation "A" => (v).receiver
local notation "ss" => I.sectors
local notation "ST" => (v).sheetsStart base
local notation "plan" => (v).linkedRankInputs ss ST
local notation "head₀" => sheetHeader B ST (ss).pageBits
local notation "key₀" => sheetOriginal B ST (ss).pageBits
local notation "native" => (v).rankBook plan base
local notation "b" => (v).assemblerBits
local notation "t" => (v).ticketBits
local notation "P₀" => (v).rankPorts base
local notation "L" => rankLayout B ((v).rankPortEnd base) (A).hosts b t (A).lanes P₀ head₀ key₀
variable (hx : a.successor.receiver.blocks=2^k) (hj : a.successor.receiver.candidates=totalLocal B)
  (gg : a.successor.receiver.groups=S.groupCount (i+1))

set_option maxHeartbeats 800000 in
/-- The mounted source and target column dictionaries agree on each numerical
candidate. Only the finite upper bounds of their row charts change. -/
theorem linked_calendar (before : (ss).before=publicBefore D k n ht (S.groupWidth k tail i)
      input.placement.cap (programCount ctl.board ht))
    (slot : ∀j,(ss).sourceSlot j=publicSourceSlot D k n ht input.placement.cap (programCount ctl.board ht)
       (A).candidates j.val) :
    plan=datedRankInputs B (ss).ports head₀ key₀ v hx hj :=by
  let size:=CandidateSheet.size (ss).stems (ss).contacts (ss).privates
  have count : size=N:=(ss).count.symm.trans hj
  have gate : (ss).sourceSlot=fun j=>slotGate B (j.cast hj):=by
    funext j
    exact (slot j).trans
      ((congrArg (fun n₀=>publicSourceSlot D k n ht input.placement.cap (programCount ctl.board ht) n₀ j.val)
          (hj.trans (local_roster_exact B))).trans (slot_at_date B (j.cast hj)).symm)
  have heads : (plan).header=fun x j=>head₀ (x.cast hx) (j.cast hj):=by
    funext x j
    simp only [ResetOutput.linkedRankInputs,sheetHeader,CandidateSheet.output,finProdFinEquiv_apply_val,
      Fin.val_cast]
    change Expr.lookup ⟨ST+(j.val+size*x.val)*2^(ss).pageBits,(ss).pageBits⟩ .row=_
    rw [count]
    rfl
  have keys : (plan).original=fun x j=>key₀ (x.cast hx) (j.cast hj):=by
    funext x j
    simp only [ResetOutput.linkedRankInputs,sheetOriginal,sheetHeader,CandidateSheet.output,
      finProdFinEquiv_apply_val,Fin.val_cast,originalBase]
    change Expr.lookup ⟨ST+(A).blocks*size*2^(ss).pageBits+(j.val+size*x.val)*2^(ss).pageBits,(ss).pageBits⟩ .row=_
    rw [congrArg (fun blocks => blocks*size) hx,count]
    rfl
  have prior : (ss).before=wordBefore B:=before.trans (before_at_date B).symm
  have sameInputs (x y : (v).RankInputs) (p_eq : x.ports=y.ports) (before_eq : x.before=y.before)
      (s : x.sourceSlot=y.sourceSlot) (h : x.header=y.header) (o : x.original=y.original) : x=y:=by
    cases x;cases y;simp_all
  apply sameInputs (plan) (datedRankInputs B (ss).ports head₀ key₀ v hx hj)
  · rfl
  · exact prior
  · dsimp only [ResetOutput.linkedRankInputs,datedRankInputs]
    exact gate
  · dsimp only [ResetOutput.linkedRankInputs,datedRankInputs] at heads ⊢
    exact heads
  · dsimp only [ResetOutput.linkedRankInputs,datedRankInputs] at keys ⊢
    exact keys

variable (before : I.sectors.before=publicBefore D k n (GroupStage.depthBound D n f g) (S.groupWidth k tail i)
      input.placement.cap (programCount ctl.board (GroupStage.depthBound D n f g)))
    (slot : ∀j,I.sectors.sourceSlot j=publicSourceSlot D k n (GroupStage.depthBound D n f g) input.placement.cap (programCount ctl.board (GroupStage.depthBound D n f g))
      a.successor.receiver.candidates j.val)
local notation "aligned" => linked_calendar B I hx hj before slot
variable (rack : Fin a.successor.receiver.hosts→Option B.next.V) (ok : I.Ready) (m : Memory w)
local notation "portMem" => ((v).rankPortPhase base w).image (I.candidateEntry ok m)
variable (src : RankSources B («b»:=a.successor.assemblerBits) («t»:=a.successor.ticketBits) (M:=a.successor.receiver.lanes) rack (a.successor.rankPorts (a.rebased floor))
    (sheetHeader B (a.successor.sheetsStart (a.rebased floor)) I.sectors.pageBits)
    (sheetOriginal B (a.successor.sheetsStart (a.rebased floor)) I.sectors.pageBits)
    ((a.successor.rankPortPhase (a.rebased floor) w).image (I.candidateEntry ok m)))
local notation "meta₀" => fun x j h g=>actualMeta B rack (Fin.cast hx x) (Fin.cast hj j) h (Fin.cast gg g)
local notation "off₀" => fun x p j h g=>actualOffset («b»:=b) B rack (Fin.cast hx x) p (Fin.cast hj j) h (Fin.cast gg g)

private theorem cast_field_width {width₁ width₂ x y : ℕ} (width : width₁=width₂) (atWidth : (x : Cell width₂)=(y : Cell width₂)) :
    (x : Cell width₁)=(y : Cell width₁) := by
  subst width₁
  exact atWidth

include hx hj gg before slot src

set_option maxHeartbeats 2000000 in
/-- All fresh-candidate inputs to the actual seven-field date, including the
zero inputs for the four retained-only fields. The ranks are computed by the
installed program on the original cable keys and the compact four-port roster. -/
theorem calendar_previous_read (i j) :
    Source ((v).previous I.operand ((v).renderFromRanks plan base) base i j)
      ((v).previousValue I.operand meta₀ off₀ i j) (A).lanes (I.operandEntry ok m) :=by
  have book : native=(L).reindex hx hj :=by
    rw [aligned]
    exact rank_book_compatible B (ss).ports head₀ key₀ v base hx hj gg
  have nativeBefore:=ok.ranks
  rw [book] at nativeBefore
  have previous:=(Layout.previous_reindex L hx hj).mp nativeBefore
  obtain ⟨_,_,mem,cut⟩:=(L).reindex_code hx hj portMem
  have end₀ : (v).rankEnd base=(L).endAddress:=
    (congrArg (fun l:Layout (A).blocks (A).candidates=>l.endAddress) book).trans cut
  have current : (native).memory portMem=(L).memory portMem:=
    (congrArg (fun l=>Layout.memory l portMem) book).trans mem
  have bounds:=(v).control_address_bounds base
  have long : (v).controlFloor base<2^w:=(bounds.2.2.1.trans bounds.2.2.2).trans_lt ok.full
  have span : (v).rankEnd base≤(v).controlFloor base:=by
    change (v).rankEnd base≤DescentNextSignedWindow.Native.All.endAddress ((v).fieldsEnd base) _ _ _ _ _ _
    unfold ResetOutput.fieldsEnd DescentResetFieldAssembler.endAddress DescentNextSignedWindow.Native.All.endAddress
    omega
  have room : (L).endAddress<2^w:=end₀ ▸ span.trans_lt long
  have result:=ranked_fields B rack ((v).rankPortEnd base) P₀ head₀ key₀ portMem src previous room
  apply I.previous_read ok m meta₀ off₀
  · intro x j
    have eqHead:=congrArg (fun (p:(v).RankInputs)=>p.header x j) aligned
    rw [eqHead,current]
    exact num_source _ _ _ gg (result.2.1 (x.cast hx) (j.cast hj)).2
  · intro x p j
    rw [current,book,Layout.finalRank_reindex]
    exact num_source _ _ _ gg (result.2.2.1 (x.cast hx) p (j.cast hj)).2
  · intro x j h g t₀
    exact meta_room B rack src.near src.small (x.cast hx) (j.cast hj) h (g.cast gg) t₀

set_option maxHeartbeats 800000 in
/-- In particular the three new scalar fields are the live, peer, and offset
fields of the mathematically identified original cable at the selected slot. -/
theorem calendar_candidate_read (i j) :
    let x:=(v).operandIndex I.operand i
    Source ((v).previous I.operand ((v).renderFromRanks plan base) base i j)
      (fun h g=>(ResetOutput.pointerField x.2.1).elim (0:Cell (A).signedBits) (fun f=>
        (DescentNextSignedWindow.Native.fields ((rack h).bind (fun z=>
          candidateRows B (fieldNames B) ((g.cast gg,z),x.1.cast hx) (j.cast (congrArg (2*·) hj)))) f : ℕ)))
      (A).lanes (I.operandEntry ok m) :=by
  intro x
  have lower:=calendar_previous_read B I hx hj gg before slot rack ok m src i j
  convert lower using 2
  rename_i h
  funext g
  symm
  cases f : ResetOutput.pointerField x.2.1 with
  | none=>simp only [ResetOutput.previousValue,←show x=(v).operandIndex I.operand i from rfl,f,Option.elim_none]
  | some f₀=>
    simp only [ResetOutput.previousValue,←show x=(v).operandIndex I.operand i from rfl,f,Option.elim_some]
    apply cast_field_width ok.width
    exact calendar_field_read B hj rack h (g.cast gg) (x.1.cast hx) j f₀

set_option maxHeartbeats 800000 in
/-- The same original candidate and rank books emit each successor's signed cable
panel into the actual physical bank used at the following date. -/
theorem calendar_signed_output (cap : (A).capacity=B.next.placement.cap)
    (degree : I.degree=B.next.placement.degree)
    (digits : max (B.next.placement.degree+1) (B.next.placement.cap+1)<2^b)
    (x : Fin (A).blocks) (j : Fin (2*(A).capacity)) :
    Reads (DescentResetWindowTail.page ((v).rankEnd base) (A).blocks (A).capacity b
      (A).lanes (A).hosts (A).groups x j)
      (fun h g=>DescentSignedCableCodec.encode ((rack h).bind (fun z=>Stage.signedPanel
        B.next.placement (B.next.order.trans Fin.valEmbedding) S B.next.valid (fieldNames B)
        ((g.cast gg,z),x.cast hx) (j.cast (congrArg (2*·) cap))))) (A).lanes
      ((v).renderMemory ((v).renderFromRanks plan base) base I.degree ((native).memory portMem)) :=by
  have book : native=(L).reindex hx hj :=by
    rw [aligned]
    exact rank_book_compatible B (ss).ports head₀ key₀ v base hx hj gg
  have previous:=ok.ranks
  rw [book] at previous
  have input:=(Layout.previous_reindex L hx hj).mp previous
  have end₀ : (v).rankEnd base=(L).endAddress:=
    (congrArg (fun l:Layout (A).blocks (A).candidates=>l.endAddress) book).trans
      ((L).reindex_code hx hj portMem).2.2.2
  have range:=(v).control_address_bounds base
  have extent : (A).rendered ((v).fieldsEnd base)<2^w:=
    (range.2.2.1.trans range.2.2.2).trans_lt ok.full
  have floor₀:=(v).render_end base ok.width
  have room : DescentResetWindowTail.endAddress (L).endAddress X B.next.placement.cap b
      (A).lanes (A).hosts gs<2^w:=by
    have seen:=floor₀.le.trans_lt extent
    simpa only [end₀,hx,cap,gg] using seen
  have signed:=(signed_memory B rack ((v).rankPortEnd base) P₀ head₀ key₀ portMem src input room digits).2.1
  change Reads _ _ _ (DescentResetWindowTail.memory _ _ _ _ _ _ _ _ (native).header
    (native).finalRank ((native).memory portMem))
  rw [book,end₀]
  exact (L).tail_reindex_read hx hj cap degree gg (L).endAddress portMem _ signed x j

/-- Carry those very same signed panels to the destination of the entire native
reset operation, after the operand and node processors execute. -/
theorem calendar_signed_sheets (cap : (A).capacity=B.next.placement.cap)
    (degree : I.degree=B.next.placement.degree)
    (digits : max (B.next.placement.degree+1) (B.next.placement.cap+1)<2^b)
    (x : Fin (A).blocks) (j : Fin (2*(A).capacity)) :
    Reads ((PhysicalReset.FinalInputs.predecessor I).signed x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode ((rack h).bind (fun r=>Stage.signedPanel
        B.next.placement (B.next.order.trans Fin.valEmbedding) S B.next.valid (fieldNames B)
        ((g.cast gg,r),x.cast hx) (j.cast (congrArg (2*·) cap))))) (A).lanes (I.sheetsResult ok m) :=by
  apply I.signed_at_sheets ok m x j
  have original:=calendar_signed_output B I hx hj gg before slot rack ok m src cap degree digits x j
  have same : DescentNextSignedWindow.Native.All.page ((v).fieldsEnd base) (A).blocks (A).capacity
      (A).signedBits (A).lanes (A).hosts (A).groups x j =
      DescentResetWindowTail.page ((v).rankEnd base) (A).blocks (A).capacity b (A).lanes (A).hosts (A).groups x j := by
    rw [ok.width]
    rfl
  rw [same]
  exact original

theorem calendar_signed_date (cap : (A).capacity=B.next.placement.cap)
    (degree : I.degree=B.next.placement.degree)
    (digits : max (B.next.placement.degree+1) (B.next.placement.cap+1)<2^b)
    (z : I.FinalInputs) (room : z.Room) {first out : Memory w}
    (head : I.throughOperandDate.Runs first (I.sheetsResult ok m)) (run : (PhysicalReset.date z).Runs first out)
    (x : Fin (A).blocks) (j : Fin (2*(A).capacity)) :
    Reads ((PhysicalReset.FinalInputs.predecessor I).signed x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode ((rack h).bind (fun r=>Stage.signedPanel
        B.next.placement (B.next.order.trans Fin.valEmbedding) S B.next.valid (fieldNames B)
        ((g.cast gg,r),x.cast hx) (j.cast (congrArg (2*·) cap))))) (A).lanes out :=by
  apply PhysicalReset.signed_at_date z ok room m head run x j
  have original:=calendar_signed_output B I hx hj gg before slot rack ok m src cap degree digits x j
  have same : DescentNextSignedWindow.Native.All.page ((v).fieldsEnd base) (A).blocks (A).capacity
      (A).signedBits (A).lanes (A).hosts (A).groups x j =
      DescentResetWindowTail.page ((v).rankEnd base) (A).blocks (A).capacity b (A).lanes (A).hosts (A).groups x j := by
    rw [ok.width]
    rfl
  rw [same]
  exact original

end
end Hierarchy.DescentSixParty.ClosedReset.Window

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1100000
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
  (sceneRoom : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom

open DescentResetLocalRoster DescentSixParty.ClosedReset.Window
/-- All the order, pitch, and room parameters of the emitted rank controller
follow from the genuine previous date's degree and charged capacity. -/
theorem fromNamed_rank_coordinates (ports : venue.degree=D) (paid : input.placement.cap=cap) :
    (v).receiver.blocks=2^k ∧ (v).receiver.candidates=totalLocal B ∧
    (v).receiver.groups=S.groupCount (age+1) ∧ (v).receiver.hosts=(v).sheets.hosts ∧
    (v).receiver.lanes=(v).sheets.lanes ∧ (v).assemblerBits=(v).sheets.metaBits ∧
    (v).ticketBits=originalBits D k n (GroupStage.depthBound D n f g) input.placement.cap
      (programCount board (GroupStage.depthBound D n f g)) g ∧
    (u).sectors.before=publicBefore D k n (GroupStage.depthBound D n f g) cc
      input.placement.cap (programCount board (GroupStage.depthBound D n f g)) ∧
    (∀j,(u).sectors.sourceSlot j=publicSourceSlot D k n (GroupStage.depthBound D n f g)
      input.placement.cap (programCount board (GroupStage.depthBound D n f g)) (v).receiver.candidates j.val) ∧
    (v).receiver.capacity=B.next.placement.cap ∧ (u).degree=B.next.placement.degree ∧
    max (B.next.placement.degree+1) (B.next.placement.cap+1)<2^(v).assemblerBits :=by
  refine ⟨rfl,?_,rfl,rfl,rfl,rfl,?_,?_,?_,?_,B.next.branch.symm,?_⟩
  · change publicSlots board Ht k cap=totalLocal B
    rw [ports,←paid,local_roster_exact B]
  · change originalBits venue.degree k n Ht cap (programCount board Ht) g=_
    rw [ports,paid]
  · change publicBefore venue.degree k n Ht cc cap (programCount board Ht)=_
    rw [ports,paid]
  · intro j
    have sameFn : publicSourceSlot venue.degree k n Ht cap (programCount board Ht) =
        publicSourceSlot D k n (GroupStage.depthBound D n f g) input.placement.cap
          (programCount board (GroupStage.depthBound D n f g)) := by rw [ports, paid]
    exact congrFun (congrFun sameFn (v).receiver.candidates) j.val
  · change 2^g*cap=B.next.placement.cap
    rw [←paid,B.next_capacity]
  · apply (signed_digit_room B).trans_le
    apply Nat.pow_le_pow_right (by decide : 0<2)
    rw [paid]
    exact le_max_left _ _


local notation "A₁" => (v).receiver
local notation "G₁" => S.groupCount (age+1)
local notation "ST" => (v).sheetsStart base₀
local notation "plan" => (v).linkedRankInputs (u).sectors ST
local notation "draw" => (v).renderFromRanks plan base₀
local notation "keyWidth" => originalBits D k n (GroupStage.depthBound D n f g)
  input.placement.cap (programCount board (GroupStage.depthBound D n f g)) g
open DescentSharedCableNames
/-- The original shelf receipt for the actual named date suffices simultaneously
for the three refreshed operand fields and the completed successor signed bank. -/
theorem fromNamed_ranked_reads (ports : venue.degree=D) (paid : input.placement.cap=cap)
    (ok : (u).Ready) (m : Memory w) (rack : Fin (v).sheets.hosts→Option B.next.V)
    (src : RankSources B (b:=(v).sheets.metaBits) (t:=keyWidth) (M:=(v).sheets.lanes)
      rack ((v).rankPorts base₀) (sheetHeader B ST (u).sectors.pageBits) (sheetOriginal B ST (u).sectors.pageBits)
      (((v).rankPortPhase base₀ w).image ((u).candidateEntry ok m)))
    (last : (u).FinalInputs) (room : last.Room) {first out : Memory w}
    (toOperands : (u).throughOperandDate.Runs first ((u).sheetsResult ok m)) (toFinal : (date last).Runs first out) :
    ∃ (hx : (A₁).blocks=2^k) (hj : (A₁).candidates=totalLocal B)
      (gg : (A₁).groups=G₁) (capAt : (A₁).capacity=B.next.placement.cap)
      (alignedHosts : (A₁).hosts=(v).sheets.hosts),
      (∀i j,let x:=(v).operandIndex (u).operand i
        Source ((v).previous (u).operand draw base₀ i j)
          (fun h g=>(ResetOutput.pointerField x.2.1).elim (0:Cell (A₁).signedBits) (fun f=>
             (DescentNextSignedWindow.Native.fields ((rack (h.cast alignedHosts)).bind (fun z=>
                candidateRows B (fieldNames B) ((g.cast gg,z),x.1.cast hx) (j.cast (congrArg (2*·) hj)))) f:ℕ)))
          (A₁).lanes ((u).operandEntry ok m)) ∧
      ∀(x:Fin (A₁).blocks) (j:Fin (2*(A₁).capacity)), Reads ((FinalInputs.predecessor u).signed x.val j.val)
        (fun (h:Fin (A₁).hosts) (g:Fin (A₁).groups)=>DescentSignedCableCodec.encode
          ((rack (h.cast alignedHosts)).bind (fun r=>Stage.signedPanel B.next.placement
           (B.next.order.trans Fin.valEmbedding) S B.next.valid (fieldNames B)
           ((g.cast gg,r),Fin.cast hx x) (Fin.cast (congrArg (2*·) capAt) j)))) (A₁).lanes out :=by
  obtain ⟨hx,hj,gg,hosts,lanes,«meta»,key,before,slot,capa,deg,fit⟩:=
    fromNamed_rank_coordinates (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom ports paid
  let retyped:=rank_sources_at B hosts lanes «meta» key rack ((v).rankPorts base₀)
    (((v).rankPortPhase base₀ w).image ((u).candidateEntry ok m)) src
  exact ⟨hx,hj,gg,capa,hosts,
    calendar_candidate_read B (u) hx hj gg before slot _ ok m retyped,
    calendar_signed_date B (u) hx hj gg before slot _ ok m retyped capa deg fit last room toOperands toFinal⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
