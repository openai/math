import OAI.Hierarchy.DescentCalendarPreviousFields
import OAI.Hierarchy.DescentDatedRetainedSources
import OAI.Hierarchy.DescentPulledRetainedFee

namespace OAI
/-! # The physical source-sibling ticket at the recorded reset -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentSharedCableNames DescentResetFieldAssembler DescentResetLocalRoster
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetRankedWindows
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentResetCandidatePair
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "N" => totalLocal B
local notation "X" => 2^k
local notation "gs" => S.groupCount (i+1)
local notation "ht" => GroupStage.depthBound D n f g
variable {a : PhysicalReset} {floor w : ℕ} (I : a.DateInputs floor w)
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
variable (hx : (A).blocks=X) (hj : (A).candidates=N) (gg : (A).groups=gs)

variable (before : (ss).before=publicBefore D k n ht (S.groupWidth k tail i)
      input.placement.cap (programCount ctl.board ht))
    (slot : ∀j,(ss).sourceSlot j=publicSourceSlot D k n ht input.placement.cap (programCount ctl.board ht)
      (A).candidates j.val)
local notation "aligned" => linked_calendar B I hx hj before slot
variable (rack : Fin (A).hosts→Option B.next.V) (ok : I.Ready) (m : Memory w)
local notation "portMem" => ((v).rankPortPhase base w).image (I.candidateEntry ok m)
variable (src : RankSources B («b»:=b) («t»:=t) (M:=(A).lanes) rack P₀ head₀ key₀ portMem)
open DescentResetSourceTicketCompare DescentResetTrunkCompactPointer
open scoped BigOperators
local notation "rk" => (native).memory portMem
local notation "F₀" => (v).front
local notation "C₀" => (v).setup
local notation "cut₀" => (v).actorEnd base
local notation "old₀" => (v).issuedScene base I.earlier
local notation "first₀" => (v).operandFloor base
local notation "last₀" => ((C₀).code first₀ w I.bank I.laws).image (I.beforeSetupImage ok m)

private theorem reads_sizes {H H' G G' a a' M M' w : ℕ}
    (host : H'=H) (group : G'=G) (bitsAt : a'=a) (lanes : M'=M)
    (bank : Bank) (value : Fin H→Fin G→Cell a) (mem : Memory w) (old : Reads bank value M mem) :
    Reads bank (fun h g=>Fin.cast (congrArg (fun z=>2^z) bitsAt.symm) (value (h.cast host) (g.cast group))) M' mem:=by
  subst H';subst G';subst a';subst M';exact old

private theorem reads_groups {H G G' a M w : ℕ}
    (group : G'=G) (bank : Bank) (value : Fin H→Fin G→Cell a) (mem : Memory w)
    (old : Reads bank value M mem) :
    Reads bank (fun h g=>value h (g.cast group)) M mem := by
  subst G'
  exact old

include before slot src in
set_option maxHeartbeats 800000 in
/-- Weighted original-ordinal prefix on every physical column of the rank
program, including absent rows and the last incomplete packed group. -/
theorem calendar_ticket_bank (x : Fin (A).blocks) (j : Fin (A).candidates) :
    Reads ((native).oldBank x j) (fun (h : Fin (A).hosts) (g₀ : Fin (A).groups)=>((∑l : Fin N,feeAt (wordBefore B)
      (original_fees («b»:=t) B rack (x.cast hx) h (g₀.cast gg)) (j.cast hj) l : ℕ):Cell b))
      (A).lanes rk :=by
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
  have h:=ranked_ticket_bank B rack ((v).rankPortEnd base) P₀ head₀ key₀ portMem src previous room (x.cast hx) (j.cast hj)
  have shift (l : Layout X N) {X' N' : ℕ} (xx : X'=X) (nn : N'=N) (x₁ : Fin X') (j₁ : Fin N') :
      (l.reindex xx nn).oldBank x₁ j₁=l.oldBank (x₁.cast xx) (j₁.cast nn):=by
    subst X';subst N';rfl
  rw [current,show (native).oldBank x j=(L).oldBank (x.cast hx) (j.cast hj) by rw [book];exact shift L hx hj x j]
  exact reads_groups (H:=(A).hosts) (a:=b) (M:=(A).lanes) gg
    ((L).oldBank (x.cast hx) (j.cast hj))
    (fun h₀ g₀=>((∑l : Fin N, feeAt (wordBefore B)
      (original_fees («b»:=t) B rack (x.cast hx) h₀ g₀) (j.cast hj) l : ℕ) : Cell b))
    ((L).memory portMem) h

variable (blocks : (C₀).placement.blocks=(A).blocks)
    (slots : ∀d : Fin (C₀).strip, (F₀).signedQueries/2+d.val<(A).candidates)
    (hosts : (F₀).newHosts=(A).hosts) (groups : (F₀).peer.groups=(A).groups)
    (lanes : (F₀).peer.lanes=(A).lanes) (pitch : (C₀).lanes=(F₀).peer.lanes)
    (width : (C₀).ticketBits=b)
    {N₀ «P₀ʹ» : ℕ} (rosterSize : «P₀ʹ»=(F₀).peer.hosts) (name : Fin N₀→Fin «P₀ʹ») (other : Fin N₀→Option (Fin N₀))
    (live : N₀≤(F₀).newHosts) (active : N₀≤(old₀).inverse.size)
    (census : Measured ((F₀).trunkBanks cut₀ old₀) name other (((F₀).received cut₀ old₀ I.sceneFits).image m))

include before slot src lanes pitch rosterSize active census in
set_option maxHeartbeats 800000 in
/-- The carried operand reads the original unpermuted donor's true incoming
chronology through the source sibling at its reached compact actor. -/
theorem recorded_ticket_at (x : Fin (C₀).placement.blocks) (d₀ : Fin (C₀).strip) :
    let j : Fin (A).candidates:=⟨_,slots d₀⟩
    let value (h : Fin (F₀).newHosts) (g : Fin (F₀).peer.groups) : Cell (C₀).ticketBits :=
      Fin.cast (congrArg (fun z=>2^z) width.symm)
        (((∑l : Fin N,feeAt (wordBefore B) (original_fees («b»:=t) B rack (x.cast (blocks.trans hx))
          (h.cast hosts) (g.cast (groups.trans gg))) (j.cast hj) l : ℕ):Cell b))
    ((v).retainedTicket base x d₀).Fits w ((C₀).casts first₀) ∧
      DescentPackedZip.Source ((v).retainedTicket base x d₀)
        (fun h g=>(((pointer live other h).elim 0 (fun r=>value r g)).val:Cell (C₀).fieldBits)) (C₀).lanes last₀ :=by
  intro j value
  have at_:=calendar_ticket_bank B I hx hj gg before slot rack ok m src (x.cast blocks) j
  have stored : Reads ((v).incomingTicketBank base x.val d₀.val) value (F₀).peer.lanes rk:=
    reads_sizes (H:=(A).hosts) (G:=(A).groups) (a:=b) (M:=(A).lanes)
      hosts groups width lanes ((native).oldBank (x.cast blocks) j)
      (fun h₀ g₀=>((∑l : Fin N, feeAt (wordBefore B) (original_fees («b»:=t) B rack
        (x.cast (blocks.trans hx)) h₀ (g₀.cast gg)) (j.cast hj) l : ℕ) : Cell b))
      rk at_
  exact I.dated_ticket_rows ok m x d₀ blocks (slots d₀) hosts groups lanes pitch rosterSize name other live active census value stored

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
