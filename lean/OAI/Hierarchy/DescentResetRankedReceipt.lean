import OAI.Hierarchy.DescentResetLocalRankRun
import OAI.Hierarchy.DescentResetRankedWindows
import OAI.Hierarchy.DescentResetActualSourcePull
import OAI.Hierarchy.DescentResetOriginalFees

namespace OAI
/-! # Authentic mixed reset headers and original cable keys issue every fresh rank -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetLocalRoster
open scoped Classical BigOperators Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "H₀" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H₀*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k

open DescentPackedColony DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentResetFieldAssembler
local notation "K" => totalLocal B
local notation "X" => 2^k
local notation "grp" => S.groupCount (i+1)
local notation "entry" => (Z).rawHostRank T vertex
open DescentResetRankedWindows DescentResetSourceTicketCompare DescentResetFieldAssembler
variable {H M b t Wd : ℕ} (rack : Fin H→Option B.next.V)

/-- The concrete date chooses both lookup functions from its original installed
word codec. Neither depends on which of the candidate rows is active. -/
def rankLayout (base H b t M : ℕ) (ports : Ports 4) (header original : Fin X→Fin K→Expr) : Layout X K :=
  ⟨base,b,t,M,H,grp,ports,wordBefore B,slotGate B,header,original⟩

variable (base : ℕ) (ports : Ports 4) (header original : Fin (2^k)→Fin (totalLocal B)→Expr)
local notation "Λ" => rankLayout B base H b t M ports header original

structure RankSources (m : Memory Wd) : Type where
  name : B.next.V↪Fin H
  ordered : ∀v u : B.next.V,name v<name u↔entry v<entry u
  anchor : ∀v u,rack v=some u→name u=v
  complete : ∀u,rack (name u)=some u
  peer : Fin H→Fin 4→Option (Fin H)
  roster : ∀u,DescentSortedRoster.present peer (name u)=(insert u (B.next.placement.near u)).map name
  capacity : B.next.placement.degree+1≤4
  mounted : Mounted ports (DescentSortedRoster.indexed peer) m grp M
  measured : ∀x j,Source (header x j) (fun h g=>DescentResetFieldAssembler.raw b (actualMeta B rack x j h g)) M m
  words : ∀x : Fin (2^k), ∀j : Fin (totalLocal B), Source (original x j) (fun h : Fin H => fun g : Fin (S.groupCount (i+1)) => (actualParentNumber B rack x j h g : Cell t)) M m
  small : B.next.placement.cap<2^b
  near : B.next.placement.degree+1<2^b
  old : B.raw.cap≤2^b
  units : B.next.placement.cap<2^t
  nearOld : B.next.placement.degree+1<2^t
  codeRoom : DescentResetParentCodec.capCount H₀ r Y L (A).cap slots pcCap≤2^t
  sorted : SourceSorted W input.order
  age : 0 < i

private theorem heldSource {e : Expr} {a : ℕ} {v : Fin H→Fin grp→Cell a} {at_ : ℕ} {m o : Memory Wd}
    (fit : e.Fits Wd at_) (before : ∀i,i<at_ → o i=m i) (orig : Source e v M m) : Source e v M o :=
  fun i=>(ProtocolRAM.eval_below e _ m o fit before).trans (orig i)

private theorem heldStatic {B₀ : DescentPackedZip.Tables} {d a c at_ : ℕ} {f : Cell d→Cell a→Cell c}
    {m o : Memory Wd} (fit : WordRoom B₀ d a M Wd at_) (before : ∀i,i<at_ → o i=m i)
    (orig : Static B₀ f M m) : Static B₀ f M o := by
  constructor
  · intro j
    have h : j.val<B₀.shift.size:=by simp [Bank.size,fit.shiftBits]
    exact (before _ ((Nat.add_lt_add_left h _).trans_le fit.shift.2.2)).trans (orig.1 j)
  · intro j
    have h : j.val<B₀.apply.size:=by simp [Bank.size,fit.applyBits]
    exact (before _ ((Nat.add_lt_add_left h _).trans_le fit.apply.2.2)).trans (orig.2 j)

private theorem laterRoom {B₀ : DescentPackedZip.Tables} {d a n u : ℕ} (room : WordRoom B₀ d a M Wd n) (later : n≤u) :
    WordRoom B₀ d a M Wd u :=
  ⟨⟨room.shift.1,room.shift.2.1,room.shift.2.2.trans later⟩,⟨room.apply.1,room.apply.2.1,room.apply.2.2.trans later⟩,
   room.shiftBits,room.applyBits⟩

abbrev Earlier {w : ℕ} (o m : Memory w) (n : ℕ):=∀a,a<n → o a=m a

private def rankChart (m o : Memory Wd) (out : ℕ)
    (s : RankSources B (M:=M) (b:=b) (t:=t) rack ports header original m) (p : (Λ).Previous Wd)
    (inc : base≤out) (frame : Earlier o m base)
    (search : ∀j,Static ((Λ).search j) (DescentResetSourceSeekRAM.select (b:=b) (t:=t) (Δ:=4) (slotGate B) j) M o ∧
      WordRoom ((Λ).search j) (b*7) t M Wd out)
    (lookup : ∀i,Static ((Λ).lookup i)
      (DescentResetSourcePullRAM.take (b:=DescentResetSourceSeekRAM.keyBits 4 K) (a:=b) (Δ:=4) («K» := K) i) M o ∧
      WordRoom ((Λ).lookup i) (DescentResetSourceSeekRAM.keyBits 4 K) b M Wd out) :
    PullChart B rack b t b 4 M out o where
  name:=s.name
  ordered:=s.ordered
  anchor:=s.anchor
  complete:=s.complete
  peer:=s.peer
  roster:=s.roster
  capacity:=s.capacity
  ports:=ports
  actual:=by
    have keep (b₀ : Bank) (fit : b₀.Fits Wd base) {v : ℕ} (hi : v<b₀.size) :
        o (b₀.base+v)=m (b₀.base+v):=frame _ ((Nat.add_lt_add_left hi _).trans_le fit.2.2)
    refine ⟨fun z j=>?_,fun v j=>?_,fun v=>?_,fun z=>?_⟩
    · exact (keep _ (p.ids j) ((row H grp M z).isLt.trans_le (p.idsRoom j))).trans (s.mounted.ids z j)
    · have hi : v.val*4+j.val<H*4:=by
        simpa only [finProdFinEquiv_apply_val,Nat.mul_comm 4,Nat.add_comm] using (finProdFinEquiv (v,j)).isLt
      exact (keep _ p.roster (hi.trans_le p.rosterRoom)).trans (s.mounted.roster v j)
    · exact (keep _ p.offsets (v.isLt.trans_le p.offRoom)).trans (s.mounted.offsets v)
    · exact (keep _ p.chunks ((row H grp M z).isLt.trans_le p.chunkRoom)).trans (s.mounted.chunks z)
  original:=original
  header:=header
  origFit:=fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ inc (p.original x j)
  headFit:=fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ inc (p.header x j)
  originalRead:=fun x j=>heldSource (p.original x j) frame (s.words x j)
  headerRead:=fun x j=>heldSource (p.header x j) frame (s.measured x j)
  headerRoom:=meta_room B rack s.near s.small
  wordRoom:=s.codeRoom
  search:=(Λ).search
  searchStatic:=fun j=>(search j).1
  searchRoom:=fun j=>(search j).2
  lookup:=(Λ).lookup
  lookupStatic:=fun i=>(lookup i).1
  lookupRoom:=fun i=>(lookup i).2

private theorem ticket_value (x : Fin X) (j : Fin K) :
    (fun v g=>(actualTicket B rack x j v g:Cell b))=actualLocal B rack (sourceTicketCell (a:=b) B) x j := by
  funext v g
  cases hv : rack v with
  | none => simp only [actualLocal,actualTicket,hv,Option.elim_none,Nat.cast_zero]
  | some h =>
    simp only [actualLocal,actualTicket,hv,Option.elim_some]
    cases he : localOrigin B ((g,h),x) j <;> rfl

set_option maxHeartbeats 3200000 in
theorem ranked_fields_tickets (m : Memory Wd) (s : RankSources B (M:=M) (b:=b) (t:=t) rack ports header original m)
    (p : (Λ).Previous Wd) (room : (Λ).endAddress<2^Wd) :
    let o:=(Λ).memory m
    (∀x j,Reads ((Λ).oldBank x j) (fun v g=>
      ((∑n,feeAt (wordBefore B) (original_fees (b:=t) B rack x v g) j n : ℕ) : Cell b)) M o) ∧
    ((Λ).program Wd).Exec m o (Λ).time ∧
    (∀x j,(header x j).Fits Wd (Λ).endAddress ∧ Source (header x j) (fun v g=>DescentResetFieldAssembler.raw b (actualMeta B rack x j v g)) M o) ∧
    (∀x a j,((Λ).finalRank x a j).Fits Wd (Λ).endAddress ∧ Source ((Λ).finalRank x a j)
      (actualOffset (b:=b) B rack x a j) M o) ∧
    (∀z,z<base ∨ (Λ).endAddress≤z → o z=m z) ∧ CheapCode ((Λ).program Wd) := by
  intro o
  obtain ⟨a,c,f,tops⟩:=(Λ).ordered
  have endFit:=tops.trans_lt room
  have seekFit:=f.trans_lt endFit
  have preFit:=c.trans_lt seekFit
  let fee:=original_fees (b:=t) B rack
  let paid (x j v g) : Cell b:=⟨∑n,feeAt (wordBefore B) (fee x v g) j n,
    (sum_fee_le (b:=t) B rack x v g j).trans_lt s.small⟩
  have start:=DescentResetSourceTicketPair.any base b t M Wd m preFit
  have fits:=DescentResetSourceTicketPair.fits (a:=b) (b:=t) (M:=M) header original p.header p.original preFit
  have rows:=DescentResetSourceTicketPair.sources (a:=b) (b:=t) (M:=M) (base:=base) (w:=Wd) (H:=H) (G:=grp) header original
    (fun x v g j=>actualMeta B rack x j v g) (fun x v g j=>(actualParentNumber B rack x j v g:Cell t)) m
    p.header p.original preFit (fun x v g j=>meta_room B rack s.near s.small x j v g) s.measured s.words
  have positive : 1<2^t:=by have:=s.nearOld;omega
  have old:=DescentResetSourceTicketBank.run (paid:=b) (w:=Wd) (root:=(Λ).ticketBase) (b:=t) (M:=M) (H:=H) (G:=grp) (wordBefore B) (Λ).questions (Λ).entries fee ((Λ).paired m) fits.1 fits.2
    positive rows (fun x j v g=>(sum_fee_le (b:=t) B rack x v g j).trans_lt s.small) seekFit
  have menus:=DescentResetSourceSeekRAM.mountBooks (Δ:=4) (b:=b) (t:=t) (a:=b) (M:=M) (Λ).seekBase (slotGate B) ((Λ).counted m) endFit
  have early:=((a.trans c).trans f)
  have before : Earlier ((Λ).searched m) m base:=fun z hz=>
    (menus.2.2.2.2 z (.inl ((hz.trans_le a).trans_le c))).trans
      ((old.2.2.2 z (.inl (hz.trans_le a))).trans (start.2.2.2 z (.inl hz)))
  let chart:=rankChart B rack base ports header original m ((Λ).searched m) (Λ).rankBase s p early before menus.2.2.1 menus.2.2.2.1
  have ticketFit (x : Fin X) (j : Fin K) := DescentResetSourceTicketBank.column_fits (w:=Wd) (root:=(Λ).ticketBase) (b:=t) (M:=M) (H:=H) (G:=grp) seekFit x j
  have sourceOld (x j) : Reads ((Λ).oldBank x j) (paid x j) M ((Λ).searched m) :=by
    intro r'
    have lower:=(Nat.add_lt_add_left ((row H grp M r').isLt.trans_le (DescentDyadicSpan.span_ge _)) ((Λ).oldBank x j).base).trans_le (ticketFit x j).2.2
    exact (menus.2.2.2.2 _ (.inl lower)).trans (old.2.2.1 x j r')
  have lookup (x : Fin X) (j : Fin K):=actual_pull_ticket B rack chart x j ((Λ).oldBank x) (paid x)
    (fun l=>p.access _ _ early ⟨(ticketFit x l).1,(ticketFit x l).2.1,(ticketFit x l).2.2.trans f⟩ (DescentDyadicSpan.span_ge _))
    (sourceOld x) (fun h g e=>by
      apply Fin.ext
      rw [Fin.val_cast_of_lt ((sourceTicket B e.val e.property.1).isLt.trans_le s.old)]
      exact ticket_issued B rack s.age s.sorted s.name s.complete s.units s.nearOld s.codeRoom x h g e)
  have rawTicket (x j):Source ((Λ).ticket x j) (fun v g=>(actualTicket B rack x j v g:Cell b)) M ((Λ).searched m):=by
    rw [ticket_value B rack (b:=b) x j]
    exact (lookup x j).2
  have ranks:=local_ranks B rack (Λ).rankBase header (Λ).ticket ((Λ).searched m)
    (fun x j=>ProtocolRAMGeneratedWrite.fits_mono _ early (p.header x j)) (fun x j=>(lookup x j).1)
    (fun x j=>heldSource (p.header x j) before (s.measured x j)) rawTicket s.near s.small s.old room
  have archive : Earlier o ((Λ).searched m) (Λ).rankBase:=fun z h=>ranks.2.2.1 z (.inl h)
  have kept:Earlier o m base:=fun z h=>(archive z (h.trans_le early)).trans (before z h)
  have newSearch (j):=menus.2.2.1 j
  have newLookup (i):=menus.2.2.2.1 i
  let after_:=rankChart B rack base ports header original m o (Λ).endAddress s p (early.trans tops) kept
    (fun j=>⟨heldStatic (newSearch j).2 archive (newSearch j).1,laterRoom (newSearch j).2 tops⟩)
    (fun i=>⟨heldStatic (newLookup i).2 archive (newLookup i).1,laterRoom (newLookup i).2 tops⟩)
  have localFit (x : Fin X) (a : Fin 3) (j : Fin K):=DescentResetSignedScan.Ranks.output_fits (DescentResetLocalRankRun.rankBase (Λ).rankBase b M) x a j room
  have receiver (x a j) (neq : a≠(2:Fin 3)) : Reads ((Λ).localBank x a j) (actualOffset (b:=b) B rack x a j) M o := by
    have values : (fun v g => (localOffset B rack x a j v g : Cell b)) = actualOffset (b:=b) B rack x a j :=
      funext fun v => funext fun g => offset_at_receiver B rack x a j v g neq
    rw [← values]
    exact ranks.2.1 x a j
  have result:=(Λ).any m p room
  have stored (x j) : Reads ((Λ).oldBank x j) (paid x j) M o :=by
    intro rr
    have inc:=(Nat.add_lt_add_left ((row H grp M rr).isLt.trans_le (DescentDyadicSpan.span_ge _)) ((Λ).oldBank x j).base).trans_le (ticketFit x j).2.2
    exact (archive _ (inc.trans_le f)).trans (sourceOld x j rr)
  refine ⟨?_,result.1,fun x j=>⟨after_.headFit x j,after_.headerRead x j⟩,?_,result.2.1,@result.2.2⟩
  · intro x j
    have same : (fun v g=>((∑n,feeAt (wordBefore B) (original_fees (b:=t) B rack x v g) j n : ℕ):Cell b))=paid x j := by
      funext v g
      apply Fin.ext
      exact Fin.val_cast_of_lt ((sum_fee_le (b:=t) B rack x v g j).trans_lt s.small)
    rw [same]
    exact stored x j
  intro x axis j
  by_cases ss:axis=2
  · subst axis
    exact actual_pull_atSource B rack after_ x j ((Λ).localBank x 0)
      (fun l=>p.access _ _ (early.trans tops) (localFit x 0 l) (DescentDyadicSpan.span_ge _)) (fun z=>receiver x 0 z (by decide))
  · have fit:=localFit x axis j
    rw [Layout.finalRank, ite_eq_right ss]
    exact ⟨⟨fit,trivial⟩,source_column (M:=M) ((Λ).localBank x axis j) (Λ).endAddress fit o _
      (DescentDyadicSpan.span_ge _) (receiver x axis j ss)⟩

theorem ranked_fields (m : Memory Wd) (s : RankSources B (M:=M) (b:=b) (t:=t) rack ports header original m)
    (p : (Λ).Previous Wd) (room : (Λ).endAddress<2^Wd) :
    let o:=(Λ).memory m
    ((Λ).program Wd).Exec m o (Λ).time ∧
    (∀x j,(header x j).Fits Wd (Λ).endAddress ∧ Source (header x j) (fun v g=>DescentResetFieldAssembler.raw b (actualMeta B rack x j v g)) M o) ∧
    (∀x a j,((Λ).finalRank x a j).Fits Wd (Λ).endAddress ∧ Source ((Λ).finalRank x a j)
      (actualOffset (b:=b) B rack x a j) M o) ∧
    (∀z,z<base ∨ (Λ).endAddress≤z → o z=m z) ∧ CheapCode ((Λ).program Wd) := (ranked_fields_tickets B rack base ports header original m s p room).2

theorem ranked_ticket_bank (m : Memory Wd) (s : RankSources B (M:=M) (b:=b) (t:=t) rack ports header original m)
    (p : (Λ).Previous Wd) (room : (Λ).endAddress<2^Wd) (x j) :
    Reads ((Λ).oldBank x j) (fun v g=>
      ((∑n,feeAt (wordBefore B) (original_fees (b:=t) B rack x v g) j n : ℕ) : Cell b)) M ((Λ).memory m) :=
  (ranked_fields_tickets B rack base ports header original m s p room).1 x j

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
