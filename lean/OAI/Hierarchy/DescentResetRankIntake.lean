import OAI.Hierarchy.DescentResetSignedMemory
import OAI.Hierarchy.DescentResetCandidatePair
import OAI.Hierarchy.DescentResetPeerUnionRAM

namespace OAI
/-! # Rank receipt of the paired candidate sheets at a reached reset -/
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
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "U" => Fintype.card input.V
local notation "H₀" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H₀*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "okCode" => fun t=>((T).codeLegal t).2
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Short" => DescentResetCompactParent.Word H₀ r Y L (A).cap slots pcCap

open DescentPackedColony DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentResetFieldAssembler
local notation "K" => totalLocal B
local notation "X" => 2^k
local notation "grp" => S.groupCount (i+1)
local notation "board_" => blocks B
local notation "entry" => (Z).rawHostRank T vertex
open DescentResetRankedWindows DescentResetSourceTicketCompare DescentResetFieldAssembler
open DescentResetCandidatePair DescentResetFieldAssembler DescentResetLocalRoster
variable {H M Wd p : ℕ} (name : B.next.V↪Fin H)
local notation "rack_" => rackOf B name
local notation "ss" => stemsCount B
local notation "cc" => contactCount B
local notation "pp" => privateCount B
local notation "idx" => CandidateSheet.index ss cc pp
local notation "b" => fieldBits (2^g*input.placement.cap)
local notation "t" => originalBits D k n height input.placement.cap (programCount ctl.board height) g

/-- A pair of disjoint actual sheet scans preserves the earlier four-port sort. -/
private theorem ports_after {Δ P₀ groups : ℕ} {m done : Memory Wd} {ports : Ports Δ} {prior : Bank}
    {views : Fin H→Fin Δ→Option (Fin H)} (access : Accessible ports prior H groups M Wd P₀)
    (mounted : Mounted ports views m groups M) (low : ∀n,n<P₀→done n=m n) :
    Mounted ports views done groups M := by
  have keep (bank : Bank) (fit : bank.Fits Wd P₀) {n : ℕ} (hn : n<bank.size) :
      done (bank.base+n)=m (bank.base+n):=low _ ((Nat.add_lt_add_left hn _).trans_le fit.2.2)
  refine ⟨fun z j=>?_,fun u j=>?_,fun u=>?_,fun z=>?_⟩
  · exact (keep _ (access.ids j) ((row H groups M z).isLt.trans_le (access.idsRoom j))).trans (mounted.ids z j)
  · have size : u.val*Δ+j.val<H*Δ:=by
      simpa only [finProdFinEquiv_apply_val,Nat.mul_comm Δ,Nat.add_comm] using (finProdFinEquiv (u,j)).isLt
    exact (keep _ access.roster (size.trans_le access.rosterRoom)).trans (mounted.roster u j)
  · exact (keep _ access.offsets (u.isLt.trans_le access.offRoom)).trans (mounted.offsets u)
  · exact (keep _ access.chunks ((row H groups M z).isLt.trans_le access.chunkRoom)).trans (mounted.chunks z)

def sheetHeader (start bits : ℕ) (x : Fin X) (j : Fin K) : Expr :=
  .lookup (CandidateSheet.output (s:=ss) (c:=cc) (p:=pp) start bits x j) .row
def sheetOriginal (start bits : ℕ) (x : Fin X) (j : Fin K) : Expr :=
  sheetHeader B (originalBase start X K bits) bits x j

/-- Consume the roster freshly copied to compact actor order after both sheets were written. -/
def rank_compact_reads {b₁ : ℕ} (width : b≤b₁) (start bits : ℕ) (ports : Ports 4)
    (headers keys : Inputs X ss cc pp) (m after : Memory Wd) (peers : Fin H→Fin 4→Option (Fin H))
    (names : ∀v u : B.next.V,name v<name u↔entry v<entry u) (record : B.Recorded p)
    (neighbors : ∀v,DescentSortedRoster.present peers (name v)=
      (insert v (B.reset.emittedNear B.terminals v)).map name)
    (mounted : Mounted ports (DescentSortedRoster.indexed peers) after grp M)
    (preserved : ∀addr,addr<DescentResetCandidatePair.endAddress start X K bits→
      after addr=DescentResetCandidatePair.memory start bits H grp M headers keys m addr)
    (hf : ∀x j,(headers x j).Fits Wd start) (wf : ∀x j,(keys x j).Fits Wd start)
    (headerRead : ∀x j,Source (headers x j) (fun h g=>DescentResetFieldAssembler.raw b₁ (actualMeta B rack_ x (idx j) h g)) M m)
    (keyRead : ∀x j,Source (keys x j) (fun h g=>(actualParentNumber B rack_ x (idx j) h g:Cell t)) M m)
    (rows : H*chunks grp M≤2^bits) (space : DescentResetCandidatePair.endAddress start X K bits<2^Wd)
    (sorted : SourceSorted W input.order) (elapsed : 0 < i) :
    RankSources B («b» :=b₁) («t» :=t) (M:=M) rack_ ports (sheetHeader B start bits) (sheetOriginal B start bits)
      after := by
  let done:=DescentResetCandidatePair.memory start bits H grp M headers keys m
  have ready:=DescentResetCandidatePair.read_pair start bits headers keys
    (fun x j h g=>DescentResetFieldAssembler.raw b₁ (actualMeta B rack_ x j h g)) (fun x j h g=>(actualParentNumber B rack_ x j h g:Cell t))
    m hf wf headerRead keyRead rows space
  obtain ⟨bc,bn,bo,tc,tn,tw⟩:=key_rooms B
  have widen : 2^b≤2^b₁:=Nat.pow_le_pow_right (by decide) width
  refine ⟨name,names,rack_named B name,rack_present B name,peers,?_,?_,
    mounted,?_,?_,bc.trans_le widen,bn.trans_le widen,bo.trans widen,tc,tn,tw,sorted,elapsed⟩
  · intro v;rw [rendered_near B record];exact neighbors v
  · simpa only [B.next.branch] using (Nat.le_refl 4)
  · intro x j
    have mid : originalBase start X K bits≤DescentResetCandidatePair.endAddress start X K bits:=Nat.le_add_right ..
    have fit:=DescentResetCandidatePair.bank_room (s:=ss) (c:=cc) (p:=pp) start bits x j (mid.trans_lt space)
    have allFit:=(show (sheetHeader B start bits x j).Fits Wd (DescentResetCandidatePair.endAddress start X K bits)
      from ⟨⟨fit.1,fit.2.1,fit.2.2.trans mid⟩,trivial⟩)
    have read:=source_column _ _ fit done _ rows (ready.1 x j)
    exact fun p=>(eval_below _ _ done after allFit preserved).trans (read p)
  · intro x j
    have fit:=DescentResetCandidatePair.bank_room (s:=ss) (c:=cc) (p:=pp) (originalBase start X K bits) bits x j space
    have read:=source_column _ _ fit done _ rows (ready.2 x j)
    have exprFit : (sheetOriginal B start bits x j).Fits Wd (DescentResetCandidatePair.endAddress start X K bits) :=
      ⟨fit,trivial⟩
    exact fun p=>(eval_below _ _ done after exprFit preserved).trans (read p)

/-- Every physical candidate, including empty and zero-traffic slots, is read from
the actual two attained sheets. The previously sorted neighbor table remains live. -/
def rank_input_reads (start bits : ℕ) (ports : Ports 4) (prior : Bank)
    (headers keys : Inputs X ss cc pp) (m : Memory Wd) (peers : Fin H→Fin 3→Option (Fin H))
    (names : ∀v u : B.next.V,name v<name u↔entry v<entry u) (record : B.Recorded p)
    (neighbors : ∀v,DescentSortedRoster.present (DescentResetPeerUnionRAM.selfPeers peers) (name v)=
      (insert v (B.reset.emittedNear B.terminals v)).map name)
    (accessible : Accessible ports prior H grp M Wd start)
    (mounted : Mounted ports (DescentSortedRoster.indexed (DescentResetPeerUnionRAM.selfPeers peers)) m grp M)
    (hf : ∀x j,(headers x j).Fits Wd start) (wf : ∀x j,(keys x j).Fits Wd start)
    (headerRead : ∀x j,Source (headers x j) (fun h g=>DescentResetFieldAssembler.raw b (actualMeta B rack_ x (idx j) h g)) M m)
    (keyRead : ∀x j,Source (keys x j) (fun h g=>(actualParentNumber B rack_ x (idx j) h g:Cell t)) M m)
    (rows : H*chunks grp M≤2^bits) (space : DescentResetCandidatePair.endAddress start X K bits<2^Wd)
    (sorted : SourceSorted W input.order) (elapsed : 0 < i) :
    RankSources B («b» :=b) («t» :=t) (M:=M) rack_ ports (sheetHeader B start bits) (sheetOriginal B start bits)
      (DescentResetCandidatePair.memory start bits H grp M headers keys m) := by
  have frame:=(DescentResetCandidatePair.any start bits H grp M headers keys m hf wf rows space).2.1
  exact rank_compact_reads B name (Nat.le_refl _) start bits ports headers keys m _ (DescentResetPeerUnionRAM.selfPeers peers) names record neighbors
    (ports_after accessible mounted (fun addr h=>frame _ (.inl h))) (fun _ _=>rfl)
    hf wf headerRead keyRead rows space sorted elapsed

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
