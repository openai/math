import OAI.ThreeFlat.Diagonal.HistoryMotifTariffGather
import OAI.ThreeFlat.RAM.HistorySelectedFrame

namespace OAI
/-! # Native refresh execution for the physical motif tariff -/

set_option quotPrecheck false

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression Computability.VPVNP.MotifSelector LinearAlgebra.SpectralBooks
open RAM RAM.HistoryStageBody.Physical RAM.HistoryPartyBatchExec RAM.HistoryRefreshEmitter
open PhysicalStage CompressorPacking Native RefreshDemandRows RefreshStageNav RefreshTies
open HistogramTileNetwork MotifOuterTerms MotifOrderedCells MotifSelectorChecks
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {u K : ℕ} {cur:Word (16*u^10)}
    (q:RefreshReceipt F K cur) (y:(q.move.next q.term).Site)
local notation "W" => 16*u^10
local notation "s" => q.s
local notation "m" => 2^q.s
local notation "z" => q.chosenBlock y
local notation "j" => (q.kernelSite y).1.2
local notation "G" => refreshBinaryGraph q.input
local notation "w" => refreshBinaryInput q.input
local notation "tag₀" => (tagOrdinal q.s).symm
local notation "i" => q.tile.winner G tag₀ w z
local notation "D" => RefreshMotif.denseGraph m
local notation "S" => DoublePorts.connectedSupply q.mult q.hh q.rowSum q.sym q.conn
local notation "demand" => RefreshParty.denseOrder j
local notation "supply" => RefreshParty.sparseOrder q.mult q.sym q.rowSum j
local notation "entry" => refreshBinaryEntry q.tile q.input z
local notation "row" => issuedParty q.tile q.hh q.rowSum q.sym q.conn i j
local notation "r" => refreshBinaryCopies q.tile q.input z
local notation "base₀" => q.tile.base i
local notation "letters" => Fintype.card (entry).Alphabet
local notation "idT" => Fintype.equivFin (entry).Alphabet
local notation "hist" => refreshBinaryBranchOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch

/-- The arithmetic header at the literal selected refresh party. -/
def issuedHeader : Header ((D).Port j) (entry).Alphabet (fun f=>base₀ f.1.1) (entry).bits (4*m) :=
  ⟨demand,(entry).encode⟩

def issuedTile := by
  letI := (entry).hasLetter
  exact HistogramTileNetwork.tile D S j base₀ (q.issuedHeader y) supply (entry).output
    (fun a b=>(entry).output_le_cap a (supply b).1.1) (entry).entry

def issuedGood := headerGood S j supply (entry).encode

def issuedLetter := by
  letI := (entry).hasLetter
  exact headerLetter S j supply idT (entry).encode

def issuedQuota : Histogram (Fin letters) r := numberHistogram («r»:=r) idT (hist z)

variable (B:Block F) {height start:ℕ} {mem:Memory (16*u^10)}
    (supported:B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (mounted:Mounted B height (16*u^10) start mem)

include supported mounted in
theorem issued_arity : (q.issuedHeader y).arity+(2*q.h*(entry).bitCap+2*q.h*(entry).bitCap)≤arity B ∧
    2*q.h*(entry).bits+letters≤arity B := by
  have placed:=issued_party_rom B mounted q.tile supported q.hh q.rowSum q.sym q.conn i j
  exact arity_fits B (by simp [grids]) placed.1

/-- The fixed ROM kind is judgmentally the specialized arithmetic checker and
payload once the true table and the sparse/dense port enumerations are fixed. -/
theorem issued_kind
    {tp : (q.issuedHeader y).arity+(2*q.h*(entry).bitCap+2*q.h*(entry).bitCap)≤arity B}
    {sp : 2*q.h*(entry).bits+letters≤arity B} :
    (row).kind (arity B)=HistoryPartySpecialization.kind (ar:=arity B) (q.issuedTile y) (q.issuedGood y)
        (q.issuedLetter y) tp sp := by
  dsimp only [issuedParty, issuedTile, issuedHeader, issuedGood, issuedLetter,
    refreshBinaryEntry, RefreshMotif.Table.entry]
  with_unfolding_all
    exact Party.kind_ofTile (ar:=arity B) D S j base₀ (q.tile.block i) demand supply
      Fin.val Fin.val ⟨tp,sp⟩

local notation "indexedEntry" =>
  refreshBinaryEntry q.tile q.input ((refreshBlockOrder q.input).symm (q.chosenIndex y))
local notation "arc" => archive B start height K
local notation "A" => layout u arc (refreshFamily B start height)
local notation "X" ck => (⟨(rawArm A (j).val).party,ck,(row).kind (arity B),mem⟩:HistoryPartyBatchExec.Build W)

/-- Reindex the actual admitted quota read in the checks boot to precisely the
finite index used by the native selected party's arithmetic selector. -/
theorem issued_quota (ck:Bool)
    (got:∀ a:Fin (Fintype.card (indexedEntry).Alphabet),
      numeric (X ck).bootImage (numeric (X ck).bootImage ((X ck).regs.incident+1)+a.val)=
        ((hist ((refreshBlockOrder q.input).symm (q.chosenIndex y))).val
          ((Fintype.equivFin (indexedEntry).Alphabet).symm a)).val) :
    ∀ a:Fin letters,numeric (X ck).bootImage (numeric (X ck).bootImage ((X ck).regs.incident+1)+a.val)=
      ((q.issuedQuota y).val a).val := by
  let reads (b : q.input.Base × BitWord q.rem) : Prop :=
    ∀ a : Fin (Fintype.card (refreshBinaryEntry q.tile q.input b).Alphabet),
      numeric (X ck).bootImage (numeric (X ck).bootImage ((X ck).regs.incident+1)+a.val) =
        ((hist b).val ((Fintype.equivFin (refreshBinaryEntry q.tile q.input b).Alphabet).symm a)).val
  have fromIndex : reads ((refreshBlockOrder q.input).symm (q.chosenIndex y)) := got
  have inv : (refreshBlockOrder q.input).symm (q.chosenIndex y)=z :=
    (refreshBlockOrder q.input).symm_apply_apply z
  exact (congrArg reads inv).mp fromIndex

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression Computability.VPVNP.MotifSelector RAM RAM.HistoryStageBody.Physical
open RAM.HistoryPartyBatchExec RAM.HistoryRefreshEmitter RAM.HistoryPartySpecialization RAM.NavigationNodeRows
open PhysicalStage NavigationDirectory CompressorPacking Native RefreshDemandRows RefreshStageNav RefreshTies
open HistoryContraction HistoryContraction.Tree MotifOuterTerms MotifOrderedCells MotifSelectorChecks
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F:Type} [Field F] [Fintype F] {u K heads height rom:ℕ} {cur ctr:Word (16*u^10)}
    (q:RefreshReceipt F K cur) (B:Block F) (y:(q.move.next q.term).Site) (t:Fin (height+1))
    (b:Banks) {final mem:Memory (16*u^10)}
    (img:PartyImage (heads:=heads) q B height rom b y final mem)
    (supported:B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "node" => q.step.sites.id y
local notation "fam" => refreshFamily B rom height
local notation "arc" => archive B rom height K
local notation "A" => layout u arc fam
local notation "z" => q.chosenBlock y
local notation "role" => (q.kernelSite y).1.2
local notation "i₀" => q.tile.winner (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input) z
local notation "entry" => refreshBinaryEntry q.tile q.input z
local notation "P₀" => issuedParty q.tile q.hh q.rowSum q.sym q.conn i₀ role
local notation "r" => refreshBinaryCopies q.tile q.input z
local notation "J" => (rawArm A (role).val).party
local notation "fit" => q.issued_arity y B supported img.resident
local notation "tile" => q.issuedTile y
local notation "gd" => q.issuedGood y
local notation "letter" => q.issuedLetter y
local notation "hist" => q.issuedQuota y
local notation "lib" => HistoryStaticArchive.all F (arity B)
local notation "e" => 2*q.h
local notation "d" => (entry).bitCap
local notation "s" => Fintype.card (entry).Alphabet
local notation "k" => (entry).bits
local notation "h₀" => (q.issuedHeader y).arity
local notation "SC" => MotifNativeCompactors.partialInput F r t.val
local notation "PC" => MotifNativeCompactors.partialInput F (r*d) t.val
local notation "L" => admission gd letter SC hist
local notation "R" => tiled tile PC
local notation "X" => electedBatch tile gd letter (fit).1 (fit).2 J mem true
local notation "componentsC" => components gd letter SC hist
local notation "readC" => Reads (X).regs (numeric (X).bootImage) lib r t
local notation "dim" a:arg => checks_fields tile gd letter (fit).1 (fit).2 (X).regs (numeric (X).bootImage) t a
local notation "idx" a:arg => Fin.cast (congrArg₂ Nat.add (dim a).1 (dim a).2.1)
open private liveCheckJobs from OAI.ThreeFlat.RAM.HistoryRefreshElectedJobs
local notation "Y" a:arg => electedBatch tile gd letter (fit).1 (fit).2 J
  ((X).published (liveCheckJobs tile gd letter (fit).1 (fit).2 J mem t hist a)) false

include img supported in
/-- The physical grid stores compaction pages through the native word width. -/
theorem elected_height (price : ℕ) (copies : r≤price)
    (margin : gridPageRate (arity B) (refreshGrid B)*((price+1)*(W+1)^3)≤V) :
    HistogramTileNetwork.siteHeight r d≤W := by
  have placed:=issued_party_rom B img.resident q.tile supported q.hh q.rowSum q.sym q.conn i₀ role
  exact page_height_at_age (arity B) u price r (refreshGrid B) P₀ placed.1 copies margin

include img supported in
set_option maxRecDepth 17000 in
set_option maxHeartbeats 1800000 in
/-- All elected arrays at this recorded site fit by one inequality in the
actual chronological copy charge and the fixed refresh catalogue. -/
theorem elected_pages (price : ℕ) (copies : r≤price) (level : t.val=HistogramTileNetwork.siteHeight r d)
    (margin : gridPageRate (arity B) (refreshGrid B)*((price+1)*(W+1)^3)≤V) :
    PartyPageCaps V (arity B) P₀ r t.val ((L).rows+(R).rows) ((L).bits+(R).bits) := by
  classical
  let original:=refreshBinaryBranchOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch
  have placed:=issued_party_rom B img.resident q.tile supported q.hh q.rowSum q.sym q.conn i₀ role
  have pages:=party_page_caps_at_age (RefreshMotif.denseGraph (2^q.s))
    (DoublePorts.connectedSupply q.mult q.hh q.rowSum q.sym q.conn) role (q.tile.base i₀) entry
    (RefreshParty.denseOrder role) (RefreshParty.sparseOrder q.mult q.sym q.rowSum role) Fin.val Fin.val
    (original z) (arity B) u price (refreshGrid B) placed.1 copies margin
  rw [level]
  dsimp only [issuedParty, issuedHeader, issuedTile, issuedGood, issuedLetter,
    issuedQuota, original, refreshBinaryCopies, refreshBinaryEntry, RefreshMotif.Table.entry,
    refreshBinaryGraph, refreshBinaryInput] at pages ⊢
  with_unfolding_all exact pages

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4500000 in
/-- The actual refresh boot at the selected party, its committed checks tape, the
payload boot from that reached memory, and their pair room with the chosen tree's
types. All six maps of local rows/pins are computed by these actual instructions. -/
theorem recorded_elected_room
    (saved:SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds:RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (baseNodes:b.nodes=TickWorkspace.base u 44) (pairs:TickWorkspace.base u 19≤b.charges)
    (age:16≤u) (nodeFit:node<V^2) (cap:((fam).motifs+2)*((fam).parties+2)*8*32≤V)
    (mask:2^(fam).parties<2^W) (gradeFit:q.tile.last+1≤2^W) (headsHigh:TickWorkspace.base u 19≤heads)
    (romHigh:TickWorkspace.base u 19≤rom) (romFit:rom+libraryWords B height<2^W)
    (level:t.val=HistogramTileNetwork.siteHeight r d) (width:2^t.val≤V)
    (work:StableCompactNativeBudget.budget t.val≤V)
    (kindSmall:∀ a:Fin 7,((P₀).kind (arity B)).words a≤V)
    (rows:8*((L).rows+(R).rows)≤V)
    (maps:(r*(e*k+s)+s*(r+(r+r)))+(r*(h₀+(e*d+e*d))+e*(r*d+(r*d+r*d)))≤V)
    (countRoom:23*(r+max s e)≤V) (hidden:(L).bits+(R).bits≤V)
    (tags:Fintype.card ((Fin 3→Bool)→F)≤2^W) :
    ∃ c:readC,∃ p:Reads (Y c).regs (numeric (Y c).bootImage) lib r t,
      ElectedRoom tile gd letter (fit).1 (fit).2 J node mem t hist c p ∧
      PartyImage (heads:=heads) q B height rom b y final
        (electedOutput tile gd letter (fit).1 (fit).2 J node mem t hist c p) := by
  classical
  have exactKind:=q.issued_kind y B (tp:=(fit).1) (sp:=(fit).2)
  have small:r≤V:=by omega
  have alph:((P₀).kind (arity B)).letters≤K:=by
    let lettersAt (loc : q.input.Base × BitWord q.rem) :=
      Fintype.card (refreshBinaryEntry q.tile q.input loc).Alphabet
    have h : lettersAt ((refreshBlockOrder q.input).symm (q.chosenIndex y)) ≤ K :=
      q.fit.1 (q.chosenIndex y)
    have inv:(refreshBlockOrder q.input).symm (q.chosenIndex y)=z:=(refreshBlockOrder q.input).symm_apply_apply z
    exact (congrArg lettersAt inv).symm.le.trans h
  have romRow:=issued_party_rom B img.resident q.tile supported q.hh q.rowSum q.sym q.conn i₀ role
  let elected:Fin (fam).parties:=Fin.cast romRow.2.1.symm role
  have motifs:0<(fam).motifs:=by change 0<1;decide
  have win:PartyWindow u J:=PartyWindow.of_layout arc fam 0 (role).val age motifs (by rw [romRow.2.1];exact (role).isLt) cap
  have nodeHigh:TickWorkspace.base u 19≤b.nodes:=by rw [baseNodes];have:=TickWorkspace.apart (u:=u) (by decide:19<44);omega
  obtain ⟨seed₀,c,letters₀⟩:=q.active_seed B supported img.resident y true t saved bounds img.archive b baseNodes img.row img.cursor
    age nodeFit cap mask gradeFit headsHigh romHigh romFit level width work small kindSmall alph
  have leftSeed:ElectedSeed u X:=by simpa only [electedBatch,←exactKind] using seed₀
  have c':readC:=c
  have quota:=q.issued_quota y B (height:=height) (start:=rom) true letters₀
  let dims:=dim c'
  let nets:=fun i=>(componentsC i).net
  let wires:=fun i=>(componentsC i).wire
  have sizes:=checks_dimensions tile gd letter (fit).1 (fit).2 (X).regs (numeric (X).bootImage) t c' hist
  have sizeC:HistoryPartyTapeRun.batchRows (X).table=(L).rows:=congrArg RAM.HistoryBoundedJoin.Info.factors
    (batch_info X _ nets wires dims.1 dims.2.1 sizes dims.2.2.1 dims.2.2.2.1)
  have rc : (X).table.r = r := dims.1
  have sc : (X).table.s = s := dims.2.1
  have pC:HistoryPartyTapeRun.batchPins (X).table=r*(e*k+s)+s*(r+(r+r)):=by
    have left : (X).table.left.arity = e*k+s :=
      congrArg HistoryContraction.Tree.BatchRows.Size.arity dims.2.2.2.2.1
    have right : (X).table.right.arity = r+(r+r) :=
      congrArg HistoryContraction.Tree.BatchRows.Size.arity dims.2.2.2.2.2
    rw [HistoryPartyTapeRun.batchPins,rc,sc,left,right]
  have countC:(X).count≤V:=by rw [←leftSeed.count,rc,sc];omega
  have stream:(X).table.stream=HistoryPartyBatch.dest J true node 0:=by
    change HistoryPartyBatch.dest J true (numeric mem (TickWorkspace.base u 18)-1) 0=_;rw [img.cursor]
  have mid:=PartyImage.after_checks q B height rom b y X img win nodeFit (.inr romHigh) headsHigh nodeHigh pairs
    (fun i=>nets ((idx c') i)) (fun i=>wires ((idx c') i)) rfl win.seed_room stream rfl countC (by omega) (by omega)
  obtain ⟨seed₁,p,_⟩:=q.active_seed B supported mid.resident y false t saved bounds mid.archive b baseNodes mid.row mid.cursor
    age nodeFit cap mask gradeFit headsHigh romHigh romFit level width work small kindSmall alph
  have p':Reads (Y c').regs (numeric (Y c').bootImage) lib r t:=p
  have rightSeed:ElectedSeed u (Y c'):=by
    let reached := (X).published (liveCheckJobs tile gd letter (fit).1 (fit).2 J mem t hist c')
    exact (congrArg (fun kind =>
      ElectedSeed u (⟨J,false,kind,reached⟩ : HistoryPartyBatchExec.Build W)) exactKind).mp seed₁
  have archive:=mounted_batch_archive B img.resident
  have lut:(arc).lut+staticSize B<2^W ∧ ((arc).lut+staticSize B≤TickWorkspace.base u 12 ∨ TickWorkspace.base u 19≤(arc).lut):=by
    unfold libraryWords at romFit
    change rom+StableCompactROMNative.size height+staticSize B<2^W ∧ _
    refine ⟨by omega,.inr ?_⟩
    exact romHigh.trans (Nat.le_add_right ..)
  have compact:(arc).pages+StableCompactROMNative.size height<2^W ∧ ((arc).pages+StableCompactROMNative.size height≤TickWorkspace.base u 12 ∨ TickWorkspace.base u 19≤(arc).pages):=by
    unfold libraryWords at romFit;exact ⟨by change rom+StableCompactROMNative.size height<_;omega,.inr romHigh⟩
  have vbig:1024≤V:=Nat.pow_le_pow_right (by decide:0<2) ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) u))
  have vbase:V≤V^2:=Nat.le_self_pow (by decide) V
  have scalar:V^2<2^W:=by
    have h:=TickWorkspace.word_space (u:=u) (i:=0) (by omega) (by change 0<V^4;positivity)
    have step:V^2≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
    change TickWorkspace.base u 0+V^4<2^W at h;omega
  have eFit:e≤V:=kindSmall 0
  have dFit:d≤V:=kindSmall 4
  have bank:e*d<2^W:=by have h:=Nat.mul_le_mul eFit dFit;rw [←pow_two] at h;omega
  have stripe:r*d<2^W:=by have h:=Nat.mul_le_mul small dFit;rw [←pow_two] at h;omega
  have complete:=physical_elected_room tile gd letter (fit).1 (fit).2 u arc fam 0 elected node mem t hist c' p'
    age nodeFit motifs cap mask img.cursor lut compact archive rfl rfl level (work.trans_lt (vbase.trans_lt scalar))
    quota leftSeed rightSeed rows maps countRoom hidden (fun g=>(Fintype.equivFin _ g).isLt.trans_le tags) bank stripe
  refine ⟨c',p',complete,?_⟩
  exact PartyImage.keep q B height rom b y img age nodeFit (.inr romHigh) headsHigh nodeHigh pairs
    (elected_room_outside tile gd letter (fit).1 (fit).2 J node mem t hist c' p' complete win (by omega) rows maps)

local notation "armOut" c:arg p:arg => electedOutput tile gd letter (fit).1 (fit).2 J node mem t hist c p
local notation "armTicks" c:arg p:arg => electedCost tile gd letter (fit).1 (fit).2 J mem t hist c p

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4500000 in
/-- The selected archived party executes at the reached memory, producing its
compiled pair, the four resident root words and the preserved refresh image.
The rate comes from the fixed refresh grid of the block. -/
theorem recorded_elected_arm
    (saved:SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds:RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (baseNodes:b.nodes=TickWorkspace.base u 44) (pairs:TickWorkspace.base u 19≤b.charges)
    (age:16≤u) (nodeFit:node<V^2) (cap:((fam).motifs+2)*((fam).parties+2)*8*32≤V)
    (mask:2^(fam).parties<2^W) (gradeFit:q.tile.last+1≤2^W) (headsHigh:TickWorkspace.base u 19≤heads)
    (romHigh:TickWorkspace.base u 19≤rom) (romFit:rom+libraryWords B height<2^W)
    (level:t.val=HistogramTileNetwork.siteHeight r d) (width:2^t.val≤V)
    (work:StableCompactNativeBudget.budget t.val≤V)
    (kindSmall:∀ a:Fin 7,((P₀).kind (arity B)).words a≤V)
    (rows:8*((L).rows+(R).rows)≤V)
    (maps:(r*(e*k+s)+s*(r+(r+r)))+(r*(h₀+(e*d+e*d))+e*(r*d+(r*d+r*d)))≤V)
    (countRoom:23*(r+max s e)≤V) (hidden:(L).bits+(R).bits≤V)
    (tags:Fintype.card ((Fin 3→Bool)→F)≤2^W) :
    ∃ c:readC,∃ p:Reads (Y c).regs (numeric (Y c).bootImage) lib r t,
      ElectedRoom tile gd letter (fit).1 (fit).2 J node mem t hist c p ∧
      r≤2^t.val ∧ r*d≤2^t.val ∧
      (HistoryPartyPair.procedure W J).Exec mem (armOut c p) (armTicks c p) ∧
      (∀ j : Fin 4,(armOut c p) (HistoryPartyPair.atPair J node 1+j.val)=
        (HistoryBoundedJoin.Info.words ⟨HistoryPartyPair.atPair J node 0,r*(e*k)+(r*h₀+e*(r*d)),
          (L).rows+(R).rows,(L).bits+(R).bits⟩ j:Word W)) ∧
      HistoryCompiledRows.Records (tag (K:=F)) (pair L R).compile (HistoryPartyPair.atPair J node 0) (armOut c p) ∧
      PartyImage (heads:=heads) q B height rom b y final (armOut c p) ∧
      armTicks c p≤gridPairRate (refreshGrid B)*(W+1)^3*(1+r) := by
  classical
  obtain ⟨c,p,room,image⟩:=q.recorded_elected_room B y t b img supported saved bounds baseNodes pairs
    age nodeFit cap mask gradeFit headsHigh romHigh romFit level width work kindSmall rows maps countRoom hidden tags
  have run:=HistoryRefreshEmitter.elected_arm tile gd letter (fit).1 (fit).2 J node mem t hist c p room
  have fee:=elected_pair_tariff tile gd letter (fit).1 (fit).2 J node mem t hist c p room
  have placed:=issued_party_rom B img.resident q.tile supported q.hh q.rowSum q.sym q.conn i₀ role
  have rate:partyTariff s e k h₀ d≤gridPairRate (refreshGrid B):=(party_rates_in_grid (refreshGrid B) P₀ placed.1).1
  exact ⟨c,p,room,room.copy,room.digit,run.1,run.2.1,run.2.2,image,
    fee.trans (Nat.mul_le_mul_right (1+r) (Nat.mul_le_mul_right ((W+1)^3) rate))⟩

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HistoryGatherExecution RAM.HistoryGatherBody
open RAM.HistoryStageBody.Physical PhysicalStage NavigationDirectory CompressorPacking Native
open RefreshDemandRows RefreshStageNav RefreshTies RefreshParty
open private header_congr from OAI.ThreeFlat.RAM.HistoryGatherBody
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {u K endHeaders : ℕ} {cur ctr : Word (16*u^10)}
    (q : RefreshReceipt F K cur)
local notation "W" => 16*u^10
local notation "m" => 2^q.s
local notation "P" => CursorSpace.recordPointers q.entry
local notation "bound" => q.entry.next.heap
variable {final mem : Memory (16*u^10)}
    (saved : SavedFrame cur ctr endHeaders q.entry.next.header bound q.out final)
    (limits : endHeaders≤q.cursor.heap ∧ bound≤cur.val ∧ cur.val<ctr.val)
    (body : ∀ i,(q.cursor.header ≤ i ∧ i<q.entry.next.header ∨ endHeaders ≤ i)→i<bound→mem i=final i)
    (y : (q.move.next q.term).Site)
local notation "z" => q.kernelSite y
local notation "ix" => (q.step.sites.ord y).val
local notation "pt" => (z).1.2
local notation "choice" => q.tile.winner (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input) (q.chosenBlock y)
local notation "issuedRecord" => issuedParty q.tile q.hh q.rowSum q.sym q.conn choice pt

open TickWorkspace

/-- The S12 pair-info count of the chronological party lies strictly below
S17, including the largest admissible node and bank. -/
theorem header_pair_info (J : HistoryGatherBody.Layout) (node : ℕ)
    (loc : HistoryRefreshEmitter.PartyWindow u J.party)
    (temp : J.temp=base u 17) (small : node<(volume u)^2)
    (atNode : (HistoryNodePorts.id J.nodePorts).value (fun _=>0) mem (fun _=>0)=(node:Word W)) :
    ((selected J mem).privatePage 1+1).val<J.temp := by
  have ptr : (selected J mem).privatePage 1=(HistoryPartyPair.atPair J.party node 1:Word W) := by
    simp [HistoryGatherBody.selected,HistoryPartyPair.atPair,HistoryScratch.atWord,atNode,Nat.cast_add,Nat.cast_mul]
  let bank : HistoryScratch.Local:=⟨J.party.motif+2,J.party.party+2,2,1⟩
  have ok : bank.Valid J.party.motifs J.party.parties :=
    ⟨Nat.add_lt_add_right loc.motif 2,Nat.add_lt_add_right loc.party 2,by change 2 < 8; decide,by change 1 < 32; decide⟩
  have two : 2≤volume u := Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.one_le_pow _ _ (show 1≤u by have:=loc.age;omega))
  have cell:=HistoryScratch.fits (base:=base u 12) (x:=bank) small loc.capacity ok (show 1<volume u by omega)
  have upper : HistoryPartyPair.atPair J.party node 1+1<base u 12+(volume u)^4 := by
    simpa [HistoryPartyPair.atPair,HistoryScratch.atWord,bank,loc.volume,loc.arena] using cell
  have apart := TickWorkspace.apart (u:=u) (by decide : 12<17)
  have less : HistoryPartyPair.atPair J.party node 1+1<J.temp:=by rw [temp];exact upper.trans_le apart
  have fit : HistoryPartyPair.atPair J.party node 1+1<2^W := by
    have big : 1024≤volume u:=Nat.pow_le_pow_right (by decide : 0<2)
      ((show 10≤u by have:=loc.age;omega).trans (Nat.le_self_pow (by decide) _))
    have four : volume u≤(volume u)^4:=Nat.le_self_pow (by decide) _
    have word:=TickWorkspace.word_space (i:=17) (u:=u) (by have:=loc.age;omega)
      (by change 17<(volume u)^4;omega)
    rw [temp] at less
    omega
  have successor : (HistoryPartyPair.atPair J.party node 1 : Word W) + 1 =
      ((HistoryPartyPair.atPair J.party node 1 + 1 : ℕ) : Word W) :=
    (Nat.cast_succ _).symm
  rw [ptr, successor, Fin.val_cast_of_lt fit]
  exact less

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.RAM.HistoryRefreshEmitter

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr PhysicalProcedure Diagonal.TickWorkspace
open HistoryGatherBody HistoryStageBody.Physical HistoryPartyBatchExec HistoryMotifJoin
open HistoryBoundedBody HistoryJoinScan Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F:Type*} [CommRing F] {u p a b node:ℕ} (arch:Archive) (f:Family) (w:Fin f.parties)
    (L:Tree F a) (R:Tree F b) (wire:Fin (a+b)→BitSource 0 p) (id:((Fin 3→Bool)→F)→ℕ)
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "A" => layout u arch f
local notation "C" => withMotif A 0
local notation "J" => rawArm A w.val
variable (oldCap:ℕ) (input stage live:Memory (16*u^10)) (plan:HistoryGatherExecution.Plan (16*u^10))
local notation "last₀" => HistoryGatherExecution.output J plan live
local notation "at₀" n => entryOf A node w id stage live last₀ n
local notation "lastIn" => at₀ f.parties
local notation "hub₀" => groupHub C lastIn true node p 0 1
local notation "build₀" => groupBuild C true hub₀ lastIn
local notation "tape₀" => Tape.tape («W»:=W) (fun _ : Fin 1=>(Tree.pair L R).compile)
    (fun _=>wire) id (fun _=>rootHeader A node w (a+b) p)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2600000 in
/-- Assemble the full native root from the actual selected two-child pair
and its port gather. All other roster entries are discharged by their
empty physical program, with their real input memory, and all root bank
order and table fits are calculated from the single physical arena. -/
theorem physical_kernel_run {kernelPtr incidentPtr m h pad:ℕ} (mode:(A).mode=.refresh m h pad)
    (original:IncidenceRead u f node w stage kernelPtr incidentPtr)
    (immutable:IncidenceRoom u node kernelPtr incidentPtr) (loc:IncidenceOutside u node kernelPtr incidentPtr)
    (age:16≤u) (nr:node<V^2) (nonempty:0<f.motifs)
    (cap:(f.motifs+2)*(f.parties+2)*8*32≤V) (mask:2^f.parties<2^W)
    (lut:arch.lut+1<2^W) (lutStride:arch.lutStride<2^W) (pages:arch.pages<2^W)
    (pageStride:arch.pageStride<2^W) (counts:arch.counts+1<2^W)
    (lutAway:arch.lut+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.lut)
    (countsAway:arch.counts+2≤base u 14+2*V ∨ base u 14+2*V+26≤arch.counts)
    (headerCap:3+5*f.demands+4*f.supplies≤V) (ports:HistoryGatherExecution.portsEnd J<2^W)
    (widths:∀ side k,k<HistoryGatherExecution.cap J side→plan.width side k≤V)
    (mapBase:plan.gatherBase=HistoryPartyPair.atPair (J).party node 2) (mapCount:plan.gatherCount≤V)
    (pairKeep:∀ x,OutsideNode u node x→live x=beforeWinner A node w id stage x)
    (moved:∀ x,OutsideNode u node x→stage x=input x)
    (prefixCost pairCost:ℕ)
    («prefix» :(HistoryNodePorts.phase W (A).nodePorts oldCap).Exec input stage prefixCost)
    (privateRoom:(C).privateStarts+9<2^W)
    (privateSafe:Protected (privateHeader C W) stage (C).privateStarts 9)
    (elected:(HistoryPartyPair.procedure W (J).party).Exec (beforeWinner A node w id stage) live pairCost)
    (compiled:HistoryCompiledRows.Records id (Tree.pair L R).compile (HistoryPartyPair.atPair (J).party node 0) live)
    (info:∀ j:Fin 4,live (HistoryPartyPair.atPair (J).party node 1+j.val)=
      (HistoryBoundedJoin.Info.words ⟨HistoryPartyPair.atPair (J).party node 0,a+b,L.rows+R.rows,L.bits+R.bits⟩ j:Word W))
    (copied:(HistoryGatherBody.procedure W J).Exec live last₀ (HistoryGatherExecution.tariff W J plan))
    (pins:∀ j:Fin (a+b),last₀ (HistoryPartyPair.atPair (J).party node 2+j.val)=(BitLayout.sourceAddress (wire j):Word W))
    (pinCount:a+b≤V) (gates:4*(Tree.pair L R).compile.cells≤V) (bits:L.bits+R.bits<2^W)
    (gateFit:∀ i j,HistoryCompiledRows.metadata id (Tree.pair L R).compile i j<2^W)
    (rootPins:p<2^W) (kernelArity:(selected C lastIn).oldBits+(selected C lastIn).newBits=(p:Word W))
    (guard:lastIn ((((C).privateStarts+8:ℕ):Word W).val)=0)
    (safe:Protected (joinHeader C W true) lastIn ((C).party.seed+64) (HistoryMotifJoin.rows C W true).length) :
    let pairFee:=choosePairCost A node w id stage live last₀ pairCost
    let mapFee:=chooseMapCost («W»:=W) A w (HistoryGatherExecution.tariff W J plan)
    let ticks:=prefixCost+(4+9*(2*(privateHeader C W).binds+4)+
      ((List.range f.parties).map (fun j=>pairFee j+mapFee j)).sum+
      (4+(HistoryMotifJoin.rows C W true).length*(2*(joinHeader C W true).binds+4)+(build₀).ticks tape₀))
    (kernelProcedure A W oldCap).Exec input ((build₀).output tape₀) ticks ∧
      HistoryCompiledRows.Records id (resultTree L R wire).compile (resultBank C node true 0) ((build₀).output tape₀) ∧
      (∀ j:Fin 4,(build₀).output tape₀ (resultBank C node true 1+j.val)=
        (HistoryBoundedJoin.Info.words ⟨resultBank C node true 0,p,(resultTree L R wire).rows,(resultTree L R wire).bits⟩ j:Word W)) ∧
      (∀ x,OutsideNode u node x→(build₀).output tape₀ x=input x) := by
  intro pairFee mapFee ticks
  have roster:=physical_roster_frame arch f node w id stage live plan original immutable loc age nr nonempty cap mask
    lut lutStride pages pageStride counts lutAway countsAway headerCap ports widths mapBase mapCount pairKeep
  have vac (j:Fin f.parties) (off:j≠w):VacantRoom (rawArm A j.val) node id (at₀ j.val):=
    (physical_vacant_room_all u arch f node w j (at₀ j.val) kernelPtr incidentPtr id (roster j.val j.isLt.le).1
      immutable off age nr nonempty cap mask lut lutStride pages pageStride counts lutAway countsAway headerCap ports).1
  have survives (j:Fin f.parties) (later:w.val<j.val):∀ x,winnerAddress A node w L R x→
      VacantAway (rawArm A j.val) node id (at₀ j.val) x:=by
    have off:j≠w:=by intro h;cases h;omega
    exact physical_vacant_away u arch f node w j off id _ (vac j off) L R age nonempty nr cap gates pinCount
  have frame:=roster f.parties le_rfl
  have oneFit:1<2^W := by have pos:=Nat.two_pow_pos f.parties;omega
  obtain ⟨idx,_,_,on,bitsAt⟩:=frame.1.root_fields arch f w immutable oneFit
  have order:=physical_root_order u arch f node w L R age nr nonempty cap pinCount gates bits
  obtain ⟨banks,stay,source⟩:=ordered_charts A node w L R wire id lastIn order
  have space:=physical_root_space (p:=p) u arch f node w L R id lastIn age nr nonempty cap pinCount gates gateFit
  have hubFit (j:Fin 6) : (hub₀).words j<2^W:=by
    have order₀:=order.lane₀;have order₁:=order.lane₁;have front:=order.front
    have lane₂:=order.lane₂;have lane₃:=order.lane₃;have lane₄:=order.lane₄
    have header:=order.header;have cmds:=order.commands;have wide:=order.wide
    fin_cases j
    · change resultBank C node true 0<2^W;omega
    · exact rootPins
    · change 0<2^W;omega
    · exact oneFit
    · change (A).party.seed+64+7<2^W;omega
    · change (A).party.arguments<2^W;omega
  have childFit:HistoryPartyPair.atPair (J).party node 1+1<2^W:=by have b:=source.child;omega
  have headerFit:(C).party.seed+64+(HistoryMotifJoin.rows C W true).length<2^W:=by
    rw [rows_len]
    change (A).party.seed+64+(7+7*(A).party.parties) < 2^W
    rw [← Nat.add_assoc]
    have commands := (Nat.le_add_right (A).party.commands 14).trans order.commands
    have arguments := (Nat.le_add_right (A).party.arguments 7).trans_lt order.wide
    exact (order.header.trans commands).trans_lt arguments
  have destFit:resultBank C node true 1<2^W:=by have b:=source.result;omega
  have ran:=emit_roster A node L R wire id stage w m h pad oldCap mode input prefixCost «prefix» privateRoom privateSafe
    live plan pairCost elected compiled info copied pins
    (physical_gather_away u arch f node w L R plan age nr nonempty cap gates mapBase) vac survives
    idx kernelArity guard on bitsAt mask childFit headerFit safe hubFit destFit source banks space stay
  exact ⟨ran.1,ran.2.1,ran.2.2.1,fun x hx=>(root_join_outside arch f w L R wire id lastIn age nonempty
    cap pinCount gates ran.2.2.2 hx).trans ((frame.2 x hx).trans (moved x hx))⟩

end
end ThreeFlat.RAM.HistoryRefreshEmitter

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HistoryStageBody.Physical
open RAM.HistoryPartyBatchExec RAM.HistoryRefreshEmitter RAM.NavigationNodeRows RAM.HistoryStageSetup
open RAM.HistoryGatherBody RAM.HistoryMotifJoin PhysicalStage NavigationDirectory CompressorPacking Native
open RefreshDemandRows RefreshStageNav RefreshTies
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {u K heads : ℕ} {cur ctr : Word (16*u^10)}
variable (q : RefreshReceipt F K cur) (arch : RAM.HistoryStageBody.Physical.Archive) (f : Family)
variable (y : (q.move.next q.term).Site)
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "C" => withMotif (layout u arch f) 0
local notation "node" => q.step.sites.id y
local notation "P" => CursorSpace.recordPointers q.entry
local notation "ix" => (q.step.sites.ord y).val

private theorem kernel_halfrows_at {final now : Memory W}
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds : heads≤q.cursor.heap ∧ q.entry.next.heap≤cur.val ∧ cur.val<ctr.val)
    (retained : ∀ x,q.cursor.heap≤x→x<q.entry.next.heap→now x=final x)
    (high : TickWorkspace.base u 19≤q.cursor.heap)
    (small : ∀ z,(q.move.next q.term).incidentWidth z<2^W) :
    State.HalfRows q.step.sites (fun i=>TickWorkspace.base u 19 ≤ i ∧ i<2^W) (numeric now) := by
  have restricted : SavedFrame cur ctr q.cursor.heap q.entry.next.header q.entry.next.heap q.out final :=
    fun a ac at' zone hi=>saved a ac at' (zone.imp_right bounds.1.trans) hi
  have issued:=q.halfRows (eEnd:=q.entry.next.heap) le_rfl restricted ⟨le_rfl,bounds.2⟩ small
  exact issued.transfer (fun a ha=>congrArg Fin.val (retained a ha.1 ha.2))
    (fun a ha=>⟨high.trans ha.1,ha.2.trans_le (bounds.2.1.trans cur.isLt.le)⟩)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1100000 in
/-- Every indirect read of the two refresh header scans remains outside its own
destination.  The final half descriptor comes from the actual issued geometry. -/
theorem kernel_header_protected {modePorts : ℕ} {final entry now : Memory W}
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds : heads≤q.cursor.heap ∧ q.entry.next.heap≤cur.val ∧ cur.val<ctr.val)
    (retained : ∀ x,q.cursor.heap≤x→x<q.entry.next.heap→entry x=final x)
    (b : Banks) (baseNodes : b.nodes=TickWorkspace.base u 44)
    (row : DirectoryRow b q.step.sites.layer (q.step.sites.ord y) entry)
    (current : numeric entry (TickWorkspace.base u 18)-1=node)
    (age : 16≤u) (nr : node<V^2) (high : TickWorkspace.base u 19≤q.cursor.heap)
    (parties : f.parties=2^q.s) (mode : f.mode=.refresh modePorts q.h q.pad)
    (motifs : 0<f.motifs) (capacity : (f.motifs+2)*(f.parties+2)*8*32≤V)
    (mask : 2^f.parties<2^W) (small : ∀ z,(q.move.next q.term).incidentWidth z<2^W)
    (frame : ∀ x,OutsideNode u node x→now x=entry x) :
    Protected (privateHeader C W) now (C).privateStarts 9 ∧
      Protected (joinHeader C W true) now ((C).party.seed+64) (HistoryMotifJoin.rows C W true).length := by
  let winner:=Fin.cast parties.symm (q.kernelSite y).1.2
  have inc:=q.incidence_at_entry saved bounds retained f parties y b baseNodes row current mask
  obtain ⟨room,loc⟩:=q.incidence_geometry y age high bounds.2.1 nr
  have seen:=inc.keep_outside f node winner loc frame
  have big : 128≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 7≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have nf:=HistoryShrinkEmitter.directory_address_space (u:=u) age big nr
  have fld:=seen.root_fields arch f winner room (by omega)
  have addr:=HistoryShrinkEmitter.nodeAddress_at (A:=C) (m:=now) (u:=u) rfl fld.1
  have large (a : ℕ) (h : TickWorkspace.base u 19≤a) : now a=entry a :=
    frame a (outside_of_region node age nr (.inr (.inl h)))
  have gap:=TickWorkspace.apart (u:=u) (by decide : 19<44)
  have dir (k : Fin 8) :
      wordAt now (HistoryMotifJoin.nodeAddress (C).nodePorts now) k.val=entry (b.nodes+8*node+k.val) := by
    rw [addr,wordAt,←Nat.cast_add,Fin.val_cast_of_lt (by have:=k.isLt;omega),baseNodes]
    exact large _ (by omega)
  have halves:=q.kernel_halfrows_at saved bounds
    (fun a lo hi=>(large a (high.trans lo)).trans (retained a lo hi)) high small
  have point:= (dir 6).trans row.incident
  have pos : 0<q.degree:=by rw [←q.degreeEq];omega
  have nodes:=HistoryShrinkEmitter.NodeReadCells.of_archive (A:=C) q.step.sites y age big pos node nr rfl addr halves point
  let z:=q.kernelSite y
  have span (t : Records.Table) (k : Fin (t.cols (1+q.h+q.pad))) :
      q.cursor.heap≤(P).dst t+ix*t.cols (1+q.h+q.pad)+k.val ∧
        (P).dst t+ix*t.cols (1+q.h+q.pad)+k.val<q.entry.next.heap := by
    have ord : (Records.rowOrder (1+q.h+q.pad) t (z,k)).val=ix*t.cols (1+q.h+q.pad)+k.val:=by
      rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,q.kernelSite_index]; rfl
    simpa only [ord,Nat.add_assoc] using q.record_interval t (Records.rowOrder _ t (z,k))
  have ms : MotifReadCells C now (fun i=>TickWorkspace.base u 19 ≤ i):=by
    apply MotifReadCells.of_addresses C ((P).kernel+ix*5) ((P).motif+ix*6) fld.2.1 fld.2.2.1
    · intro j
      obtain ⟨a,h⟩:=span .kernel j
      exact ⟨high.trans a,h.trans_le (bounds.2.1.trans cur.isLt.le)⟩
    · intro j
      obtain ⟨a,h⟩:=span .motif j
      exact ⟨high.trans a,h.trans_le (bounds.2.1.trans cur.isLt.le)⟩
  have count : q.step.sites.layer.childCount=1:=by rw [q.issued_layer]; rfl
  have children : (wordAt now (HistoryMotifJoin.nodeAddress (C).nodePorts now) 4).val≤V:=by
    have read := (dir ⟨4,by decide⟩).trans row.childCount
    calc
      _ = q.step.sites.layer.childCount :=
        (congrArg Fin.val read).trans (Fin.val_cast_of_lt (by rw [count]; omega))
      _ ≤ V := count.le.trans (by omega)
  have banks:=(HistoryShrinkEmitter.PhysicalBanks.layout u arch f).withMotif 0
  exact ⟨HistoryShrinkEmitter.privateHeader_physical banks big nodes ms (PrivateReadCells.refresh C mode),
    HistoryShrinkEmitter.joinHeader_physical banks age big true node nr capacity
      (by change 0<f.parties;rw [parties];exact Nat.two_pow_pos _)
      (fun _=>motifs) nodes ms fld.1 children⟩

open HistoryContraction
open private large_stride from OAI.ThreeFlat.RAM.HistoryShrinkPlacement
variable {Pins : Type} (L : q.input.Words Pins)
local notation "step₀" => q.wordStep L
local notation "target₀" => Move.WordStep.targetSite (R:=q.move) (i:=q.term) y
local notation "next₀" => ((q.move.target_eq q.term).symm ▸ (step₀).words.ports :
  PortLayout (q.move.rules.target q.term) Pins)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
/-- The roster leaves the typed root arity in its two native port banks and zero
in the private refresh guard read by the final bounded join. -/
theorem kernel_arity_guard {final entry now : Memory W}
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds : heads≤q.cursor.heap ∧ q.entry.next.heap≤cur.val ∧ cur.val<ctr.val)
    (retained : ∀ x,q.cursor.heap≤x→x<q.entry.next.heap→entry x=final x)
    (b : Banks) (baseNodes : b.nodes=TickWorkspace.base u 44)
    (row : DirectoryRow b q.step.sites.layer (q.step.sites.ord y) entry)
    (current : numeric entry (TickWorkspace.base u 18)-1=node)
    (age : 16≤u) (nr : node<V^2) (high : TickWorkspace.base u 19≤q.cursor.heap)
    (small : ∀ z,(q.move.next q.term).incidentWidth z<2^W)
    (T : HistoryStageRoot.Input) (id : T.id=node) (nodes : T.nodeBase=b.nodes)
    (cache : T.resultBase=TickWorkspace.base u 13)
    (seen : HistoryStageRoot.Ports L.ports next₀ (step₀).stage.count (step₀).stage.child target₀ T (numeric entry))
    (frame : ∀ x,OutsideNode u node x→now x=entry x)
    (words : now ((((C).privateStarts+8:ℕ):Word W).val)=0 ∧ ∀ k : Fin (1+1),
      now ((C).nodePorts.starts+k.val)=(childWidth (C).nodePorts 1 (numeric entry) ((C).nodePorts.starts+k.val):Word W)) :
    (HistoryGatherBody.selected C now).oldBits+(HistoryGatherBody.selected C now).newBits=
      ((step₀).stage.rootWidth target₀:Word W) ∧
      now ((((C).privateStarts+8:ℕ):Word W).val)=0 := by
  have one : (step₀).stage.count target₀=1 :=
    (refreshBinary_assembler_ports q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn L q.branch q.degreeEq target₀).1
  have ar : (step₀).stage.rootWidth target₀=(∑ i,L.ports.halfBits ((step₀).stage.child target₀ i).val)+
      (next₀).halfBits target₀ :=
    refreshBinary_assembler_arity q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn L q.branch q.degreeEq target₀
  let n:=(step₀).stage.count target₀
  let old:=∑ i,L.ports.halfBits ((step₀).stage.child target₀ i).val
  let H:=q.step.sites.layer.incident+ix*2
  have big : 128≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 7≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have nf:=HistoryShrinkEmitter.directory_address_space (u:=u) age big nr
  have nt : HistoryStageRoot.node T=TickWorkspace.base u 44+8*node := by
    simp only [HistoryStageRoot.node,nodes,baseNodes,id]
  have gap:=TickWorkspace.apart (u:=u) (by decide : 19<44)
  have early:=TickWorkspace.apart (u:=u) (by decide : 18<19)
  have large (a : ℕ) (h : TickWorkspace.base u 19≤a) : now a=entry a :=
    frame a (outside_of_region node age nr (.inr (.inl h)))
  have halves:=q.kernel_halfrows_at saved bounds
    (fun a lo hi=>(large a (high.trans lo)).trans (retained a lo hi)) high small
  have initial:=q.kernel_halfrows_at saved bounds retained high small
  have entered : numeric entry (HistoryStageRoot.node T+6)=H := by
    rw [nt,←baseNodes]
    exact (congrArg Fin.val row.incident).trans (Fin.val_cast_of_lt (initial.headerSafe y 0).2)
  have head : numeric now (HistoryStageRoot.node T+6)=H :=
    (congrArg Fin.val (large _ (by rw [nt];omega))).trans entered
  have fresh : HistoryStageRoot.halfWidth T (numeric now)=(next₀).halfBits target₀ :=
    (stage_half q.step.sites halves T y head).trans ((stage_half q.step.sites initial T y entered).symm.trans seen.fresh)
  have dir : HistoryStageRoot.childCount T (numeric now)=n :=
    (congrArg Fin.val (large (HistoryStageRoot.node T+4) (by rw [nt];omega))).trans seen.degree
  have first : numeric entry (C).nodePorts.cursor-1=T.id:=current.trans id.symm
  have nowId : numeric now (C).nodePorts.cursor-1=T.id := by
    change (now (TickWorkspace.base u 18)).val-1=T.id
    rw [frame _ (outside_of_region node age nr (.inr (.inr (.inl rfl))))]
    exact first
  have nb : (C).nodePorts.nodes=T.nodeBase:=by rw [nodes,baseNodes]; rfl
  have cb : (C).nodePorts.cache=T.resultBase:=by rw [cache]; rfl
  have pre:=HistoryStageSetup.child_prefix_value L.ports next₀ (step₀).stage.count
    (step₀).stage.child target₀ (C).nodePorts T (numeric entry) seen first nb cb n le_rfl
  have savedOld : now ((C).nodePorts.starts+n)=(old:Word W):=by
    calc
      _=(childWidth (C).nodePorts 1 (numeric entry) ((C).nodePorts.starts+n):Word W):=
        words.2 ⟨n,by change (step₀).stage.count target₀<1+1;omega⟩
      _=(childWidth (C).nodePorts n (numeric entry) ((C).nodePorts.starts+n):Word W):=rfl
      _=_:=congrArg (fun k:ℕ=>(k:Word W)) pre
  have headerFit : numeric now (HistoryStageRoot.node T+6)+1<2^W:=by rw [head];exact (halves.headerSafe y 1).2
  have lastFit : 0<numeric now (numeric now (HistoryStageRoot.node T+6))→
      HistoryStageBounds.lastIncident T (numeric now)+3<2^W:=by
    intro live
    rw [head,halves.count y] at live
    let last : Fin (2*q.degree):=⟨2*q.degree-1,by omega⟩
    have storedCount : numeric now H = 2*q.degree := halves.count y
    change numeric now (numeric now (HistoryStageRoot.node T+6)+1) +
      4*(numeric now (numeric now (HistoryStageRoot.node T+6))-1)+3 < 2^W
    rw [head,storedCount]
    exact (halves.entriesSafe y last 3).2
  have scale : 10*V≤TickWorkspace.stride u:=large_stride (by omega)
  have fits : (C).nodePorts.starts+n<2^W:=by
    change TickWorkspace.base u 18+3*V+(step₀).stage.count target₀<2^W
    rw [one];omega
  refine ⟨?_,words.1⟩
  rw [ar]
  exact root_ports C T now n old ((next₀).halfBits target₀) nowId nb (by omega)
    (by change TickWorkspace.base u 18<2^W;omega) (by rw [nt];omega) headerFit lastFit dir fits savedOld fresh


local notation "inputIso" => StageAddress.refreshInputIso q.input.graph q.input.chart
  (splitWord q.s q.rem) (tagOrdinal q.s).symm q.input.width
local notation "electedSite" => (q.chosenBlock y,(q.kernelSite y).1.2)

set_option maxRecDepth 15000 in
set_option maxHeartbeats 1800000 in
/-- The two surviving child-prefix values of the elected pair give the exact
old-port offset and old half arity used in its native gather. -/
theorem elected_prefix {entry post : Memory W} (T : HistoryStageRoot.Input) (id : T.id=node)
    (nodes : T.nodeBase=TickWorkspace.base u 44) (cache : T.resultBase=TickWorkspace.base u 13)
    (current : numeric entry (TickWorkspace.base u 18)-1=node)
    (seen : HistoryStageRoot.Ports L.ports next₀ (step₀).stage.count (step₀).stage.child target₀ T (numeric entry))
    (survives : ∀ j : Fin (1+1),post ((C).nodePorts.starts+j.val)=
      (childWidth (C).nodePorts 1 (numeric entry) ((C).nodePorts.starts+j.val):Word W)) :
    post (C).nodePorts.starts=0 ∧
      post ((C).nodePorts.starts+1)=(((inputIso).pushWord L).ports.halfBits electedSite:Word W) := by
  have shape:=refreshBinary_assembler_ports q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn L q.branch q.degreeEq target₀
  have one : (step₀).stage.count target₀=1:=shape.1
  have site : q.typedKernelSite y=electedSite:=
    Prod.ext (q.chosenBlock_coordinates y).1.symm (q.chosenBlock_coordinates y).2.symm
  have width (a : q.input.shape.Edge) : q.input.width a=refreshBinaryInput q.input ((inputIso).edge a) :=
    congrArg q.input.width ((StageAddress.refreshEdge (splitWord q.s q.rem)
      (tagOrdinal q.s).symm).symm_apply_apply a).symm
  have chart:=(inputIso).pushWord_halfBits_at L width electedSite
  have child (i : Fin ((step₀).stage.count target₀)) :
      L.ports.halfBits ((step₀).stage.child target₀ i).val=((inputIso).pushWord L).ports.halfBits electedSite := by
    have coord : ((step₀).stage.child target₀ i).val=(inputIso).site.symm (q.typedKernelSite y):=shape.2.1 i
    exact (congrArg L.ports.halfBits
      (coord.trans (congrArg (inputIso).site.symm site))).trans chart.symm
  have nb : (C).nodePorts.nodes=T.nodeBase:=by rw [nodes]; rfl
  have cb : (C).nodePorts.cache=T.resultBase:=by rw [cache]; rfl
  have first : numeric entry (C).nodePorts.cursor-1=T.id:=current.trans id.symm
  have atOne:=HistoryStageSetup.child_prefix_value L.ports next₀ (step₀).stage.count
    (step₀).stage.child target₀ (C).nodePorts T (numeric entry) seen first nb cb 1 one.ge
  have sum : childWidth (C).nodePorts 1 (numeric entry) ((C).nodePorts.starts+1)=
      ((inputIso).pushWord L).ports.halfBits electedSite := by
    calc
      _=childWidth (C).nodePorts ((step₀).stage.count target₀) (numeric entry) ((C).nodePorts.starts+1):=rfl
      _=_:=atOne.trans (by
        rw [Fin.sum_univ_one]
        exact child ((0 : Fin 1).castLE one.ge))
  constructor
  · simpa [childWidth,HistoryNodePorts.sum] using survives 0
  · exact (survives 1).trans (congrArg (fun k:ℕ=>(k:Word W)) sum)

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression Computability.VPVNP.MotifSelector LinearAlgebra.SpectralBooks
open RAM RAM.HistoryStageBody.Physical RAM.HistoryRefreshEmitter RAM.HistoryPartyBatchExec
open PhysicalStage CompressorPacking Native RefreshDemandRows RefreshStageNav RefreshTies
open HistogramTileNetwork MotifOuterTerms MotifOrderedCells MotifSelectorChecks HistoryContraction Tree
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F Pins:Type} [Field F] [Fintype F] {u K:ℕ} {cur:Word (16*u^10)}
    (q:RefreshReceipt F K cur) (words:q.input.Words Pins) (y:(q.move.next q.term).Site)
local notation "G" => refreshBinaryGraph q.input
local notation "port₀" => (tagOrdinal q.s).symm
local notation "bw₀" => refreshBinaryInput q.input
local notation "M" => refreshBinary q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn
local notation "iso₀" => StageAddress.refreshInputIso q.input.graph q.input.chart (splitWord q.s q.rem) port₀ q.input.width
local notation "old₀" => (iso₀).pushWord (H:=oldPortGraph (arrival G port₀)) (b:=bw₀) words
local notation "actualPort" => actualPortGraph (outputGraph G q.mult q.sym q.rowSum q.noLoop q.hm q.pad)
local notation "fresh₀" => (((M).next q.branch).halfWords Pins)
local notation "z" => q.chosenBlock y
local notation "v" => (q.kernelSite y).1.2
local notation "here" => (z,v)
local notation "e₀" => refreshBinaryEntry q.tile q.input
local notation "r₀" => refreshBinaryCopies q.tile q.input
local notation "t₀" => siteHeight (r₀ z) (e₀ z).bitCap
local notation "x₀" => refreshBinaryBranchOrder q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch
local notation "base₀" => (fun z₁=>q.tile.base (q.tile.winner G port₀ bw₀ z₁))
local notation "supply" => DoublePorts.connectedSupply q.mult q.hh q.rowSum q.sym q.conn
local notation "dense" => RefreshMotif.denseGraph (2^q.s)
local notation "sparse" => RefreshParty.sparseOrder q.mult q.sym q.rowSum v
local notation "shiftsFor" h₁:arg => sparseWidth q.mult base₀ r₀ e₀ h₁
local notation "freshAt" h₁:arg => WordLayout.atWidth (graph:=actualPort)
  (freshWidth q.mult q.rowSum (termWidth q.mult bw₀ (shiftsFor h₁)) q.pad) fresh₀
local notation "owner₀" => @id ((q.input.Base × BitWord q.rem) × Fin (2^q.s))
local notation "beforeAt" h₁:arg => (old₀).oldPin (freshAt h₁) owner₀ (fun _=>1)
  RefreshTies.singleChild here ⟨here,rfl⟩
local notation "afterAt" h₁:arg => (old₀).newPin (freshAt h₁) owner₀ (fun _=>1)
  RefreshTies.singleChild here

def issuedChecks := admission (q.issuedGood y) (q.issuedLetter y)
  (MotifNativeCompactors.partialInput F (r₀ z) t₀) (q.issuedQuota y)

def issuedPayload := tiled (q.issuedTile y) (MotifNativeCompactors.partialInput F ((r₀ z)*(e₀ z).bitCap) t₀)

open private pullPins from OAI.ThreeFlat.Diagonal.RefreshSiteTree

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
def issuedWire := by
  letI := (e₀ z).hasLetter
  let pins := WordLayout.argSize old₀ (freshAt x₀) owner₀ (fun _=>1) RefreshTies.singleChild here
  let src:=pullPins G q.mult q.hm q.pad q.sym q.rowSum q.noLoop (termWidth q.mult bw₀ (shiftsFor x₀))
    here pins (afterAt x₀)
  let P:=fun _:q.input.Base×BitWord q.rem=>ports q.mult
  let prior:=demandPin (arrival G port₀) (externalSite G) (external_site G port₀) P bw₀
    (shiftsFor x₀) z v (beforeAt x₀) src
  let out:=sparsePin (externalSite G) P bw₀ (shiftsFor x₀) z v src
  exact partyPointer (h:=0) (p:=pins) (d:=(e₀ z).bitCap) dense supply v (base₀ z) (profile G port₀ bw₀ z) (q.issuedHeader y) sparse
    (e₀ z).output (x₀ z) (fun a t=>.pin (prior a t)) (fun a t=>.pin (out a t))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private def treeAtHistory (history : refreshBinaryBranches q.tile q.input) : Σ p, Tree F p :=
  ⟨_, siteTree G port₀ q.mult bw₀ base₀ r₀ e₀ history q.hm q.hh q.pad q.sym q.rowSum q.noLoop q.conn
    z v (beforeAt history) (afterAt history)⟩

private def assemblyHistory {V L K₁ : Type} [Fintype V] [Fintype L] [Field K₁] {m : ℕ}
    (c : Fin m → Fin m → ℕ) (b : V×L → Bool×Fin m×Fin m → ℕ) (r : V×L → ℕ)
    (tiles : ∀ i, FixedMotifTile (RefreshMotif.denseGraph m) (ports c) (b i) K₁)
    (index : Fin (Fintype.card (Histories c b r tiles))) : Histories c b r tiles :=
  (Fintype.equivFin (Histories c b r tiles)).symm index

open private choice_instances from OAI.ThreeFlat.Diagonal.PhysicalStageRefresh

open private combine rewriteAgreement installedOutputAgreement from
  OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedStage
open private selectedStage_heq from
  OAI.ThreeFlat.Diagonal.PhysicalRefreshWordStage

private theorem combined_site_root {coeff pin : Type} [CommSemiring coeff]
    {sourceShape : HistoryContraction.Shape} {sourceRule : Rewrite sourceShape coeff}
    {sourceIndex : Fin sourceRule.count} {sourceInput : Form sourceShape pin}
    {sourceOutput : Form (sourceRule.target sourceIndex) pin}
    (made : Stage sourceRule sourceIndex sourceInput sourceOutput)
    {destShape : HistoryContraction.Shape} {destRule : Rewrite destShape coeff}
    {destIndex : Fin destRule.count} {destInput : Form destShape pin}
    {destOutput : Form (destRule.target destIndex) pin} {resultType : Sort _}
    (install : Stage destRule destIndex destInput destOutput → resultType)
    (shapes : sourceShape = destShape) (rules : HEq sourceRule destRule)
    (indices : sourceIndex.val = destIndex.val) (inputs : HEq sourceInput destInput)
    (outputs : HEq sourceOutput destOutput)
    (sites : (destRule.target destIndex).Site = (sourceRule.target sourceIndex).Site)
    (readRoot : resultType → (destRule.target destIndex).Site → Σ n, Tree coeff n)
    (preserves : ∀ st addr, readRoot (install st) addr = ⟨_,st.root addr⟩)
    (addr : (destRule.target destIndex).Site) :
    readRoot (combine made install shapes rules indices inputs outputs) addr =
      ⟨_,made.root (cast sites addr)⟩ := by
  cases shapes
  cases eq_of_heq rules
  cases (Fin.ext indices : sourceIndex = destIndex)
  cases eq_of_heq inputs
  cases eq_of_heq outputs
  exact preserves made addr

section InputTableView
open Expander
open private edgeAt labelAt from OAI.ThreeFlat.Diagonal.PhysicalRefreshInputStage

variable {m lanes hbits rem h pad : ℕ} {c : Fin m → Fin m → ℕ} {scale gap : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) scale) (A : State m lanes)
    (mix : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
    (hm : 2 ≤ m) (hh : 0 < h) (sym : ∀ i j, c i j = c j i)
    (rows : ∀ i, ∑ j, c i j = h) (zero : ∀ i, c i i = 0)
    (conn : Bound (transition c h) ℝ gap) (L : A.Words Pins)
local notation "tableSrc" => changeLanes A.graph mix
local notation "tableWidth" => refreshInput A mix port
local notation "tableRule" => T.step tableSrc port tableWidth hm hh sym rows zero conn
local notation "tableDst" => actualPortGraph (outputGraph tableSrc c sym rows zero hm pad)
local notation "tableIso" => StageAddress.refreshInputIso A.graph A.chart mix port A.width

attribute [local irreducible] RefreshMotif.Table.wordStageOnChart

set_option maxHeartbeats 240000 in
omit [Fintype F] in
private theorem inputTableRoot (idx : Fin (tableRule).count)
    (bits : LiveSlot A.Base (BitWord rem) m (1+h+pad) → ℕ)
    (fresh : WordLayout tableDst bits Pins) (same : (tableRule).target idx = WordLayout.shape tableDst bits)
    (output : WordLayout tableDst bits Pins)
    (wordsEq : ((tableIso).pushWord (H:=oldPortGraph (arrival tableSrc port)) (b:=tableWidth) L).inherited
      fresh id (fun _ => 1) singleChild = output)
    (addr : (A.Base × BitWord rem) × Fin m) :
    let installed := refreshInputStage T A mix port hm hh sym rows zero conn L idx bits fresh same output wordsEq
    let chart := T.wordStageOnChart tableSrc port tableWidth hm hh sym rows zero conn
      (U:=A.Site) (E:=(A.Base × Fin m) × BitWord lanes) (source:=A.shape.graph) (width:=A.width)
      tableIso L idx bits fresh same (edgeAt A mix port) (labelAt A mix port)
    (⟨installed.rootWidth addr,installed.root addr⟩ : Σ n, Tree F n) = ⟨chart.rootWidth addr,chart.root addr⟩ := rfl

end InputTableView

section InstalledRoot
open Expander

variable {m lanes hbits rem h pad : ℕ} {c : Fin m → Fin m → ℕ} {scale gap : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) scale) (A : State m lanes)
    (mix : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
    (hm : 2 ≤ m) (hh : 0 < h) (sym : ∀ i j, c i j = c j i)
    (rows : ∀ i, ∑ j, c i j = h) (zero : ∀ i, c i i = 0)
    (conn : Bound (transition c h) ℝ gap) (L : A.Words Pins)
    (idx : Fin (refreshMove T A mix port hm hh sym rows zero conn).rules.count)

attribute [local irreducible] CompressorRefresh.graph RefreshTies.freshWidth
  RefreshMotif.Table.wordStageOnChart RefreshTies.refreshAssemblyAtWidth

local notation "rootMove" => refreshMove T A mix port hm hh sym rows zero conn
local notation "rootSource" => RefreshPrepared.sourceStage T A mix port hm hh sym rows zero conn L idx
local notation "rootInstall" => RefreshPrepared.install T A mix port hm hh sym rows zero conn L idx
local notation "rootOutput" => refreshWords T A mix port hm hh sym rows zero conn L idx

set_option maxHeartbeats 220000 in
private abbrev rootsAt := combined_site_root rootSource rootInstall

set_option maxHeartbeats 220000 in
private abbrev rootsRule :=
  rootsAt T A mix port hm hh sym rows zero conn L idx rfl
    (heq_of_eq (rewriteAgreement T A mix port hm hh sym rows zero conn)) rfl

set_option maxHeartbeats 220000 in
private abbrev rootsInput :=
  rootsRule T A mix port hm hh sym rows zero conn L idx HEq.rfl

set_option maxHeartbeats 220000 in
private abbrev rootsForm :=
  rootsInput T A mix port hm hh sym rows zero conn L idx
    (installedOutputAgreement T A mix port hm hh sym rows zero conn L idx) rfl
    (fun installed addr => ⟨installed.rootWidth addr, installed.root addr⟩)

private def preservesRootPairs {fieldTy pinTy : Type} [Field fieldTy] {srcShape : Shape}
    {rewriteRule : Rewrite srcShape fieldTy} {branchIdx : Fin rewriteRule.count}
    {inputForm : Form srcShape pinTy} {oldForm newForm : Form (rewriteRule.target branchIdx) pinTy}
    (installer : Stage rewriteRule branchIdx inputForm oldForm →
      Stage rewriteRule branchIdx inputForm newForm) : Prop :=
  ∀ (st : Stage rewriteRule branchIdx inputForm oldForm) (addr : (rewriteRule.target branchIdx).Site),
    (⟨(installer st).rootWidth addr, (installer st).root addr⟩ : Σ arity, Tree fieldTy arity) =
      ⟨st.rootWidth addr, st.root addr⟩

open private installNumbered selectedBits selectedOutput outputShape sameGraph sameBits sameIssuedOutput
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

private theorem numberedRoots {fieldTy pinTy : Type} [Field fieldTy]
    {oldDegree oldLanes newDegree newLanes : ℕ} {oldState : State oldDegree oldLanes}
    (moveRule : Move fieldTy oldState newDegree newLanes) (branchIdx : Fin moveRule.rules.count)
    (oldWords : oldState.Words pinTy) (newWords : (moveRule.next branchIdx).Words pinTy)
    (siteEnum : Fintype (moveRule.next branchIdx).Site)
    (edgeEnum : Fintype (((moveRule.next branchIdx).Base × Fin newDegree) × BitWord newLanes))
    (portGraph : PortGraph (moveRule.next branchIdx).Site
      (((moveRule.next branchIdx).Base × Fin newDegree) × BitWord newLanes))
    (edgeBits : ((moveRule.next branchIdx).Base × Fin newDegree) × BitWord newLanes → ℕ)
    (portWord : WordLayout portGraph edgeBits pinTy)
    (shapeId : moveRule.rules.target branchIdx = @WordLayout.shape _ _ siteEnum edgeEnum portGraph edgeBits)
    (graphId : portGraph = (moveRule.next branchIdx).shape.graph) (bitsId : edgeBits = (moveRule.next branchIdx).width)
    (wordId : HEq portWord newWords) :
    preservesRootPairs
      (installNumbered moveRule branchIdx oldWords newWords siteEnum edgeEnum portGraph edgeBits portWord
        shapeId graphId bitsId wordId) := by
  intro st addr
  rfl

set_option maxHeartbeats 110000 in
private abbrev chartNumberedRoots :=
  numberedRoots (refreshMove T A mix port hm hh sym rows zero conn) idx L
    (refreshWords T A mix port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 110000 in
private abbrev chartLayoutRoots :=
  chartNumberedRoots T A mix port hm hh sym rows zero conn L idx
    (inferInstance : Fintype ((A.Base × BitWord rem) × Fin m))
    (inferInstance : Fintype (RefreshTies.LiveSlot A.Base (BitWord rem) m (1+h+pad)))
    (RefreshTies.actualPortGraph (RefreshTies.outputGraph (changeLanes A.graph mix) c sym rows zero hm pad))

set_option maxHeartbeats 110000 in
private abbrev chartWordsRoots :=
  chartLayoutRoots T A mix port hm hh sym rows zero conn L idx
    (selectedBits T A mix port hm hh sym rows zero conn idx)
    (selectedOutput T A mix port hm hh sym rows zero conn L idx)
    (outputShape T A mix port hm hh sym rows zero conn idx)

set_option maxHeartbeats 110000 in
private abbrev chartInstallRoots :=
  chartWordsRoots T A mix port hm hh sym rows zero conn L idx
    (sameGraph T A mix port hm hh sym rows zero conn idx)
    (sameBits T A mix port hm hh sym rows zero conn idx)
    (sameIssuedOutput T A mix port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 300000 in
private abbrev rootsInstalled :=
  rootsForm T A mix port hm hh sym rows zero conn L idx
    (chartInstallRoots T A mix port hm hh sym rows zero conn L idx)

attribute [local irreducible] combine RefreshIssued.selected RefreshPrepared.sourceStage
  RefreshPrepared.install refreshWords

set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
omit [Fintype F] in
private theorem chartStageRoot (addr : (A.Base × BitWord rem) × Fin m) :
    let actual := refreshWordStage T A mix port hm hh sym rows zero conn L idx
    (⟨actual.rootWidth addr, actual.root addr⟩ : Σ n, Tree F n) =
      ⟨(rootSource).rootWidth addr, (rootSource).root addr⟩ := by
  let observe (st : StageFor rootMove idx L rootOutput) : Σ n, Tree F n :=
    ⟨st.rootWidth addr, st.root addr⟩
  have casted := eq_of_heq (selectedStage_heq T A mix port hm hh sym rows zero conn L idx)
  have same := casted.trans (RefreshIssued.selected_eq T A mix port hm hh sym rows zero conn L idx)
  exact (congrArg observe same).trans (rootsInstalled T A mix port hm hh sym rows zero conn L idx addr)

end InstalledRoot

section TableAssemblyRoots

variable {hostTy colourTy tailTy : Type} [Fintype hostTy] [Fintype tailTy]
  [AddCommGroup colourTy] [AddCommGroup tailTy] {degree depth extra : ℕ}
  {entries : Fin degree → Fin degree → ℕ} {scale gap : ℝ}

section WidthProjection

variable (lifted : LiftedSlots hostTy degree (colourTy × tailTy)) (address : Fin degree ≃ colourTy)
  (portWidth : Address (hostTy × tailTy) degree → ℕ)
  (baseSize : hostTy × tailTy → Bool × Fin degree × Fin degree → ℕ)
  (copies : hostTy × tailTy → ℕ)
  (tiles : ∀ site, FixedMotifTile (RefreshMotif.denseGraph degree) (ports entries) (baseSize site) F)
  (capacity : ∀ site edge, profile lifted address portWidth site edge ≤ baseSize site edge * copies site)
  (enough : 2 ≤ degree) (positive : 0 < depth) (padding : ℕ)
  (symmetric : ∀ i j, entries i j = entries j i) (rowSum : ∀ i, ∑ j, entries i j = depth)
  (noLoop : ∀ i, entries i i = 0) (connected : Expander.Bound (Expander.transition entries depth) ℝ gap)
  (branch : Fin (Fintype.card (Histories entries baseSize copies tiles)))

local notation "widthRootHistory" => (Fintype.equivFin (Histories entries baseSize copies tiles)).symm branch
local notation "widthRootSelected" => freshWidth entries rowSum
  (termWidth entries portWidth (sparseWidth entries baseSize copies tiles widthRootHistory)) padding

variable (priorWords : WordLayout (oldPortGraph (arrival lifted address)) portWidth Pins)
  (edgeBits : LiveSlot hostTy tailTy degree (1+depth+padding) → ℕ)
  (newWords : WordLayout
    (actualPortGraph (outputGraph lifted entries symmetric rowSum noLoop enough padding)) edgeBits Pins)
  (shapeId : (histogramStep lifted address entries portWidth baseSize copies tiles capacity enough
    positive padding symmetric rowSum noLoop connected).target branch =
      WordLayout.shape (actualPortGraph (outputGraph lifted entries symmetric rowSum noLoop enough padding)) edgeBits)
  (addr : (hostTy × tailTy) × Fin degree)

local notation "widthRootInstalled" =>
  refreshAssemblyAtWidth lifted address entries portWidth baseSize copies tiles capacity enough positive
    padding symmetric rowSum noLoop connected branch priorWords edgeBits newWords shapeId
local notation "widthRootRaw" =>
  refreshAssembly lifted address entries portWidth baseSize copies tiles capacity enough positive
    padding symmetric rowSum noLoop connected branch priorWords (WordLayout.atWidth widthRootSelected newWords)

attribute [local irreducible] refreshAssembly siteTree

set_option maxHeartbeats 220000 in
omit [Fintype F] in
private theorem rawAssemblyWidthRoot :
    (⟨(widthRootInstalled).rootWidth addr, (widthRootInstalled).root addr⟩ : Σ n, Tree F n) =
      ⟨(widthRootRaw).rootWidth addr, (widthRootRaw).root addr⟩ := rfl

end WidthProjection

section ChartProjection

variable {sourceSites sourceEdges : Type} [Fintype sourceSites] [Fintype sourceEdges]
  (table : RefreshMotif.Table F entries (1+depth+extra) scale)
  (lifted : LiftedSlots hostTy degree (colourTy × tailTy)) (address : Fin degree ≃ colourTy)
  (portWidth : Address (hostTy × tailTy) degree → ℕ)
  (enough : 2 ≤ degree) (positive : 0 < depth)
  (symmetric : ∀ i j, entries i j = entries j i) (rowSum : ∀ i, ∑ j, entries i j = depth)
  (noLoop : ∀ i, entries i i = 0) (connected : Expander.Bound (Expander.transition entries depth) ℝ gap)
  {source : PortGraph sourceSites sourceEdges} {width : sourceEdges → ℕ}

local notation "chartRootOld" => oldPortGraph (arrival lifted address)

variable (chart : HistoryRelabel.Iso (WordLayout.shape source width)
    (WordLayout.shape (oldPortGraph (arrival lifted address)) portWidth))
  (inputWords : WordLayout source width Pins)
  (branch : Fin (table.step lifted address portWidth enough positive symmetric rowSum noLoop connected).count)
  (edgeBits : LiveSlot hostTy tailTy degree (1+depth+extra) → ℕ)
  (newWords : WordLayout
    (actualPortGraph (outputGraph lifted entries symmetric rowSum noLoop enough extra)) edgeBits Pins)
  (shapeId : (table.step lifted address portWidth enough positive symmetric rowSum noLoop connected).target branch =
    WordLayout.shape (actualPortGraph (outputGraph lifted entries symmetric rowSum noLoop enough extra)) edgeBits)
  (widthId : ∀ edge, width edge = portWidth (chart.edge edge))
  (labelId : ∀ edge digit, (chart.label edge digit).val = digit.val)
  (addr : (hostTy × tailTy) × Fin degree)

local notation "chartRootStage" => table.wordStageOnChart lifted address portWidth enough positive symmetric
  rowSum noLoop connected chart inputWords branch edgeBits newWords shapeId widthId labelId
local notation "chartRootBase" => (fun site => table.base (table.winner lifted address portWidth site))
local notation "chartRootCopies" => table.repeats lifted address portWidth
local notation "chartRootTiles" => table.entry lifted address portWidth
local notation "chartRootHistory" =>
  (Fintype.equivFin (Histories entries chartRootBase chartRootCopies chartRootTiles)).symm branch
local notation "chartRootSelected" => freshWidth entries rowSum
  (termWidth entries portWidth (sparseWidth entries chartRootBase chartRootCopies chartRootTiles chartRootHistory)) extra
local notation "chartRootPacked" => chart.pushWord (H:=chartRootOld) (b:=portWidth) inputWords
local notation "chartRootRaw" =>
  refreshAssembly lifted address entries portWidth chartRootBase chartRootCopies chartRootTiles
    (fun site => table.fits _) enough positive extra symmetric rowSum noLoop connected branch
    chartRootPacked (WordLayout.atWidth chartRootSelected newWords)

attribute [local irreducible] refreshAssemblyAtWidth refreshAssembly siteTree

set_option maxHeartbeats 300000 in
omit [Fintype F] in
private theorem refreshTableAssemblyRoot :
    (⟨(chartRootStage).rootWidth addr, (chartRootStage).root addr⟩ : Σ n, Tree F n) =
      ⟨(chartRootRaw).rootWidth addr, (chartRootRaw).root addr⟩ :=
  rawAssemblyWidthRoot lifted address portWidth chartRootBase chartRootCopies chartRootTiles
    (fun _site => table.fits _) enough positive extra symmetric rowSum noLoop connected
    branch chartRootPacked edgeBits newWords shapeId addr

end ChartProjection
end TableAssemblyRoots

section BinaryRoot
variable {siteBits rest height padding : ℕ} {entries : Fin (2^siteBits) → Fin (2^siteBits) → ℕ}
    {scale gap : ℝ} (table : RefreshMotif.Table F entries (1+height+padding) scale)
    (source : State (2^siteBits) (siteBits+rest))
    (portsFit : 2≤2^siteBits) (heightPos : 0<height)
    (symmetric : ∀ i j, entries i j=entries j i) (rowSum : ∀ i, ∑ j, entries i j=height)
    (noLoop : ∀ i, entries i i=0) (connected : Expander.Bound (Expander.transition entries height) ℝ gap)
    (input : source.Words Pins)
    (branch : Fin (refreshBinary table source portsFit heightPos symmetric rowSum noLoop connected).rules.count)
    (addr : (source.Base × BitWord rest) × Fin (2^siteBits))

local notation "binaryChart" => RefreshPrepared.sourceStage table source (splitWord siteBits rest)
  (Native.tagOrdinal siteBits).symm portsFit heightPos symmetric rowSum noLoop connected input branch

set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
omit [Fintype F] in
private theorem binaryChartRoot :
    (⟨_, refreshBinary_siteTree table source portsFit heightPos symmetric rowSum noLoop connected
      input branch addr⟩ : Σ n, Tree F n) = ⟨(binaryChart).rootWidth addr, (binaryChart).root addr⟩ :=
  chartStageRoot table source (splitWord siteBits rest) (Native.tagOrdinal siteBits).symm
    portsFit heightPos symmetric rowSum noLoop connected input branch addr

set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
omit [Fintype F] in
private theorem chartTreeAt (destination : (source.Base × BitWord rest) × Fin (2^siteBits))
    (same : addr = destination) :
    (⟨_, refreshBinary_siteTree table source portsFit heightPos symmetric rowSum noLoop connected
      input branch addr⟩ : Σ n, Tree F n) =
      ⟨(binaryChart).rootWidth destination, (binaryChart).root destination⟩ := by
  subst destination
  exact binaryChartRoot table source portsFit heightPos symmetric rowSum noLoop connected input branch addr

end BinaryRoot

section RawAssemblyRoot
open Expander
variable {Vertex Channel Lane : Type} [Fintype Vertex] [Fintype Lane]
    [AddCommGroup Channel] [AddCommGroup Lane] {m height : ℕ}
    (graph : LiftedSlots Vertex m (Channel × Lane)) (port : Fin m ≃ Channel)
    (weights : Fin m → Fin m → ℕ) (width : Address (Vertex × Lane) m → ℕ)
    (base : Vertex × Lane → Bool × Fin m × Fin m → ℕ) (copies : Vertex × Lane → ℕ)
    (tiles : ∀ a, FixedMotifTile (RefreshMotif.denseGraph m) (ports weights) (base a) F)
    (fits : ∀ a e, profile graph port width a e ≤ base a e * copies a)
    (large : 2 ≤ m) (positive : 0 < height) (padding : ℕ)
    (symmetric : ∀ i j, weights i j = weights j i)
    (rows : ∀ i, ∑ j, weights i j = height) (noLoop : ∀ i, weights i i = 0)
    {gap : ℝ} (connected : Bound (transition weights height) ℝ gap)
    (index : Fin (Fintype.card (Histories weights base copies tiles)))

local notation "rootChoice" => assemblyHistory weights base copies tiles index
local notation "rootOutGraph" => actualPortGraph (outputGraph graph weights symmetric rows noLoop large padding)
local notation "rootOutWidth" => freshWidth weights rows
  (termWidth weights width (sparseWidth weights base copies tiles rootChoice)) padding
local notation "rootStage" => refreshAssembly graph port weights width base copies tiles fits large
  positive padding symmetric rows noLoop connected index

attribute [local irreducible] siteTree actualPortGraph freshWidth

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
omit [Fintype F] in
private theorem rawAssemblySiteRoot
    (old : WordLayout (oldPortGraph (arrival graph port)) width Pins)
    (fresh : WordLayout rootOutGraph rootOutWidth Pins) (point : (Vertex × Lane) × Fin m) :
    (⟨(rootStage old fresh).rootWidth point, (rootStage old fresh).root point⟩ : Σ n, Tree F n) =
    ⟨old.argSize fresh id (fun _ => 1) singleChild point,
      siteTree graph port weights width base copies tiles rootChoice large positive padding
        symmetric rows noLoop connected point.1 point.2
        (old.oldPin fresh id (fun _ => 1) singleChild point ⟨point, rfl⟩)
        (old.newPin fresh id (fun _ => 1) singleChild point)⟩ := rfl

end RawAssemblyRoot

section PreparedAssemblyRoot
open Expander
open private selectedBits outputWords outputShape selectedOutput issuedWords
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage
open private edgeAt labelAt from OAI.ThreeFlat.Diagonal.PhysicalRefreshInputStage

variable {m lanes hbits rem h pad : ℕ} {c : Fin m → Fin m → ℕ} {scale gap : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) scale) (A : State m lanes)
    (mix : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
    (hm : 2 ≤ m) (hh : 0 < h) (sym : ∀ i j, c i j = c j i)
    (rows : ∀ i, ∑ j, c i j = h) (zero : ∀ i, c i i = 0)
    (conn : Bound (transition c h) ℝ gap) (L : A.Words Pins)
    (idx : Fin (refreshMove T A mix port hm hh sym rows zero conn).rules.count)
    (addr : (A.Base × BitWord rem) × Fin m)

local notation "preparedSource" => RefreshPrepared.sourceStage T A mix port hm hh sym rows zero conn L idx
local notation "preparedBits" => selectedBits T A mix port hm hh sym rows zero conn idx
local notation "preparedWords" => outputWords (Pins := Pins) T A mix port hm hh sym rows zero conn idx
local notation "preparedShape" => outputShape T A mix port hm hh sym rows zero conn idx
local notation "preparedOutput" => selectedOutput T A mix port hm hh sym rows zero conn L idx
local notation "preparedAgreement" => issuedWords T A mix port hm hh sym rows zero conn L idx
local notation "preparedInput" => refreshInputStage T A mix port hm hh sym rows zero conn L idx
  preparedBits preparedWords preparedShape preparedOutput preparedAgreement

attribute [local irreducible] refreshInputStage RefreshMotif.Table.wordStageOnChart
  refreshAssemblyAtWidth refreshAssembly siteTree

set_option maxRecDepth 6000 in
set_option maxHeartbeats 280000 in
omit [Fintype F] in
private theorem preparedInputRoot :
    (⟨(preparedSource).rootWidth addr, (preparedSource).root addr⟩ : Σ n, Tree F n) =
      ⟨(preparedInput).rootWidth addr, (preparedInput).root addr⟩ := rfl

set_option maxRecDepth 6000 in
set_option maxHeartbeats 280000 in
private abbrev preparedTableRoot :=
  (preparedInputRoot T A mix port hm hh sym rows zero conn L idx addr).trans
    (inputTableRoot T A mix port hm hh sym rows zero conn L idx
      preparedBits preparedWords preparedShape preparedOutput preparedAgreement addr)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 350000 in
private abbrev preparedRawAssemblyRoot :=
  (preparedTableRoot T A mix port hm hh sym rows zero conn L idx addr).trans
    (refreshTableAssemblyRoot T (changeLanes A.graph mix) port (refreshInput A mix port)
      hm hh sym rows zero conn (source := A.shape.graph) (width := A.width)
      (StageAddress.refreshInputIso A.graph A.chart mix port A.width)
      L idx preparedBits preparedWords preparedShape (edgeAt A mix port) (labelAt A mix port) addr)

end PreparedAssemblyRoot

section AssemblyRoot
open private outputWords from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage
local notation "rawChart" => RefreshPrepared.sourceStage q.tile q.input (splitWord q.s q.rem)
  port₀ q.hm q.hh q.sym q.rowSum q.noLoop q.conn words q.branch
local notation "rawHistory" => assemblyHistory q.mult base₀ r₀ e₀ q.branch
local notation "chartWords" => outputWords (Pins := Pins) q.tile q.input (splitWord q.s q.rem)
  port₀ q.hm q.hh q.sym q.rowSum q.noLoop q.conn q.branch
local notation "chartFresh" => WordLayout.atWidth (graph := actualPort)
  (freshWidth q.mult q.rowSum (termWidth q.mult bw₀ (shiftsFor rawHistory)) q.pad) chartWords

set_option maxRecDepth 10000 in
set_option maxHeartbeats 600000 in
private abbrev rawSelectedSiteTree :=
  rawAssemblySiteRoot G port₀ q.mult bw₀ base₀ r₀ e₀ (fun _ => q.tile.fits _)
    q.hm q.hh q.pad q.sym q.rowSum q.noLoop q.conn q.branch old₀ chartFresh here

-- Compare the chart projections before inspecting the raw assembly's site tree.
attribute [local irreducible] siteTree freshWidth WordLayout.atWidth

set_option maxRecDepth 6000 in
set_option maxHeartbeats 350000 in
private abbrev chartRawAssembly :=
  preparedRawAssemblyRoot q.tile q.input (splitWord q.s q.rem) port₀
    q.hm q.hh q.sym q.rowSum q.noLoop q.conn words q.branch here

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
omit [Fintype F] in
private theorem chartAssemblyHistory :
    (⟨(rawChart).rootWidth here, (rawChart).root here⟩ : Σ n, Tree F n) =
      treeAtHistory q words y rawHistory :=
  (chartRawAssembly q words y).trans (rawSelectedSiteTree q words y)

end AssemblyRoot

local notation "kernel" => resultTree (q.issuedChecks y) (q.issuedPayload y) (q.issuedWire words y)

private theorem packedPartyResult {coeff : Type} [CommRing coeff] {a b pins : ℕ}
    (left : Tree coeff a) (right : Tree coeff b) (wire : Fin (a+b) → BitSource 0 pins) :
    (⟨pins,Tree.join 0 1 (fun _ => a+b) (fun _ => wire) (fun _ => pair left right)⟩ :
      Σ p, Tree coeff p) = ⟨pins,resultTree left right wire⟩ := rfl

section
attribute [local irreducible] partyPointer pair admission tiled demandPin sparsePin
  headerGood headerLetter numberHistogram HistogramTileNetwork.tile Fintype.equivFin

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
omit [Fintype F] in
private theorem issuedHistoryKernel :
    treeAtHistory q words y x₀ = ⟨_,kernel⟩ := by
  dsimp only [treeAtHistory, siteTree, Tree.directParty, Tree.party, issuedChecks, issuedPayload,
    issuedWire, issuedTile, issuedGood, issuedLetter, issuedQuota, issuedHeader];
    apply packedPartyResult
end

local notation "ws" => q.wordStep words
local notation "v₀" => Move.WordStep.targetSite (R:=q.move) (i:=q.term) y

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private abbrev assemblerTreeAt :=
  refreshBinary_assembler_root q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn
    words q.branch q.degreeEq v₀

set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
private abbrev chartTreeAtChosen :=
  chartTreeAt q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn words q.branch
    (q.typedKernelSite y) here
    (Prod.ext (q.chosenBlock_coordinates y).1.symm (q.chosenBlock_coordinates y).2.symm)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
omit [Fintype F] in
private theorem assemblyHistorySelected :
    assemblyHistory q.mult base₀ r₀ e₀ q.branch = x₀ := by
  unfold assemblyHistory refreshBinaryBranchOrder
  exact @choice_instances (refreshBinaryBranches q.tile q.input) _ _ q.branch
    (refreshBinaryBranchCount q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 500000 in
omit [Fintype F] in
private theorem treeAtSelectedHistory :
    treeAtHistory q words y (assemblyHistory q.mult base₀ r₀ e₀ q.branch) =
      treeAtHistory q words y x₀ :=
  congrArg (treeAtHistory q words y) (assemblyHistorySelected q)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
omit [Fintype F] in
/-- The compiled tree is the actual root of the selected, degree-recast word
step, including its pin arity and both geometric port maps. -/
theorem issued_tree :
    (⟨(ws).stage.rootWidth v₀,(ws).stage.root v₀⟩:Σ p,Tree F p)=⟨_,kernel⟩ :=
  (assemblerTreeAt q words y).trans <|
    (chartTreeAtChosen q words y).trans <|
      (chartAssemblyHistory q words y).trans <|
        (treeAtSelectedHistory q words y).trans (issuedHistoryKernel q words y)

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt


namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HistoryStageBody.Physical
open RAM.HistoryPartyBatchExec RAM.HistoryRefreshEmitter RAM.NavigationNodeRows HistoryStageSetup
open PhysicalStage NavigationDirectory CompressorPacking Native RefreshDemandRows RefreshStageNav RefreshTies
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F:Type} [Field F] [Fintype F] {u K heads:ℕ} {cur ctr:Word (16*u^10)}
    (q:RefreshReceipt F K cur) (B:Block F) {height rom:ℕ} (b:Banks) (y:(q.move.next q.term).Site)
    {final initial:Memory (16*u^10)} (img:PartyImage (heads:=heads) q B height rom b y final initial)
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "node" => q.step.sites.id y
local notation "f" => refreshFamily B rom height
local notation "arc" => archive B rom height K
local notation "A" => layout u arc f
local notation "stage" => fillSegment (A).nodePorts.starts (1+1)
    (fun k=>(HistoryMotifJoin.childWidth (A).nodePorts 1 (numeric initial) k:Word W)) initial

private theorem singleton_node_phase_execution (word arity : ℕ) (ports : HistoryNodePorts.Layout)
    (mem : Memory word) (singleton : arity = 1)
    (run : (HistoryNodePorts.phase word ports arity).Exec mem
      (fillSegment ports.starts (arity+1)
        (fun i => (HistoryMotifJoin.childWidth ports arity (numeric mem) i : Word word)) mem)
      (4+(arity+1)*(2*(HeaderScan.closed (w:=word) (HistoryMotifJoin.childPrefix ports arity)).binds+4))) :
    (HistoryNodePorts.phase word ports 1).Exec mem
      (fillSegment ports.starts (1+1)
        (fun i => (HistoryMotifJoin.childWidth ports 1 (numeric mem) i : Word word)) mem)
      (HistoryNodePorts.phaseCost 1) := by
  subst arity
  rw [← HistoryNodePorts.phase_ticks word ports 1]
  exact run

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
/-- The true selected node computes both S18 predecessor prefixes, preserves its
directory and ROM, and executes every dormant party before its elected arm. -/
theorem initialize_kernel
    (saved:SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds:RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (supported:B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (baseNodes:b.nodes=TickWorkspace.base u 44) (baseCharges:TickWorkspace.base u 19≤b.charges)
    (age:16≤u) (nr:node<V^2) (lib:TickWorkspace.base u 19≤rom) (archHigh:TickWorkspace.base u 19≤heads)
    (motifs:0<(f).motifs) (cap:((f).motifs+2)*((f).parties+2)*8*32≤V) (mask:2^(f).parties<2^W)
    (lut:(arc).lut+1<2^W) (step:(arc).lutStride<2^W) (pages:(arc).pages<2^W)
    (pageStep:(arc).pageStride<2^W) (counts:(arc).counts+1<2^W)
    (lutAway:(arc).lut+2≤TickWorkspace.base u 14+2*V ∨ TickWorkspace.base u 14+2*V+26≤(arc).lut)
    (countsAway:(arc).counts+2≤TickWorkspace.base u 14+2*V ∨ TickWorkspace.base u 14+2*V+26≤(arc).counts)
    (header:3+5*(f).demands+4*(f).supplies≤V) (ports:HistoryGatherExecution.portsEnd A<2^W)
    (current:numeric initial (TickWorkspace.base u 18)=node+1)
    (read:q.step.data.Reads (numeric initial))
    (cells:q.step.data.Footprint (fun i=>TickWorkspace.base u 19 ≤ i ∧ i<2^W) (numeric initial))
    (children:∀ k:Fin q.step.sites.layer.childCount,q.step.data.child (q.step.sites.ord y) k<V^2) :
    let role:=(q.kernelSite y).1.2
    let card:=(issued_party_rom B img.resident q.tile supported q.hh q.rowSum q.sym q.conn 0 role).2.1
    let win:=Fin.cast card.symm role
    (HistoryNodePorts.phase W (A).nodePorts 1).Exec initial stage (HistoryNodePorts.phaseCost 1) ∧
      (∀ x,OutsideNode u node x→stage x=initial x) ∧
      PartyImage (heads:=heads) q B height rom b y final stage ∧
      PartyImage (heads:=heads) q B height rom b y final (beforeWinner A node win (tag (K:=F)) stage) := by
  intro role card win
  have one:q.step.sites.layer.childCount=1:=by rw [q.issued_layer];rfl
  have big:128≤V:=by
    change 128≤2^(u^10)
    calc 128=2^7:=by decide
         _≤2^(u^10):=Nat.pow_le_pow_right (by decide) ((show 7≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have moved (x:ℕ) (h:OutsideNode u node x) : stage x=initial x :=
    starts_outside arc f initial age 1 (by omega) h
  have nHigh:TickWorkspace.base u 19≤b.nodes:=by
    rw [baseNodes]
    unfold TickWorkspace.base
    omega
  have stageImg:=PartyImage.keep q B height rom b y img age nr (.inr lib) archHigh nHigh baseCharges moved
  refine ⟨?_,moved,stageImg,?_⟩
  · exact @singleton_node_phase_execution W q.step.sites.layer.childCount (A).nodePorts initial one
      (@HistoryShrinkEmitter.child_starts_archive u A initial q.step.sites.layer
        q.step.data (q.step.sites.ord y)
        (HistoryShrinkEmitter.PhysicalBanks.layout u arc f) rfl age big nr (by omega) (by omega)
        b baseNodes current img.row read cells children)
  · exact PartyImage.before_checks q B height rom b y stageImg saved bounds supported baseNodes baseCharges
      age nr lib archHigh motifs cap mask lut step pages pageStep counts lutAway countsAway header ports

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM Diagonal Diagonal.PhysicalStage HistoryRefreshEmitter
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] [Fintype F]

/-- The complete port-page suffix of the final refresh grid fits in the actual
mounted library, including the zero-digit case. -/
theorem issued_port_window {u s h pad height rom : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {C : ℝ}
    (B : Block F) (T : RefreshMotif.Table F c (1+h+pad) C)
    (supported : B.publicTemplate (.refresh s h pad c C T)) (i : Fin (T.last+1)) (j : Fin (2^s))
    (whole : archiveWindow u rom (libraryWords B height)) :
    archiveWindow u ((refreshFamily B rom height).ports+(refreshGrid B).stride*(i.val*2^s+j.val))
      (refreshGrid B).stride := by
  let G:=refreshGrid B
  let fam:=refreshFamily B rom height
  let test : StaticMotif F→Prop := fun
    | .shrink .. => True
    | .refresh s _ _ _ _ T => ∀ (i:Fin (T.last+1)) (j:Fin (2^s)),
      archiveWindow u ((fam).ports+(G).stride*(i.val*2^s+j.val)) (G).stride
  have here : test (.refresh (B.exponent B.levels) B.h B.pad B.graph _ B.refresh) := by
    intro i j
    have get:=grid_row (refreshParty B) i j
    obtain ⟨hr,_⟩:=List.getElem?_eq_some_iff.mp get
    change 2^B.exponent B.levels*i.val+j.val<(G).rows.length at hr
    rw [Nat.mul_comm (2^B.exponent B.levels) i.val] at hr
    have width:=Nat.mul_le_mul_left (G).stride hr
    rw [Nat.mul_succ] at width
    have total : libraryWords B height=StableCompactROMNative.size height+staticSize B+
        HistoryCompactorCounts.size height+((List.ofFn (shrinkGrid B)).map Grid.size).sum+(G).size := by
      simp [libraryWords,gridSize,grids,G,Nat.add_assoc]
    have size : (G).size=7*(G).rows.length+(G).stride*(G).rows.length := Nat.add_mul ..
    have addr : (fam).ports=rom+StableCompactROMNative.size height+staticSize B+HistoryCompactorCounts.size height+
        ((List.ofFn (shrinkGrid B)).map Grid.size).sum+7*(G).rows.length := rfl
    apply whole.sub
    · rw [addr];omega
    · rw [addr,total,size];omega
  exact ((congrArg test (B.public_refresh supported)).mpr here) i j

end
end ThreeFlat.RAM.HistoryStageBody.Physical

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HistoryGatherExecution RAM.HistoryGatherBody
open RAM.HistoryStageBody.Physical RAM.HistoryRefreshEmitter PhysicalStage NavigationDirectory CompressorPacking Native
open RefreshDemandRows RefreshStageNav RefreshTies RefreshParty TickWorkspace
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {u K heads : ℕ} {cur ctr : Word (16*u^10)}
    (q : RefreshReceipt F K cur)
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "m" => 2^q.s
local notation "P" => CursorSpace.recordPointers q.entry
local notation "deg" => 1+q.h+q.pad
variable (y : (q.move.next q.term).Site)
local notation "z" => q.kernelSite y
local notation "ix" => (q.step.sites.ord y).val
local notation "node" => q.step.sites.id y
local notation "pt" => (z).1.2
local notation "choice" => q.tile.winner (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input) (q.chosenBlock y)
local notation "kptr" => (P).kernel+ix*5
local notation "iptr" => (P).motif+ix*6

/-- Bounds for the fixed register arithmetic of the concrete refresh gather.
The physical site witnesses that the stored half table has a nonempty row. -/
structure GatherStaticBounds : Prop where
  histFit : (P).counts+(q.chosenIndex y).val*K<2^W
  stageBound : 3*m<2^W
  laneBound : 2^q.rem<2^W
  degreeBound : q.h<2^W
  halfLimit : (P).halves+(Fintype.card q.input.Base*m*2^q.rem)*(2*deg)*4≤2^W
  portFit : m<2^W
  four : 4≤2^W

omit [Fintype F] in
theorem gather_static_bounds (limit : q.entry.next.heap≤cur.val) : q.GatherStaticBounds y := by
  let v:=Fintype.card q.input.Base
  let N:=v*m*2^q.rem
  have vpos : 0<v:=Fintype.card_pos_iff.mpr ⟨(q.chosenBlock y).1⟩
  have mpos : 0 < m :=Nat.two_pow_pos _
  have lanes : 0<2^q.rem:=Nat.two_pow_pos _
  have dpos : 0<deg:=by omega
  have live : 0<v*m:=Nat.mul_pos vpos mpos
  have count : 0<N:=Nat.mul_pos live lanes
  have mN : m≤N:=(Nat.le_mul_of_pos_left m vpos).trans (Nat.le_mul_of_pos_right _ lanes)
  have lN : 2^q.rem≤N:=Nat.le_mul_of_pos_left _ live
  have three : 3*m≤N*(8*deg):=calc
    3*m≤3*N:=Nat.mul_le_mul_left _ mN
    _=N*3:=Nat.mul_comm _ _
    _≤_:=Nat.mul_le_mul_left N (by omega)
  have lrow : N≤N*(8*deg):=Nat.le_mul_of_pos_right N (by omega)
  have drow : 8*deg≤N*(8*deg):=Nat.le_mul_of_pos_left _ count
  have raw:=CursorSpace.record_layout (c:=q.cursor) (K:=K) (v:=v) (a:=q.s) (t:=q.rem) (h:=q.h) (pad:=q.pad)
  have half : (P).halves+N*(8*deg)≤q.entry.next.heap:=raw.2.2.2.2
  have word : q.entry.next.heap<2^W:=limit.trans_lt cur.isLt
  have heap : q.cursor.heap≤q.entry.next.heap:=by
    change _≤(allocate K _ _).next.heap
    rw [heap_step];omega
  have quota : q.cursor.dense+K*(v*2^q.rem)≤q.cursor.heap:=q.histogram.1
  have idx : (q.chosenIndex y).val≤v*2^q.rem:=(q.chosenIndex y).isLt.le
  have dense:= Nat.mul_le_mul_left K idx
  have grid : 3*m<2^W:=by omega
  have hm:=q.hm
  refine ⟨?_,grid,by omega,by omega,?_,by omega,by omega⟩
  · change q.cursor.dense+(q.chosenIndex y).val*K<2^W
    rw [Nat.mul_comm (q.chosenIndex y).val K];omega
  · change (P).halves+N*(2*deg)*4≤2^W
    rw [show N*(2*deg)*4=N*(8*deg) by ring]
    exact half.trans word.le

/-- Numerical extents in the concrete memory after the elected pair. The map
is the combined party's S12 bank and the source buffers occupy S17. -/
structure GatherSpace (J : HistoryGatherBody.Layout) (mem : Memory W) (page kind size : ℕ) : Prop where
  positive : 0<(J).party.V
  resident : portsEnd J<2^W
  portsBeforeControl : portsEnd J≤base u 18
  pairCountFit : HistoryPartyPair.atPair (J).party node 1+1<2^W
  portWindow : q.PortWindow (endHeaders:=heads) J mem page (HistoryPortCatalogue.stride (J).demandCap (J).supplyCap (J).digitCap)
  kindRoom : kind+7≤2^W
  pageRoom : page+HistoryPortCatalogue.stride (J).demandCap (J).supplyCap (J).digitCap≤2^W
  mapBase : ((selected J mem).privatePage 2).val=HistoryPartyPair.atPair (J).party node 2
  mapRoom : ((selected J mem).privatePage 2).val+size<2^W
  range : portsEnd J≤((selected J mem).privatePage 2).val ∨ ((selected J mem).privatePage 2).val+size≤(J).temp
  pairInfo : ((selected J mem).privatePage 1+1).val<(J).temp
  keep : ∀addr,let sel:=selected J mem
    addr=((J).nodePorts.cursor:Word W).val ∨ addr=(nodeWord J mem+5).val ∨ addr=(sel.kernel+4).val ∨
    addr=(sel.incident+2).val ∨ addr=(sel.incident+3).val ∨
    (∃i:Fin 7,addr=(sel.kindPage+(i.val:Word W)).val) ∨
    (page≤addr ∧ addr<page+HistoryPortCatalogue.stride (J).demandCap (J).supplyCap (J).digitCap) →
    (addr<(J).temp ∨ portsEnd J≤addr) ∧ (addr<((selected J mem).privatePage 2).val ∨ ((selected J mem).privatePage 2).val+size≤addr)
  clear : let last:=page+HistoryPortCatalogue.stride (J).demandCap (J).supplyCap (J).digitCap
    (last≤(J).temp ∨ portsEnd J≤page) ∧ (last≤((selected J mem).privatePage 2).val ∨ ((selected J mem).privatePage 2).val+size≤page)
  headAddress : page+HistoryPortCatalogue.headerBase (J).demandCap (J).supplyCap<2^W
  pinRoom : ∀{p h:ℕ}, 2+p≤2^W → ∀i:Fin p,BitLayout.sourceAddress (.pin i : BitSource h p)<2^W

variable (B : Block F) {rom height : ℕ}
local notation "fam" => refreshFamily B rom height
local notation "G" => refreshGrid B
local notation "J" => rawArm (layout u (archive B rom height K) fam) (pt).val
local notation "index" => (choice).val*m+(pt).val
local notation "pg" => (fam).ports+(G).stride*index
local notation "kg" => (fam).kinds+7*index

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
/-- The issued archived row and mounted final family give every address
separation used by the active map scan, even for an empty map. -/
theorem gather_space {final mem : Memory W}
    (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (limits : heads≤q.cursor.heap ∧ q.entry.next.heap≤cur.val ∧ cur.val<ctr.val)
    (retained : ∀i,q.cursor.heap ≤ i→i<q.entry.next.heap→mem i=final i)
    (parties : (fam).parties=m)
    (read : IncidenceRead u fam node (Fin.cast parties.symm pt) mem kptr iptr)
    (room : IncidenceRoom u node kptr iptr)
    (age : 16≤u) (smallNode : node<V^2) (capacity : ((fam).motifs+2)*((fam).parties+2)*8*32≤V)
    (headersHigh : base u 19≤q.cursor.header) (headsHigh : base u 19≤heads)
    (romHigh : base u 19≤rom) (romFit : rom+libraryWords B height<2^W)
    (tileFit : q.tile.last+1≤2^W) (histFit : (P).counts+(q.chosenIndex y).val*K<2^W)
    (headerBound : 3+5*(fam).demands+4*(fam).supplies≤V)
    (size : ℕ) (sizeBound : size≤V) :
    q.GatherSpace (heads:=heads) y J mem pg kg size := by
  have big : 1024≤V:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have v4 : V≤V^4:=Nat.le_self_pow (by decide) _
  have control : base u 18+stride u<2^W:=TickWorkspace.word_space (i:=18) (by omega) (by change 18<V^4;omega)
  have sep18:=TickWorkspace.apart (u:=u) (by decide : 17<18)
  have sep19:=TickWorkspace.apart (u:=u) (by decide : 18<19)
  have sep12:=TickWorkspace.apart (u:=u) (by decide : 12<17)
  have sep44:=TickWorkspace.apart (u:=u) (by decide : 18<44)
  have stop : portsEnd J≤base u 18 := by
    have n : 1+(fam).demands+(fam).supplies≤V:=by omega
    have area:=Nat.mul_le_mul_right V n
    have growth:V^2≤V^4:=Nat.pow_le_pow_right (Nat.two_pow_pos _) (by decide)
    rw [pow_two] at growth
    change base u 17+V^4≤base u 18 at sep18
    change base u 17+(1+(fam).demands+(fam).supplies)*V≤_
    omega
  have whole : archiveWindow u rom (libraryWords B height) := ⟨romFit,.inr (by omega)⟩
  have kind:=issued_kind_window B q.tile supported choice pt whole
  have page:=issued_port_window B q.tile supported choice pt whole
  have strideEq : HistoryPortCatalogue.stride (J).demandCap (J).supplyCap (J).digitCap=(G).stride:=rfl
  have highK:base u 18≤kg:=by
    change _≤gridStart B rom height+((List.ofFn (shrinkGrid B)).map Grid.size).sum+7*index
    unfold gridStart;omega
  have highP:base u 18≤pg:=by
    change _≤gridStart B rom height+((List.ofFn (shrinkGrid B)).map Grid.size).sum+7*(G).rows.length+(G).stride*index
    unfold gridStart;omega
  have raw:=read.root_fields (archive B rom height K) fam (Fin.cast parties.symm pt) room (by omega)
  have atNode : (HistoryNodePorts.id (J).nodePorts).value (fun _=>0) mem (fun _=>0)=(node:Word W):=raw.1
  have ker : (selected J mem).kernel=((kptr : ℕ):Word W):=raw.2.1
  have inc : (selected J mem).incident=((iptr : ℕ):Word W):=raw.2.2.1
  have kfit:=room.kernel
  have ifit:=room.incident
  have rowIndex (tbl : Records.Table) (c : Fin (tbl.cols deg)) :
      (Records.rowOrder deg tbl (z, c)).val=ix*tbl.cols deg+c.val := by
    rw [Records.rowOrder,RefreshStageLayout.pair_index,Records.siteOrder_val,q.kernelSite_index]; rfl
  have kinterval:=q.record_interval .kernel (Records.rowOrder deg .kernel (z,(0:Fin 5)))
  have iinterval:=q.record_interval .motif (Records.rowOrder deg .motif (z,(0:Fin 6)))
  rw [rowIndex .kernel (0:Fin 5)] at kinterval
  rw [rowIndex .motif (0:Fin 6)] at iinterval
  have kstart : q.cursor.heap≤kptr:=by
    have b : q.cursor.heap≤(P).kernel+(ix*5+0):=kinterval.1
    simpa only [Nat.add_zero] using b
  have istart : q.cursor.heap ≤ iptr := by
    have b : q.cursor.heap≤(P).motif+(ix*6+0):=iinterval.1
    simpa only [Nat.add_zero] using b
  have plus (a b:ℕ) (fits:a+b<2^W) : ((a:Word W)+(b:Word W)).val=a+b := by
    rw [←Nat.cast_add,Fin.val_cast_of_lt fits]
  have shape : wordAt mem (selected J mem).incident 2=((choice).val:Word W) := by
    have issued:=q.elected_at_entry saved limits retained y tileFit histFit (2:Fin 4)
    apply Fin.ext
    change (mem ((selected J mem).incident+(2:Word W)).val).val=_
    have atShape : ((selected J mem).incident+(2 : Word W)).val=(iptr : ℕ)+2 := by
      rw [inc]
      exact plus (iptr : ℕ) 2 (by omega)
    rw [atShape,Fin.val_cast_of_lt ((choice).isLt.trans_le tileFit)]
    exact issued
  let pre:=List.ofFn (shrinkGrid B)
  have pages:=Mounted.selected_pages (B:=B) («G»:=refreshGrid B) (pre:=pre) («m»:=mem) J choice pt
    rfl rfl rfl rfl rfl parties rfl shape
  have kindPtr : (selected J mem).kindPage=((kg : ℕ):Word W):=pages.1
  have cursor : ((J).nodePorts.cursor:Word W).val=base u 18:=Fin.val_cast_of_lt room.cursor
  have nodeAt : (nodeWord J mem+5).val=base u 44+8*node+5:=by
    have word : nodeWord J mem=((base u 44+8*node:ℕ):Word W):=by
      change (base u 44:Word W)+8*((HistoryNodePorts.id (J).nodePorts).value (fun _=>0) mem (fun _=>0))=_
      rw [atNode,Nat.cast_add,Nat.cast_mul];rfl
    rw [word];exact plus _ 5 room.node
  have kval (i:ℕ) (h:i≤4) : ((selected J mem).kernel+(i:Word W)).val=kptr+i := by
    rw [ker];exact plus (kptr : ℕ) i (by omega)
  have ival (i:ℕ) (h:i≤5) : ((selected J mem).incident+(i:Word W)).val=iptr+i := by
    rw [inc];exact plus (iptr : ℕ) i (by omega)
  have kloc (i:Fin 7) : ((selected J mem).kindPage+(i.val:Word W)).val=kg+i.val:=by
    rw [kindPtr];exact plus (kg : ℕ) i.val (by have:=kind.1;have:=i.isLt;omega)
  have highKer (i:ℕ) (h:i≤4) : base u 18≤((selected J mem).kernel+(i:Word W)).val := by rw [kval i h];omega
  have highInc (i:ℕ) (h:i≤5) : base u 18≤((selected J mem).incident+(i:Word W)).val := by rw [ival i h];omega
  have k4:=highKer 4 le_rfl
  have i2:=highInc 2 (by decide)
  have i3:=highInc 3 (by decide)
  have window : q.PortWindow (endHeaders:=heads) J mem pg (HistoryPortCatalogue.stride (J).demandCap (J).supplyCap (J).digitCap) := by
    refine ⟨⟨.inr (by rw [cursor];exact stop),.inr (by rw [nodeAt];omega),
      .inr (stop.trans (highKer 3 (by decide))),fun _=>.inr (stop.trans k4),fun _=>.inr (stop.trans (highInc 5 le_rfl))⟩,
      .inr (stop.trans k4),.inr (stop.trans i2),?_,?_,?_⟩
    · intro i;right;rw [kloc];omega
    · intro i _;right;omega
    · intro i hi _;right;rcases hi with h|h <;> omega
  have mv:(fam).motifs=1:=rfl
  have pgood : (pt).val<(fam).parties:=(pt).isLt.trans_eq parties.symm
  let bnk : HistoryScratch.Local:=⟨2,(pt).val+2,2,2⟩
  have valid : bnk.Valid (fam).motifs (fam).parties:=⟨by change 2<_;rw [mv];decide,
    Nat.add_lt_add_right pgood 2,by change 2<8; decide,by change 2<32; decide⟩
  have win : base u 12≤HistoryPartyPair.atPair (J).party node 2 ∧
      HistoryPartyPair.atPair (J).party node 2+V≤base u 12+TickWorkspace.stride u ∧
      HistoryPartyPair.atPair (J).party node 2+V<2^W :=
    local_window u fam node age smallNode capacity bnk valid
  let countBank : HistoryScratch.Local:=⟨2,(pt).val+2,2,1⟩
  have countValid : countBank.Valid (fam).motifs (fam).parties :=
    ⟨by change 2<_;rw [mv];decide,Nat.add_lt_add_right pgood 2,by change 2<8; decide,by change 1<32; decide⟩
  have countEnd:= (local_window u fam node age smallNode capacity countBank countValid).2.2
  change HistoryPartyPair.atPair (J).party node 1+V<2^W at countEnd
  have ptr:=private_map_base J node mem atNode (by have:=win.2.2;omega)
  have low : ((selected J mem).privatePage 2).val+size≤base u 17 :=by rw [ptr];have:=win.2.1;omega
  have layout := PartyWindow.of_layout (archive B rom height K) fam 0 (pt).val age (by rw [mv];decide) pgood capacity
  have info:=header_pair_info J node layout rfl smallNode atNode
  refine ⟨by change 0<V;omega,by omega,stop,by omega,window,kind.1.le,by rw [strideEq];exact page.1.le,
    ptr,by rw [ptr];have:=win.2.2;omega,.inr low,info,?_,⟨.inr (by omega),.inr (by omega)⟩,?_,?_⟩
  · intro a
    dsimp only
    intro choices
    have high : base u 18≤a := by
      rcases choices with rfl|rfl|rfl|rfl|rfl|⟨i,rfl⟩|inPage
      · rw [cursor]
      · rw [nodeAt];omega
      · exact k4
      · exact i2
      · exact i3
      · rw [kloc];omega
      · exact highP.trans inPage.1
    exact ⟨.inr (stop.trans high),.inr (by omega)⟩
  · have cmp : HistoryPortCatalogue.headerBase (J).demandCap (J).supplyCap≤(G).stride:=by
      change HistoryPortCatalogue.headerBase (G).demand (G).supply≤HistoryPortCatalogue.stride (G).demand (G).supply (G).digits
      simp only [HistoryPortCatalogue.headerBase,HistoryPortCatalogue.supplyBase,HistoryPortCatalogue.stride];omega
    have h:=page.1;omega
  · intro p h fits i
    change 2+i.val<_
    have:=i.isLt;omega

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression Computability.VPVNP.MotifSelector LinearAlgebra.SpectralBooks
open RAM RAM.HistoryStageBody.Physical RAM.HistoryRefreshEmitter RAM.HistoryPartyBatchExec
open RAM.HistoryPartySpecialization RAM.HistoryBoundedBody RAM.HistoryBoundedJoin RAM.HistoryMotifJoin
open PhysicalStage NavigationDirectory CompressorPacking Native RefreshDemandRows RefreshStageNav RefreshTies
open HistogramTileNetwork MotifOuterTerms MotifOrderedCells MotifSelectorChecks HistoryContraction Tree
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F Pins:Type} [Field F] [Fintype F] {u K heads:ℕ} {cur ctr:Word (16*u^10)}
    (q:RefreshReceipt F K cur) (B:Block F) (words:q.input.Words Pins) (y:(q.move.next q.term).Site)
    {height rom:ℕ} (b:RAM.NavigationNodeRows.Banks) {final initial:Memory (16*u^10)}
    (img:PartyImage (heads:=heads) q B height rom b y final initial)
    (supported:B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "node" => q.step.sites.id y
local notation "fam" => refreshFamily B rom height
local notation "arc" => archive B rom height K
local notation "A₀" => layout u arc fam
local notation "C₀" => withMotif A₀ 0
local notation "role" => (q.kernelSite y).1.2
local notation "z₀" => q.chosenBlock y
local notation "hk" => (issued_party_rom B img.resident q.tile supported q.hh q.rowSum q.sym q.conn 0 role).2.1
local notation "winner" => Fin.cast (hk).symm role
local notation "J" => rawArm A₀ (winner).val
local notation "tag₀" => tag (K:=F)
local notation "stage" => fillSegment (A₀).nodePorts.starts (1+1)
    (fun k=>(childWidth (A₀).nodePorts 1 (numeric initial) k:Word W)) initial
local notation "live" => beforeWinner A₀ node winner tag₀ stage
local notation "r" => refreshBinaryCopies q.tile q.input z₀
local notation "ix" => q.tile.winner (refreshBinaryGraph q.input) (tagOrdinal q.s).symm (refreshBinaryInput q.input) z₀
local notation "rec₀" => issuedParty q.tile q.hh q.rowSum q.sym q.conn ix role
local notation "tile₀" => q.issuedTile y
local notation "good" => q.issuedGood y
local notation "letter" => q.issuedLetter y
local notation "quota" => q.issuedQuota y
local notation "arityFit" => q.issued_arity y B supported img.resident
local notation "entry₀" => refreshBinaryEntry q.tile q.input z₀
local notation "d" => (entry₀).bitCap
local notation "e" => 2*q.h
local notation "s" => Fintype.card (entry₀).Alphabet
local notation "k" => (entry₀).bits
local notation "h₀" => (q.issuedHeader y).arity
variable (selectedLevel : Fin (height+1))
local notation "t" => selectedLevel
local notation "left" => q.issuedChecks y
local notation "right" => q.issuedPayload y
local notation "wire" => q.issuedWire words y
local notation "root" => resultTree left right wire
local notation "ws" => q.wordStep words
local notation "v" => Move.WordStep.targetSite (R:=q.move) (i:=q.term) y
local notation "next₀" => ((q.move.target_eq q.term).symm ▸ (ws).words.ports : PortLayout _ Pins)
local notation "P" => CursorSpace.recordPointers q.entry
local notation "kernelBase" => (P).kernel+(q.step.sites.ord y).val*5
local notation "motifBase" => (P).motif+(q.step.sites.ord y).val*6

/-- The output required by the chronological stage join, measured at the
same final machine state as every cached row and both traversal controls. -/
def Emitted (post:Memory W) (ticks:ℕ) : Prop :=
  (kernelProcedure A₀ W 1).Exec initial post ticks ∧
    HistoryCompiledRows.Records tag₀ ((ws).stage.root v).compile (resultBank C₀ node true 0) post ∧
    (∀ j:Fin 4,post (resultBank C₀ node true 1+j.val)=
      (Info.words ⟨resultBank C₀ node true 0,(ws).stage.rootWidth v,
        ((ws).stage.root v).rows,((ws).stage.root v).bits⟩ j:Word W)) ∧
    (∀ i,OutsideNode u node i→post i=initial i) ∧
    ticks≤blockKernelRate B*((W+1)^3*(1+r)+((ws).stage.root v).resources)

local notation "eout" => electedOutput («W»:=W) (B:=height) («r»:=r) (ar:=arity B)
  tile₀ good letter (arityFit).1 (arityFit).2 (J).party node live
local notation "eticks" => electedCost («W»:=W) (B:=height) («r»:=r) (ar:=arity B)
  tile₀ good letter (arityFit).1 (arityFit).2 (J).party live

private theorem transport_compiled {F:Type*} {wordWidth stream header:ℕ} {mem:Memory wordWidth} {id:((Fin 3→Bool)→F)→ℕ}
    {X Y:Σ a,Tree F a} (eq:X=Y)
    (table:HistoryCompiledRows.Records id Y.2.compile stream mem)
    (summary:∀ j:Fin 4,mem (header+j.val)=(Info.words ⟨stream,Y.1,Y.2.rows,Y.2.bits⟩ j:Word wordWidth)) :
    HistoryCompiledRows.Records id X.2.compile stream mem ∧
      ∀ j:Fin 4,mem (header+j.val)=(Info.words ⟨stream,X.1,X.2.rows,X.2.bits⟩ j:Word wordWidth) := by
  cases eq
  exact ⟨table,summary⟩

open private liveCheckJobs from OAI.ThreeFlat.RAM.HistoryRefreshElectedJobs
local notation "finishBatch" => electedBatch («W»:=W) (K:=F) (ar:=arity B)
  tile₀ good letter (arityFit).1 (arityFit).2 (J).party
local notation "finishLib" => HistoryStaticArchive.all F (arity B)
local notation "checkBatch" => finishBatch live true
local notation "payloadBatch" proof:arg => finishBatch
  ((checkBatch).published (liveCheckJobs («W»:=W) (K:=F) (B:=height) («r»:=r) (ar:=arity B)
    tile₀ good letter (arityFit).1 (arityFit).2 (J).party live t quota proof)) false

set_option maxRecDepth 18000 in
set_option maxHeartbeats 3400000 in
/-- Finish the literal selected refresh from its checked batch receipt and the
typed geometric pin gather, through every idle arm and the final scalar/header
checks, then read out the original word-step tree across its degree cast. -/
theorem finish_kernel (heightEq : selectedLevel.val = siteHeight r d) :
    ∀ {check : Reads (checkBatch).regs (numeric (checkBatch).bootImage) finishLib r t}
    {payload : Reads (payloadBatch check).regs (numeric (payloadBatch check).bootImage) finishLib r t}
    (_saved:SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (_bounds:RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (_baseNodes:b.nodes=TickWorkspace.base u 44) (_age:16≤u) (_nr:node<V^2)
    (_high:TickWorkspace.base u 19≤heads) (_mode:(fam).mode=.refresh (2^q.s) q.h q.pad)
    (_nonempty:0<(fam).motifs) (_cap:((fam).motifs+2)*((fam).parties+2)*8*32≤V) (_mask:2^(fam).parties<2^W)
    (_lut:(arc).lut+1<2^W) (_step:(arc).lutStride<2^W) (_pages:(arc).pages<2^W)
    (_pageStep:(arc).pageStride<2^W) (_counts:(arc).counts+1<2^W)
    (_lutAway:(arc).lut+2≤TickWorkspace.base u 14+2*V ∨ TickWorkspace.base u 14+2*V+26≤(arc).lut)
    (_countsAway:(arc).counts+2≤TickWorkspace.base u 14+2*V ∨ TickWorkspace.base u 14+2*V+26≤(arc).counts)
    (_header:3+5*(fam).demands+4*(fam).supplies≤V) (_ports:HistoryGatherExecution.portsEnd J<2^W)
    (_small:∀ a,(q.move.next q.term).incidentWidth a<2^W)
    (T:HistoryStageRoot.Input) (_id:T.id=node) (_nodes:T.nodeBase=b.nodes) (_cache:T.resultBase=TickWorkspace.base u 13)
    (_seen:HistoryStageRoot.Ports words.ports next₀ (ws).stage.count (ws).stage.child v T (numeric initial))
    (_pref:(HistoryNodePorts.phase W (A₀).nodePorts 1).Exec initial stage (HistoryNodePorts.phaseCost 1))
    (_moved:∀ x,OutsideNode u node x→stage x=initial x)
    (_countsFit:r+max s e≤V) (_rows:8*((left).rows+(right).rows)≤V)
    (_maps:(r*(e*k+s)+s*(r+(r+r)))+(r*(h₀+(e*d+e*d))+e*(r*d+(r*d+r*d)))≤V)
    (_hidden:(left).bits+(right).bits≤V) (_tags:∀ i,tag₀ i<2^W)
    (_rootFit:(ws).stage.rootWidth v<2^W)
    (_room:ElectedRoom («W»:=W) (B:=height) («r»:=r) (ar:=arity B)
      tile₀ good letter (arityFit).1 (arityFit).2 (J).party node live t quota check payload)
    (plan:HistoryGatherExecution.Plan W)
    (_copied:(HistoryGatherBody.procedure W J).Exec (eout t quota check payload)
      (HistoryGatherExecution.output J plan (eout t quota check payload)) (HistoryGatherExecution.tariff W J plan))
    (_pinWords:∀ j:Fin (r*(e*k)+(r*h₀+e*(r*d))),
      HistoryGatherExecution.output J plan (eout t quota check payload) (HistoryPartyPair.atPair (J).party node 2+j.val)=
      (BitLayout.sourceAddress (wire j):Word W))
    (_widths:∀ side j,j<HistoryGatherExecution.cap J side→plan.width side j≤V)
    (_mapBase:plan.gatherBase=HistoryPartyPair.atPair (J).party node 2) (_size:plan.gatherCount≤V)
    (_mapCost:HistoryGatherExecution.tariff W J plan≤partyMapRate (kernelTemplate (refreshGrid B)) rec₀*(1+r)),
    ∃ post ticks,q.Emitted (rom:=rom) (height:=height) (initial:=initial) B words y post ticks := by
  classical
  obtain ⟨levelValue,levelBound⟩ := selectedLevel
  change levelValue = siteHeight r d at heightEq
  subst levelValue
  let levelUsed : Fin (height+1) := ⟨siteHeight r d,levelBound⟩
  intro check payload _saved _bounds _baseNodes _age _nr _high _mode _nonempty _cap _mask _lut _step _pages _pageStep _counts
    _lutAway _countsAway _header _ports _small T _id _nodes _cache _seen _pref _moved _countsFit _rows _maps _hidden _tags _rootFit
    _room plan _copied _pinWords _widths _mapBase _size _mapCost
  let bounded:=And.intro _bounds.header _bounds.controls
  have retained (x:ℕ) (lo:q.cursor.heap≤x) := img.archive x (_bounds.header.trans lo)
  have inc:=q.incidence_at_entry (mem := initial) (final := final) (saved := _saved)
    (bounds := bounded) (retained := retained) fam hk y b _baseNodes img.row img.cursor _mask
  obtain ⟨immutable,loc⟩:=q.incidence_geometry y _age (_high.trans _bounds.header) _bounds.controls.1 _nr
  have first:=inc.keep_outside fam node winner loc _moved
  have locJ:=PartyWindow.of_layout arc fam 0 (winner).val _age _nonempty (winner).isLt _cap
  have after:=elected_room_outside tile₀ good letter (arityFit).1 (arityFit).2 (J).party node live levelUsed quota check payload
    _room locJ _countsFit _rows _maps
  have access:=physical_roster_frame arc fam node winner tag₀ stage (eout levelUsed quota check payload) plan first immutable loc
    _age _nr _nonempty _cap _mask _lut _step _pages _pageStep _counts _lutAway _countsAway _header _ports _widths _mapBase _size after
  have late:=fun x (hx:OutsideNode u node x)=>((access (fam).parties le_rfl).2 x hx).trans (_moved x hx)
  have vb : 1024 ≤ V := by
    change (2:ℕ)^10 ≤ 2^(u^10)
    exact Nat.pow_le_pow_right (by decide : 0 < 2)
      ((show 10 ≤ u by omega).trans (Nat.le_self_pow (by decide : 10 ≠ 0) u))
  have hstart:=q.kernel_header_protected arc fam y _saved bounded retained b _baseNodes img.row img.cursor _age _nr
    (_high.trans _bounds.header) hk _mode _nonempty _cap _mask _small _moved
  have hclose:=q.kernel_header_protected arc fam y _saved bounded retained b _baseNodes img.row img.cursor _age _nr
    (_high.trans _bounds.header) hk _mode _nonempty _cap _mask _small late
  have prev:=roster_prefix_words tile₀ good letter (arityFit).1 (arityFit).2 arc fam node winner 1 initial levelUsed quota check payload
    plan _mode inc immutable loc _age _nr _nonempty _cap _mask _lut _step _pages _pageStep _counts _lutAway _countsAway
    (by omega) _header _ports _widths _mapBase _size _room _countsFit _rows _maps
  have portsGuard:=q.kernel_arity_guard arc fam y words _saved bounded retained b _baseNodes img.row img.cursor _age _nr
    (_high.trans _bounds.header) _small T _id _nodes _cache _seen late prev
  have op:=elected_arm tile₀ good letter (arityFit).1 (arityFit).2 (J).party node live levelUsed quota check payload _room
  let endInput:=entryOf A₀ node winner tag₀ stage (eout levelUsed quota check payload)
    (HistoryGatherExecution.output J plan (eout levelUsed quota check payload)) (fam).parties
  have gate:4*(pair left right).compile.cells≤V:=by
    rw [Tree.compiled_rows];change 4*((left).rows+(right).rows)≤V;omega
  have pinCount:r*(e*k)+(r*h₀+e*(r*d))≤V:=by
    simp only [Nat.mul_add] at _maps ⊢;omega
  have wide:=TickWorkspace.word_space (u:=u) (i:=18) (by omega)
    (by change 18<V^4;have h:=Nat.le_self_pow (by decide : 4≠0) V;omega)
  have sz:10*V≤TickWorkspace.stride u:=by
    change 10*V≤V^4
    calc 10*V≤V*V:=Nat.mul_le_mul_right _ (by omega)
         _=V^2:=by ring
         _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have roomPrivate:(C₀).privateStarts+9<2^W:=by
    change TickWorkspace.base u 18+4*V+9<2^W
    omega
  have cellRoom : 2+V+V≤2^W := by omega
  have tagBound:=HistoryCompiledRows.metadata_fits («W»:=W) tag₀ (pair left right).compile
    (by
      rw [Tree.compiled_bits, Tree.pair_bits]
      exact (Nat.add_le_add (Nat.add_le_add_left pinCount 2) _hidden).trans cellRoom)
    _tags
  let emitted:=q.issued_tree words y
  have length:=congrArg Sigma.fst emitted
  obtain ⟨run,table,summary,keep⟩:=physical_kernel_run arc fam winner left right wire tag₀ 1 initial stage
    (eout levelUsed quota check payload) plan _mode first immutable loc _age _nr _nonempty _cap _mask _lut _step _pages _pageStep _counts _lutAway
    _countsAway _header _ports _widths _mapBase _size after _moved (HistoryNodePorts.phaseCost 1) (eticks levelUsed quota check payload)
    _pref roomPrivate hstart.1 op.1 op.2.2 op.2.1 _copied _pinWords pinCount gate (by omega) tagBound
    ((congrArg (fun n : ℕ => n < 2^W) length).mp _rootFit)
    (portsGuard.1.trans (congrArg (fun n : ℕ => (n : Word W)) length)) portsGuard.2 hclose.2
  have opCost:=elected_pair_tariff tile₀ good letter (arityFit).1 (arityFit).2 (J).party node live levelUsed quota check payload _room
  have rowMem:rec₀∈(refreshGrid B).rows:=(issued_party_rom B img.resident q.tile supported q.hh q.rowSum
    q.sym q.conn ix role).1
  have rate:=refresh_block_ticks B (refreshGrid B) rec₀ (by simp [grids]) rowMem A₀ ⟨rfl,rfl,rfl,rfl,rfl⟩
    node winner left right wire tag₀ stage (eout levelUsed quota check payload) (HistoryGatherExecution.output J plan (eout levelUsed quota check payload))
    endInput r (eticks levelUsed quota check payload) (HistoryGatherExecution.tariff W J plan) opCost _mapCost
  obtain ⟨loaded,reported⟩:=transport_compiled emitted table summary
  refine ⟨_,_,run,loaded,reported,keep,?_⟩
  · have eq:=congrArg (fun tree:Σ a,Tree F a=>tree.2.resources) emitted
    rw [eq];exact rate

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression Computability.VPVNP.MotifSelector LinearAlgebra.SpectralBooks
open RAM HistoryContraction RAM.HistoryGatherBody RAM.HistoryGatherExecution RAM.HistoryStageBody.Physical
open RAM.HistoryRefreshEmitter RAM.HistoryStageSetup RAM.NavigationNodeRows
open PhysicalStage NavigationDirectory CompressorPacking Native RefreshDemandRows RefreshStageNav RefreshTies
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {u K heads height rom : ℕ} {cur ctr : Word (16*u^10)}
  (q : RefreshReceipt F K cur) (B : Block F) {Pins : Type} (words : q.input.Words Pins)
  (y : (q.move.next q.term).Site)
local notation "W" => 16*u^10
local notation "V" => RAM.HistoryStageBody.Physical.volume u
local notation "m" => 2^q.s
local notation "deg" => 1+q.h+q.pad
local notation "P" => CursorSpace.recordPointers q.entry
local notation "node" => q.step.sites.id y
local notation "pt" => (q.kernelSite y).1.2
local notation "z" => q.chosenBlock y
local notation "G" => refreshBinaryGraph q.input
local notation "port₀" => (tagOrdinal q.s).symm
local notation "w₀" => refreshBinaryInput q.input
local notation "i₀" => q.tile.winner G port₀ w₀ z
local notation "issuedRecord" => issuedParty q.tile q.hh q.rowSum q.sym q.conn i₀ pt
local notation "s₀" => (q.issuedHeader y).arity
local notation "r" => refreshBinaryCopies q.tile q.input z
local notation "k" => (refreshBinaryEntry q.tile q.input z).bits
local notation "d" => (refreshBinaryEntry q.tile q.input z).bitCap
local notation "e" => 2*q.h
local notation "mapLen" => r*(e*k)+(r*s₀+e*(r*d))
local notation "iso₀" => StageAddress.refreshInputIso q.input.graph q.input.chart (splitWord q.s q.rem) port₀ q.input.width
local notation "old" => (iso₀).pushWord words
local notation "st" => (refreshBinary q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn).next q.branch
local notation "fresh" => (st).halfWords Pins
local notation "child" => (iso₀).site.symm (z,pt)
local notation "args" => WordLayout.argSize old fresh (@id ((q.input.Base×BitWord q.rem)×Fin m)) (fun _=>1) RefreshTies.singleChild (z,pt)
local notation "fam" => refreshFamily B rom height
local notation "grid" => refreshGrid B
local notation "A" => layout u (archive B rom height K) fam
local notation "J" => rawArm A (pt).val

set_option maxRecDepth 24000 in
set_option maxHeartbeats 4600000 in
/-- Run the positive refresh gather on the elected pair's memory. The first
four-word result supplies its map length. The predecessor and successor
half tables identify every written address with the chosen tree's wire. -/
theorem recorded_gather {final post : Memory W} (b : Banks)
    (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (limits : heads≤q.cursor.heap ∧ q.entry.next.heap≤cur.val ∧ cur.val<ctr.val)
    (img : PartyImage (heads:=heads) q B height rom b y final post)
    (headerFrame : ∀i,q.cursor.header ≤ i→i<q.entry.next.header→i<q.entry.next.heap→post i=final i)
    (arrays : OldArrayBounds heads q.cursor q.input) (ord : q.input.OrderedHalves words)
    (baseNodes : b.nodes=TickWorkspace.base u 44) (pairs : TickWorkspace.base u 19≤b.charges)
    {safe : ℕ→Prop} (safeRegion : ∀i,safe i→(i<TickWorkspace.base u 17 ∨ TickWorkspace.base u 18 ≤ i) ∧ i<2^W)
    (oldRows : State.HalfRows q.old safe (fun i=>(post i).val))
    (newRows : State.HalfRows q.step.sites safe (fun i=>(post i).val))
    (childRow : DirectoryRow b q.old.layer (q.old.ord child) post)
    (age : 16≤u) (nr : node<V^2) (cr : q.old.id child<V^2)
    (capacity : ((fam).motifs+2)*((fam).parties+2)*8*32≤V)
    (mask : 2^(fam).parties<2^W)
    (headersHigh : TickWorkspace.base u 19≤q.cursor.header) (headsHigh : TickWorkspace.base u 19≤heads)
    (romHigh : TickWorkspace.base u 19≤rom) (romFit : rom+libraryWords B height<2^W)
    (tileFit : q.tile.last+1≤2^W) (histFit : (P).counts+(q.chosenIndex y).val*K<2^W)
    (headerBound : 3+5*(fam).demands+4*(fam).supplies≤V)
    (sizeBound : mapLen≤V) (kindFits : ∀i:Fin 7,((issuedRecord).kind (arity B)).words i<2^W)
    (portFits : ∀i:Fin (grid).stride,(issuedRecord).port.at (grid).demand (grid).supply i.val<2^W)
    (stageBound : 3*m<2^W) (laneBound : 2^q.rem<2^W) (degreeBound : q.h<2^W)
    (halfLimit : (P).halves+(Fintype.card q.input.Base*m*2^q.rem)*(2*deg)*4≤2^W)
    (oldWidth : q.input.maxWidth≤V) (newWidth : (st).maxWidth≤V)
    (oldDegree : m≤V) (newDegree : deg≤V) (scalar : 2+mapLen+k+e+s₀+e*k+r*(e*k)+r*s₀+r*d<2^W)
    (info : post (HistoryPartyPair.atPair (J).party node 1+1)=(mapLen:Word W))
    (starts : post (J).nodePorts.starts=0)
    (last : post ((J).nodePorts.starts+1)=((old).ports.halfBits (z,pt):Word W)) :
    ∃plan : Plan W,(procedure W J).Exec post (output J plan post) (HistoryGatherExecution.tariff W J plan) ∧
      (∀j : Fin mapLen,output J plan post (HistoryPartyPair.atPair (J).party node 2+j.val)=
        (BitLayout.sourceAddress (q.issuedWire words y j):Word W)) ∧
      (∀side j,j<cap J side→plan.width side j≤V) ∧
      plan.gatherBase=HistoryPartyPair.atPair (J).party node 2 ∧ plan.gatherCount≤V ∧
      HistoryGatherExecution.tariff W J plan≤partyMapRate (kernelTemplate grid) issuedRecord*(1+r) ∧
      HistoryGatherExecution.tariff W J plan≤gridMapRate grid*(1+r) := by
  let issued:=issued_party_rom B img.resident q.tile supported q.hh q.rowSum q.sym q.conn i₀ pt
  have parties : (fam).parties=m:=issued.2.1
  let winner : Fin (fam).parties:=Fin.cast parties.symm pt
  have view (i) (range:q.cursor.header ≤ i ∧ i<q.entry.next.header ∨ heads ≤ i) (h:i<q.entry.next.heap) :
      post i=final i:=range.elim (fun h₀=>headerFrame i h₀.1 h₀.2 h) (fun lo=>img.archive i lo h)
  let keep:=fun i lo hi=>img.archive i (limits.1.trans lo) hi
  have read:=q.incidence_at_entry saved limits keep fam parties y b baseNodes img.row img.cursor mask
  have room:=(q.incidence_geometry y age (headsHigh.trans limits.1) limits.2.1 nr).1
  have mode : (J).mode=.refresh m q.h q.pad:=by
    let geometry : StaticMotif F→HistoryGatherBody.Geometry:=fun
      | .shrink .. => .refresh 0 0 0
      | .refresh s h pad .. => .refresh (2^s) h pad
    exact (congrArg geometry (B.public_refresh supported)).symm
  have two : 4≤2^W:=by
    have h₀ : 1≤u^10:=Nat.one_le_pow _ _ (by omega)
    exact Nat.pow_le_pow_right (by decide:0<2) (show 2≤W by omega)
  let raw:=read.root_fields (archive B rom height K) fam winner room (by omega)
  have enabled : partyActive J post:=(gather_occupied A post winner winner raw.2.2.2.1 raw.2.2.2.2 mask (by omega)).mpr rfl
  let S:=q.gather_space y B supported saved limits keep parties read room age nr capacity headersHigh headsHigh
    romHigh romFit tileFit histFit headerBound mapLen sizeBound
  have big : 128≤V:=Nat.pow_le_pow_right (by decide:0<2)
    ((show 7≤u by omega).trans (Nat.le_self_pow (by decide) _))
  have nb:=HistoryShrinkEmitter.directory_address_space (u:=u) age big nr
  have cb:=HistoryShrinkEmitter.directory_address_space (u:=u) age big cr
  have fitDir : b.nodes+8*node+6<2^W:=by rw [baseNodes];omega
  have fitChild : b.nodes+8*q.old.id child+6<2^W:=by rw [baseNodes];omega
  have dBank : b.nodes<2^W:=by omega
  have stop:=S.portsBeforeControl
  have nodesAfter : portsEnd J≤b.nodes:=by rw [baseNodes];have sep:=TickWorkspace.apart (u:=u) (by decide:18<44);omega
  have moneyAfter : portsEnd J≤b.charges:=by have sep:=TickWorkspace.apart (u:=u) (by decide:18<19);omega
  have startLo : portsEnd J≤(J).nodePorts.starts:=by change _≤TickWorkspace.base u 18+3*V;omega
  have startRoom : (J).nodePorts.starts+1<2^W:=by
    have end18:=TickWorkspace.word_space (u:=u) (i:=18) (by omega) (by change 18<V^4;nlinarith)
    have h:V≤V^2:=Nat.le_self_pow (by decide) _
    change TickWorkspace.base u 18+3*V+1<_
    change TickWorkspace.base u 18+V^4<_ at end18
    have twice : 3*V+1≤V^2:=by nlinarith
    have powers : V^2≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
    omega
  have argFits:=q.gather_arg_room y words ord age oldDegree newDegree oldWidth newWidth
  have widthRoom : (old).ports.halfBits (z,pt)<2^W:=by
    have eq : WordLayout.prior old (@id ((q.input.Base×BitWord q.rem)×Fin m)) (fun _=>1)
        RefreshTies.singleChild (z,pt)=(old).ports.halfBits (z,pt):=by simp [WordLayout.prior,RefreshTies.singleChild]
    have size : args = (old).ports.halfBits (z,pt) + (fresh).ports.halfBits (z,pt) :=
      congrArg (fun n : ℕ => n + (fresh).ports.halfBits (z,pt)) eq
    have bound : 2 + ((old).ports.halfBits (z,pt) + (fresh).ports.halfBits (z,pt)) ≤ 2^W :=
      (Nat.add_le_add_left size.symm.le 2).trans argFits
    omega
  have mapWord : post (HistoryPartyPair.atPair (J).party node 1+1) = ((mapLen : ℕ) : Word W) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using info
  have count:=map_size_from_pair J node mapLen raw.1 enabled S.pairCountFit mapWord (by omega)
  let call:=q.emit_gather saved limits view y J mode rfl (by omega)
    ((congrArg Fin.val raw.2.1).trans (Fin.val_cast_of_lt (by have:=room.kernel;omega)))
    ((congrArg Fin.val raw.2.2.1).trans (Fin.val_cast_of_lt (by have:=room.incident;omega)))
    arrays tileFit histFit old fresh B img.resident supported rfl rfl rfl rfl rfl parties enabled
    S.kindRoom S.pageRoom kindFits portFits stageBound laneBound degreeBound two halfLimit
  apply call S.portWindow _ S.positive S.resident headerBound oldWidth newWidth count S.mapRoom S.range S.pairInfo
    S.keep S.clear S.headAddress scalar (fun _ _=>S.pinRoom argFits _) (fun _ _=>S.pinRoom argFits _)
    node S.mapBase sizeBound rfl
  intro side j bit scratch _ _ frame
  exact q.gather_cells_from_input saved limits view y J words ord J b S.portWindow baseNodes.symm raw.1
    (fun i h=>(safeRegion i h).2) (fun i h=>(safeRegion i h).1.imp id (fun hi=>stop.trans hi))
    oldRows newRows childRow img.row nodesAfter moneyAfter startLo (by omega) fitDir fitChild dBank startRoom
    starts widthRoom last side j bit scratch frame

set_option maxRecDepth 24000 in
set_option maxHeartbeats 3000000 in
/-- Read both historical half tables and the predecessor directory at node
entry, then carry their cells through the elected pair's actual write frame. -/
theorem recorded_gather_at_entry {final entry post : Memory W} (b : Banks)
    (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (saved : SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (limits : heads≤q.cursor.heap ∧ q.entry.next.heap≤cur.val ∧ cur.val<ctr.val)
    (img : PartyImage (heads:=heads) q B height rom b y final post)
    (kept : ∀i,OutsideNode u node i→post i=entry i)
    (headerFrame : ∀i,q.cursor.header ≤ i→i<q.entry.next.header→i<q.entry.next.heap→entry i=final i)
    (arrays : OldArrayBounds heads q.cursor q.input) (ord : q.input.OrderedHalves words)
    (baseNodes : b.nodes=TickWorkspace.base u 44) (pairs : TickWorkspace.base u 19≤b.charges)
    {safe : ℕ→Prop} (safeRegion : ∀i,safe i→(i<TickWorkspace.base u 12 ∨ TickWorkspace.base u 19 ≤ i) ∧ i<2^W)
    (oldRows : State.HalfRows q.old safe (fun i=>(entry i).val))
    (newRows : State.HalfRows q.step.sites safe (fun i=>(entry i).val))
    (childRow : DirectoryRow b q.old.layer (q.old.ord child) entry)
    (age : 16≤u) (nr : node<V^2) (cr : q.old.id child<V^2)
    (capacity : ((fam).motifs+2)*((fam).parties+2)*8*32≤V)
    (mask : 2^(fam).parties<2^W)
    (headersHigh : TickWorkspace.base u 19≤q.cursor.header) (headsHigh : TickWorkspace.base u 19≤heads)
    (romHigh : TickWorkspace.base u 19≤rom) (romFit : rom+libraryWords B height<2^W)
    (tileFit : q.tile.last+1≤2^W) (histFit : (P).counts+(q.chosenIndex y).val*K<2^W)
    (headerBound : 3+5*(fam).demands+4*(fam).supplies≤V)
    (sizeBound : mapLen≤V) (kindFits : ∀i:Fin 7,((issuedRecord).kind (arity B)).words i<2^W)
    (portFits : ∀i:Fin (grid).stride,(issuedRecord).port.at (grid).demand (grid).supply i.val<2^W)
    (stageBound : 3*m<2^W) (laneBound : 2^q.rem<2^W) (degreeBound : q.h<2^W)
    (halfLimit : (P).halves+(Fintype.card q.input.Base*m*2^q.rem)*(2*deg)*4≤2^W)
    (oldWidth : q.input.maxWidth≤V) (newWidth : (st).maxWidth≤V)
    (oldDegree : m≤V) (newDegree : deg≤V) (scalar : 2+mapLen+k+e+s₀+e*k+r*(e*k)+r*s₀+r*d<2^W)
    (info : post (HistoryPartyPair.atPair (J).party node 1+1)=(mapLen:Word W))
    (starts : post (J).nodePorts.starts=0)
    (last : post ((J).nodePorts.starts+1)=((old).ports.halfBits (z,pt):Word W)) :
    ∃plan : Plan W,(procedure W J).Exec post (output J plan post) (HistoryGatherExecution.tariff W J plan) ∧
      (∀j : Fin mapLen,output J plan post (HistoryPartyPair.atPair (J).party node 2+j.val)=
        (BitLayout.sourceAddress (q.issuedWire words y j):Word W)) ∧
      (∀side j,j<cap J side→plan.width side j≤V) ∧
      plan.gatherBase=HistoryPartyPair.atPair (J).party node 2 ∧ plan.gatherCount≤V ∧
      HistoryGatherExecution.tariff W J plan≤partyMapRate (kernelTemplate grid) issuedRecord*(1+r) ∧
      HistoryGatherExecution.tariff W J plan≤gridMapRate grid*(1+r) := by
  have high (i : ℕ) (hi : TickWorkspace.base u 19 ≤ i) : post i=entry i :=
    kept i (outside_of_region node age nr (.inr (.inl hi)))
  have savedHeader (i) (lo:q.cursor.header ≤ i) (hi:i<q.entry.next.header) (hi':i<q.entry.next.heap) :
      post i=final i := (high i (headersHigh.trans lo)).trans (headerFrame i lo hi hi')
  have frame (i : ℕ) (hi : safe i) : (post i).val=(entry i).val :=
    congrArg Fin.val (kept i (outside_of_region node age nr ((safeRegion i hi).1.imp id (fun h=>.inl h))))
  have dpos:=TickWorkspace.apart (u:=u) (by decide:19<44)
  have pred:=childRow.retain (now:=post) (fun j _=>high _ (by rw [baseNodes];omega)) (high _ (by omega))
  have s12:=TickWorkspace.apart (u:=u) (by decide:12<17)
  have s19:=TickWorkspace.apart (u:=u) (by decide:18<19)
  have narrow (i) (hi:safe i) : (i<TickWorkspace.base u 17 ∨ TickWorkspace.base u 18 ≤ i) ∧ i<2^W:=
    ⟨(safeRegion i hi).1.imp (fun _=>by omega) (fun _=>by omega),(safeRegion i hi).2⟩
  exact q.recorded_gather B words y b supported saved limits img savedHeader arrays ord baseNodes pairs
    narrow (oldRows.transfer frame (fun _ h=>h)) (newRows.transfer frame (fun _ h=>h)) pred age nr cr capacity
    mask headersHigh headsHigh romHigh romFit tileFit histFit headerBound sizeBound kindFits portFits stageBound
    laneBound degreeBound halfLimit oldWidth newWidth oldDegree newDegree scalar info starts last

end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

namespace ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression Computability.VPVNP.MotifSelector LinearAlgebra.SpectralBooks
open RAM HistoryContraction RAM.HistoryGatherBody RAM.HistoryGatherExecution RAM.HistoryStageBody.Physical
open RAM.HistoryPartyBatchExec RAM.HistoryMotifJoin RAM.HistoryRefreshEmitter RAM.HistoryStageSetup RAM.NavigationNodeRows
open PhysicalStage NavigationDirectory CompressorPacking Native RefreshDemandRows RefreshStageNav RefreshTies
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] [Fintype F] {u K heads height rom : ℕ} {cur ctr : Word (16*u^10)}
  (q : RefreshReceipt F K cur) (B : Block F) {Pins : Type} (words : q.input.Words Pins)
  (y : (q.move.next q.term).Site)
local notation "W" => 16*u^10
local notation "V" => RAM.HistoryStageBody.Physical.volume u
local notation "m" => 2^q.s
local notation "deg" => 1+q.h+q.pad
local notation "P" => CursorSpace.recordPointers q.entry
local notation "node" => q.step.sites.id y
local notation "pt" => (q.kernelSite y).1.2
local notation "z" => q.chosenBlock y
local notation "G" => refreshBinaryGraph q.input
local notation "port₀" => (tagOrdinal q.s).symm
local notation "w₀" => refreshBinaryInput q.input
local notation "i₀" => q.tile.winner G port₀ w₀ z
local notation "issuedRecord" => issuedParty q.tile q.hh q.rowSum q.sym q.conn i₀ pt
local notation "s₀" => (q.issuedHeader y).arity
local notation "r" => refreshBinaryCopies q.tile q.input z
local notation "k" => (refreshBinaryEntry q.tile q.input z).bits
local notation "d" => (refreshBinaryEntry q.tile q.input z).bitCap
local notation "e" => 2*q.h
local notation "mapLen" => r*(e*k)+(r*s₀+e*(r*d))
local notation "iso₀" => StageAddress.refreshInputIso q.input.graph q.input.chart (splitWord q.s q.rem) port₀ q.input.width
local notation "old" => (iso₀).pushWord words
local notation "st" => (refreshBinary q.tile q.input q.hm q.hh q.sym q.rowSum q.noLoop q.conn).next q.branch
local notation "fresh" => (st).halfWords Pins
local notation "child" => (iso₀).site.symm (z,pt)
local notation "args" => WordLayout.argSize old fresh (@id ((q.input.Base×BitWord q.rem)×Fin m)) (fun _=>1) RefreshTies.singleChild (z,pt)
local notation "fam" => refreshFamily B rom height
local notation "grid" => refreshGrid B
local notation "A" => layout u (archive B rom height K) fam
local notation "J" => rawArm A (pt).val


local notation "arc" => archive B rom height K
local notation "target" => Move.WordStep.targetSite (R:=q.move) (i:=q.term) y
local notation "step" => q.wordStep words
local notation "nextWords" => ((q.move.target_eq q.term).symm ▸ (step).words.ports : PortLayout _ Pins)
local notation "alpha" => Fintype.card (refreshBinaryEntry q.tile q.input z).Alphabet
local notation "tk" => HistogramTileNetwork.siteHeight r d
variable (b:Banks) {final initial:Memory (16*u^10)}
  (img:PartyImage (heads:=heads) q B height rom b y final initial)

private theorem page_values_fit {n eCount limit : ℕ} (page : HistoryPortCatalogue.Page n eCount)
    (zeroFit : 0 < limit) (rowsFit : n < limit) (colsFit : eCount < limit)
    (anchorFit : page.anchor < limit) (demandFit : ∀ j, page.demand j < limit)
    (supplyFit : ∀ j, page.supply j < limit) (widthFit : ∀ j, page.baseWidth j < limit)
    (D E index : ℕ) : page.at D E index < limit := by
  have demandDigit (j : Fin page.digits) := (page.decode j).1.isLt.trans rowsFit
  have widthDigit (j : Fin page.digits) := (page.decode j).2.isLt.trans (widthFit _)
  unfold HistoryPortCatalogue.Page.at
  split
  · exact rowsFit
  split
  · exact colsFit
  split
  · exact anchorFit
  split
  · try dsimp only
    split
    · split
      · exact demandFit _
      · exact widthFit _
    · exact zeroFit
  split
  · split
    · exact supplyFit _
    · exact zeroFit
  · try dsimp only
    split
    · try dsimp only
      split
      · exact demandDigit _
      · exact widthDigit _
    · exact zeroFit

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
omit [Fintype F] in
/-- Every word of the selected refresh catalogue row fits, including either
coordinate of a decoded digit and all unused positions of the mounted page. -/
theorem issued_port_fits (placed : issuedRecord∈(grid).rows) (age : 16≤u)
    (headers : 3+5*(grid).demand+4*(grid).supply≤RAM.HistoryStageBody.Physical.volume u)
    (arity : (issuedRecord).header≤RAM.HistoryStageBody.Physical.volume u) :
    ∀i:Fin (grid).stride,(issuedRecord).port.at (grid).demand (grid).supply i.val<2^W := by
  let pg : HistoryPortCatalogue.Page (4*m) (2*q.h):=(issuedRecord).port
  have vv : RAM.HistoryStageBody.Physical.volume u<2^W := by
    have hp : 0 < u^10 := Nat.pow_pos (by omega : 0 < u)
    change 2^(u^10)<2^(16*u^10)
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have caps:=(grid).caps placed
  have dn : 4*m<2^W:=by have n:4*m≤(grid).demand:=caps.1;omega
  have sn : 2*q.h<2^W:=by have n:2*q.h≤(grid).supply:=caps.2.1;omega
  have aFit : pg.anchor<2^W:=by
    have anchor : pg.anchor<2*q.h:=by change (_:Fin (2*q.h)).val<_;exact Fin.isLt _
    exact anchor.trans sn
  have dFit (j:Fin (4*m)) : pg.demand j<2^W:=j.isLt.trans dn
  have sFit (j:Fin (2*q.h)) : pg.supply j<2^W:=j.isLt.trans sn
  have sum : (∑j,pg.baseWidth j)≤(issuedRecord).header:=by
    change (∑j,pg.baseWidth j)≤(q.tile.block i₀).bits+(∑j,pg.baseWidth j)
    omega
  have wFit (j:Fin (4*m)) : pg.baseWidth j<2^W :=
    (Finset.single_le_sum (fun i _=>Nat.zero_le (pg.baseWidth i)) (Finset.mem_univ j)).trans_lt
      (sum.trans_lt (arity.trans_lt vv))
  intro i
  exact page_values_fit pg (Nat.two_pow_pos _) dn sn aFit dFit sFit wFit _ _ i.val

omit [Fintype F] in
/-- Restoring the initial dyadic degree bounds the actual successor by the
last degree in the fixed refresh family. -/
private theorem restored_degree (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (oldDegree : m≤V) : deg≤V:=by
  let returns : StaticMotif F→Prop:=fun
    | .refresh s h pad .. => 1+h+pad≤2^s
    | .shrink .. => True
  have fixed : returns (.refresh (B.exponent B.levels) B.h B.pad B.graph _ B.refresh):=by
    change 1+B.h+B.pad≤2^B.exponent B.levels
    rw [B.restore]
    exact (increasing_ports B).monotone (Nat.zero_le B.levels)
  exact (((congrArg returns (B.public_refresh supported)).mpr fixed) : deg≤ m).trans oldDegree

omit [Fintype F] in
/-- Every incident-width sum of the recorded successor is representable,
including after transport through the program's target-degree equality. -/
theorem issued_incident_fits (supported : B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (age : 16≤u) (oldDegree : m≤V) (newWidth : (st).maxWidth≤V)
    (a : (q.move.next q.term).Site) : (q.move.next q.term).incidentWidth a<2^W:=by
  have newDegree:=q.restored_degree B supported oldDegree
  have volumes:16≤V:=age.trans ((Nat.le_self_pow (by decide:10≠0) u).trans Nat.lt_two_pow_self.le)
  have wSpace:V^3<2^W:=by
    have top:=TickWorkspace.word_space (u:=u) (i:=0) (by omega) (by change 0<V^4;positivity)
    have le:V^3≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
    change TickWorkspace.base u 0+V^4<2^W at top
    omega
  have transported {i l D D' L : ℕ} {state : State i l} (eqn:D=D') (R : Move F state D L) (j : Fin R.rules.count) :
      ((Program.recastMove eqn R).next (Program.degreeTerm eqn R j)).maxWidth=(R.next j).maxWidth:=by cases eqn;rfl
  have scale : (q.move.next q.term).maxWidth≤V:=(transported q.degreeEq _ q.branch).trans_le newWidth
  have small (a) : (q.move.next q.term).incidentWidth a<2^W:=by
    have degree : q.degree≤V:=q.degreeEq ▸ newDegree
    have h:=(q.move.next q.term).incidentWidth_le a
    have b:=Nat.mul_le_mul (Nat.mul_le_mul_left 2 degree) scale
    have scale2:2*V*V≤V^3:=by
      calc 2*V*V=2*(V*V):=by ring
           _≤V*(V*V):=Nat.mul_le_mul_right _ (by omega)
           _=V^3:=by ring
    exact h.trans_lt (b.trans_lt (scale2.trans_lt wSpace))
  exact small a

include img in
set_option maxRecDepth 24000 in
set_option maxHeartbeats 5500000 in
/-- Execute the refresh of this exact chronological node from a resident S44
directory and its parent half tables, and publish the issued word step. All
machine executions, the arithmetic registers, the positive/idle party
choices and the intermediate cache preservation are constructed here. -/
theorem emit_recorded_refresh
    (supported:B.publicTemplate (.refresh q.s q.h q.pad q.mult q.gridConstant q.tile))
    (saved:SavedFrame cur ctr heads q.entry.next.header q.entry.next.heap q.out final)
    (bounds:RefreshBounds heads q.cursor.heap q.entry.next.heap q.cursor.dense cur.val ctr.val)
    (headerFrame:∀i,q.cursor.header ≤ i→i<q.entry.next.header→i<q.entry.next.heap→initial i=final i)
    (arrays:OldArrayBounds heads q.cursor q.input) (ord:q.input.OrderedHalves words)
    (baseNodes:b.nodes=TickWorkspace.base u 44) (pairs:TickWorkspace.base u 19≤b.charges)
    (headsHigh:TickWorkspace.base u 19≤heads) (headersHigh:TickWorkspace.base u 19≤q.cursor.header)
    (romHigh:TickWorkspace.base u 19≤rom) (romFit:rom+libraryWords B height<2^W)
    (age:16≤u) (intrinsic:blockPageRate B≤u) (nr:node<V^2) (cr:q.old.id child<V^2)
    (current:numeric initial (TickWorkspace.base u 18)=node+1)
    (read:q.step.data.Reads (numeric initial))
    (cells:q.step.data.Footprint (fun i=>TickWorkspace.base u 19 ≤ i ∧ i<2^W) (numeric initial))
    (children:∀ j:Fin q.step.sites.layer.childCount,q.step.data.child (q.step.sites.ord y) j<V^2)
    {safe:ℕ→Prop} (safeRegion:∀ i,safe i→(i<TickWorkspace.base u 12 ∨ TickWorkspace.base u 19 ≤ i) ∧ i<2^W)
    (oldRows:State.HalfRows q.old safe (numeric initial))
    (newRows:State.HalfRows q.step.sites safe (numeric initial))
    (oldDirectory:DirectoryRow b q.old.layer (q.old.ord child) initial)
    (T:HistoryStageRoot.Input) (id:T.id=node) (nodes:T.nodeBase=b.nodes) (cache:T.resultBase=TickWorkspace.base u 13)
    (seen:HistoryStageRoot.Ports words.ports nextWords (step).stage.count (step).stage.child target T (numeric initial))
    (selectedHeight:tk≤height) (price:ℕ) (copies:r≤price)
    (margin:gridPageRate (arity B) (refreshGrid B)*((price+1)*(W+1)^3)≤V)
    (oldWidth:q.input.maxWidth≤V) (newWidth:(st).maxWidth≤V) :
    ∃ post ticks,q.Emitted (rom:=rom) (height:=height) (initial:=initial) B words y post ticks := by
  classical
  let lib:=q.issued_layout B rom height supported age intrinsic romHigh romFit
  have positive:0<(fam).motifs:=by rw [lib.motifs];decide
  have initialized:=q.initialize_kernel B b y img saved bounds supported baseNodes pairs age nr romHigh headsHigh
    positive lib.cap lib.mask lib.lut lib.step lib.pages lib.pageStep lib.counts (.inr lib.lutAway) (.inr lib.countsAway)
    lib.header lib.portEnd current read cells children
  obtain ⟨prefixMem,moved,stageImage,activeImage⟩:=initialized
  let t:Fin (height+1):=⟨tk,by omega⟩
  have pages:=q.elected_pages B y t b activeImage supported price copies rfl margin
  obtain ⟨c,p,room,_,_,_,info,_,postImage,_⟩:=q.recorded_elected_arm B y t b activeImage supported saved bounds
    baseNodes pairs age nr lib.cap lib.mask lib.gradeFit headsHigh romHigh romFit rfl pages.width pages.work
    pages.kindSmall pages.pairRows pages.pairPins pages.commands pages.pairBits lib.tags
  have bounded:=And.intro bounds.header bounds.controls
  let win:=Fin.cast lib.parties.symm pt
  have retained (x : ℕ) (lo : q.cursor.heap ≤ x) := img.archive x (bounds.header.trans lo)
  have inc := q.incidence_at_entry (mem := initial) (final := final) (saved := saved)
    (bounds := bounded) (retained := retained) fam lib.parties y b baseNodes img.row img.cursor lib.mask
  obtain ⟨immutable,loc⟩:=q.incidence_geometry y age (headsHigh.trans bounds.header) bounds.controls.1 nr
  have component:r+max alpha e≤V:=by have n:=pages.commands;change 23*(r+max alpha e)≤V at n;omega
  have large:128≤V:=Nat.pow_le_pow_right (by decide:0<2)
    ((show 7≤u by omega).trans (Nat.le_self_pow (by decide) _))
  let fit:=q.issued_arity y B supported img.resident
  have stable:=elected_prefix_frame (q.issuedTile y) (q.issuedGood y) (q.issuedLetter y) fit.1 fit.2 arc fam
    node win 1 initial t (q.issuedQuota y) c p inc immutable loc age nr positive lib.cap lib.mask lib.lut lib.step
    lib.pages lib.pageStep lib.counts (.inr lib.lutAway) (.inr lib.countsAway) (by omega) lib.header lib.portEnd
    room component pages.pairRows pages.pairPins
  have kept:=stable.2
  have «meta»:=q.elected_prefix arc fam y words T id (nodes.trans baseNodes) cache (by omega) seen stable.1
  have vb:10*V≤TickWorkspace.stride u:=by
    change 10*V≤V^4
    calc 10*V≤V*V:=Nat.mul_le_mul_right _ (by omega)
         _=V^2:=by ring
         _≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have wide:=TickWorkspace.word_space (u:=u) (i:=18) (by omega) (by omega)
  have oldDegree:m≤V:=by
    have cap:=lib.cap
    rw [lib.parties,lib.motifs] at cap
    omega
  have newDegree:=q.restored_degree B supported oldDegree
  have sizeBound:mapLen≤V:=by
    have total:=pages.pairPins
    change (r*(e*k+alpha)+alpha*(r+(r+r)))+
      (r*(s₀+(e*d+e*d))+e*(r*d+(r*d+r*d)))≤V at total
    change r*(e*k)+(r*s₀+e*(r*d))≤V
    simp only [Nat.mul_add] at total ⊢;omega
  let static:=q.gather_static_bounds y bounds.controls.1
  have eSmall:e≤V:=pages.kindSmall 0
  have kSmall:k≤V:=pages.kindSmall 2
  have arSmall:s₀≤V:=pages.kindSmall 3
  have ePos:0<e:=by have:=q.hh;omega
  have rDigit:r*d≤ mapLen:=(Nat.le_mul_of_pos_left _ ePos).trans (by omega)
  have square:e*k≤V^2:=by simpa only [pow_two] using Nat.mul_le_mul eSmall kSmall
  have volumes:16≤V:=age.trans ((Nat.le_self_pow (by decide:10≠0) u).trans Nat.lt_two_pow_self.le)
  have cube:V^2+9*V+2≤V^3:=by
    calc V^2+9*V+2≤2*V^2:=by nlinarith
         _≤V*V^2:=Nat.mul_le_mul_right _ (by omega)
         _=V^3:=by ring
  have wSpace:V^3<2^W:=by
    have le:V^3≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
    change TickWorkspace.base u 18+V^4<2^W at wide;omega
  have scalar:2+mapLen+k+e+s₀+e*k+r*(e*k)+r*s₀+r*d<2^W:=by
    have h : r*(e*k)+r*s₀≤ mapLen :=
      Nat.add_le_add_left (Nat.le_add_right (r*s₀) (e*(r*d))) (r*(e*k))
    omega
  have small:=q.issued_incident_fits B supported age oldDegree newWidth
  have member:=(issued_party_rom B img.resident q.tile supported q.hh q.rowSum q.sym q.conn i₀ pt).1
  have portFits:=q.issued_port_fits B y member age lib.header arSmall
  obtain ⟨plan,gathered,values,widths,base,size,rate,_⟩:=q.recorded_gather_at_entry B words y b supported saved
    bounded postImage kept headerFrame arrays ord baseNodes pairs safeRegion oldRows newRows oldDirectory age nr cr
    lib.cap lib.mask headersHigh headsHigh romHigh romFit lib.gradeFit static.histFit lib.header sizeBound
    (fun a=>(pages.kindSmall a).trans_lt (by omega)) portFits static.stageBound static.laneBound static.degreeBound static.halfLimit oldWidth
    newWidth oldDegree newDegree scalar (by
      have stored := info (⟨1,by decide⟩ : Fin 4)
      change _ = ((mapLen : ℕ) : Word W) at stored
      simpa only [Fin.val_mk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using stored) «meta».1 «meta».2
  have rootWidth:(step).stage.rootWidth target<2^W:=by
    have width:=congrArg Sigma.fst (q.issued_tree words y)
    have bound:=q.gather_arg_room y words ord age oldDegree newDegree oldWidth newWidth
    change 2+args≤2^W at bound
    change (step).stage.rootWidth target=args at width
    omega
  exact q.finish_kernel B words y b img supported t rfl saved bounds baseNodes age nr headsHigh lib.mode
    positive lib.cap lib.mask lib.lut lib.step lib.pages lib.pageStep lib.counts (.inr lib.lutAway) (.inr lib.countsAway)
    lib.header lib.portEnd small T id nodes cache seen prefixMem moved component pages.pairRows pages.pairPins pages.pairBits
    (fun g=>((Fintype.equivFin ((Fin 3→Bool)→F)) g).isLt.trans_le lib.tags) rootWidth room plan gathered values
    widths base size rate


end
end ThreeFlat.Diagonal.NavigationPass.RefreshReceipt

end OAI
