import OAI.ThreeFlat.RAM.HistoryMotifTariffCosts

namespace OAI
/-! # Physical captures for selected shrink parties -/

set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryShrinkEmitter

open Computability.VPVNP.BurstRAM PrivateRAM LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open Diagonal Diagonal.HistogramTileNetwork Diagonal.MotifOuterTerms Diagonal.MotifBinaryPacking
open Diagonal.MotifOrderedCells Diagonal.MotifSelectorChecks Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree
open HistoryStageBody.Physical HistoryRefreshEmitter HistoryGatherExecution HistoryGatherBody
open HistoryPartyBatchExec HistoryPartySpecialization BitLayout
open private padded_width_zero from OAI.ThreeFlat.RAM.HistoryGatherExecution
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F J E S : Type} [Field F] [Fintype F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
    {n e r h p u levels ar : ℕ} (A : HistoryGatherBody.Layout) (node : ℕ)
    (D : PortGraph J E) (G : Supply J S) (j : J) (base live : E→ℕ)
    (tile : FixedMotifTile D (ports G) base F)
    (dp : Fin n ≃ D.Port j) (sp : Fin e ≃ (ports G).Port j) (di : Fin n→ℕ) (si : Fin e→ℕ)
    (v : Histogram tile.Alphabet r) (old : (a : D.Port j)→Fin (live a.1.1)→BitSource h p)
    (fresh : (a : (ports G).Port j)→Fin (histWidth tile.output v a.1.1+r*tile.bits)→BitSource h p)
open private admittedTileHeader gatherMapBase from OAI.ThreeFlat.RAM.HistoryGatherExecution
open private liveCheckJobs from OAI.ThreeFlat.RAM.HistoryRefreshElectedJobs
local notation "W" => 16*u^10
local notation "V" => volume u
local instance : Nonempty tile.Alphabet:=tile.hasLetter
local notation "H" => admittedTileHeader D G j base tile dp
local notation "role" => Party.ofTile D G j base tile dp sp di si
local notation "s" => Fintype.card tile.Alphabet
local notation "tape" => HistogramTileNetwork.tile (d:=tile.bitCap) D G j base H sp tile.output
  (fun a q=>tile.output_le_cap a _) tile.entry
local notation "valid" => headerGood G j sp (H).code
local notation "symbol" => headerLetter G j sp (Fintype.equivFin tile.Alphabet) (H).code
local notation "quota" => numberHistogram (Fintype.equivFin tile.Alphabet) v
variable (tp : (admittedTileHeader D G j base tile dp).arity+(e*tile.bitCap+e*tile.bitCap)≤ar)
    (cp : e*tile.bits+Fintype.card tile.Alphabet≤ar)
    (input : Memory (16*u^10)) (t : Fin (levels+1))
local notation "X" => electedBatch tape valid symbol tp cp A.party input true
local notation "L" => admission valid symbol (MotifNativeCompactors.partialInput F r t.val) quota
local notation "R" => tiled tape (MotifNativeCompactors.partialInput F (r*tile.bitCap) t.val)
private abbrev tariffCheckRead : Prop :=
  HistoryPartySpecialization.Reads (X).regs (numeric (X).bootImage) (HistoryStaticArchive.all F ar) r t
variable (readC : tariffCheckRead (r:=r) (u:=u) A D G j base tile dp sp tp cp input t)
local notation "jobsC" => liveCheckJobs tape valid symbol tp cp A.party input t quota readC
local notation "Y" => electedBatch tape valid symbol tp cp A.party ((X).published jobsC) false
private abbrev tariffPayloadRead : Prop :=
  HistoryPartySpecialization.Reads (Y).regs (numeric (Y).bootImage) (HistoryStaticArchive.all F ar) r t
variable (readP : tariffPayloadRead (u:=u) A D G j base tile dp sp v tp cp input t readC)
local notation "paired" => electedOutput tape valid symbol tp cp A.party node input t quota readC readP
local notation "ticks" => electedCost tape valid symbol tp cp A.party input t quota readC readP
local notation "size" => r*(e*tile.bits)+(r*(H).arity+e*(r*tile.bitCap))
local notation "route" => partyPointer (d:=tile.bitCap) D G j base live H sp tile.output v old fresh
local notation "payload" => gatheredWord («W»:=W) (gatherMapBase A paired)
      (fun i=>sourceAddress (route i))
local notation "plan" => nativePlan A paired
      (typedSources («W»:=W) A D G j base live H sp tile.output v old fresh) payload

private theorem indexed_amount_le_sum {m : ℕ} (f : Fin m → ℕ) (i : Fin m) :
    f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i)

/-- For an issued party, its pair allocations bound both padded width loops
and every scalar or digit used in the source-index routine. -/
theorem gathered_party_limits (mem : Memory W) (page : ℕ)
    (loaded : ReadPage A mem role ar page) (age : 16≤u)
    {t rows priv : ℕ} (paid : PartyPageCaps V ar role r t rows priv)
    (dw : ∀ i : Fin n,(physicalWidth A mem false i.val).val=live (dp i).1.1)
    (sw : ∀ i : Fin e,(physicalWidth A mem true i.val).val=histWidth tile.output v (sp i).1.1+r*tile.bits)
    (copies : ∀ i : Fin n,live (dp i).1.1≤base (dp i).1.1*r) :
    size≤V ∧ (∀side i,i<cap A side→(physicalWidth A mem side i).val≤V) ∧
      (∀i:Fin n,base (dp i).1.1*r≤2^W) ∧
      2+size+tile.bits+e+(H).arity+e*tile.bits+r*(e*tile.bits)+r*(H).arity+r*tile.bitCap<2^W := by
  have pins : (r*(e*tile.bits+s)+s*(r+(r+r)))+
      (r*((H).arity+(e*tile.bitCap+e*tile.bitCap))+e*(r*tile.bitCap+(r*tile.bitCap+r*tile.bitCap)))≤V := paid.pairPins
  have sz : size≤V := by simp only [Nat.mul_add] at pins;omega
  have bounded (q : Bool) (k : ℕ) (inside : k<cap A q) : (physicalWidth A mem q k).val≤V := by
    cases q with
    | false=>
      by_cases present:k<n
      · let i : Fin n:=⟨k,present⟩
        have own := indexed_amount_le_sum (fun a : Fin n => base (dp a).1.1) i
        have word : base (dp i).1.1≤(H).arity := own.trans (Nat.le_add_left _ _)
        rw [dw i]
        exact ((copies i).trans ((Nat.mul_le_mul_right r word).trans_eq (Nat.mul_comm _ _))).trans
          ((by omega : r*(H).arity ≤ size).trans sz)
      · rw [padded_width_zero A mem D G j base tile dp sp di si ar page loaded false k inside (by simpa using Nat.le_of_not_gt present)]
        omega
    | true=>
      by_cases present:k<e
      · let i : Fin e:=⟨k,present⟩
        have a:=FixedMotifMaxWidth.histWidth_le tile.output v (sp i).1.1 tile.bitCap (fun l=>tile.output_le_cap l _)
        have digits : r*tile.bitCap≤e*(r*tile.bitCap):=Nat.le_mul_of_pos_left _ (by omega)
        have selector : r*tile.bits≤r*(e*tile.bits):=Nat.mul_le_mul_left r (Nat.le_mul_of_pos_left _ (by omega))
        rw [sw i]
        omega
      · rw [padded_width_zero A mem D G j base tile dp sp di si ar page loaded true k inside (by simpa using Nat.le_of_not_gt present)]
        omega
  have rs : r≤V := by have h:=paid.commands;omega
  have arity : (H).arity≤V := paid.kindSmall 3
  refine ⟨sz,bounded,?_,gather_scalar_room age _ _ _ _ _ _ sz (paid.kindSmall 2)
    (paid.kindSmall 0) arity rs (paid.kindSmall 4)⟩
  intro i
  have one := indexed_amount_le_sum (fun k : Fin n => base (dp k).1.1) i
  exact gather_digit_room age _ _ ((one.trans (Nat.le_add_left _ _)).trans arity) rs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2300000 in
/-- An occupied row of the actual shrink roster, using the output of
`emit_recorded_party`. Its paired-memory frame covers all three native
batches, and its port bounds include the zero-filled tail of the ROM row. -/
theorem real_recorded_arm (ref : HistoryGatherBody.Layout) (mode : A.mode=ref.mode)
    (dem : A.demandCap=ref.demandCap) (sup : A.supplyCap=ref.supplyCap)
    (room : ElectedRoom tape valid symbol tp cp A.party node input t quota readC readP)
    (loc : PartyWindow u A.party)
    (count : 23*(r+max s e)≤V) (gates : 8*((L).rows+(R).rows)≤V)
    (pins : (r*(e*tile.bits+s)+s*(r+(r+r)))+
      (r*((H).arity+(e*tile.bitCap+e*tile.bitCap))+e*(r*tile.bitCap+(r*tile.bitCap+r*tile.bitCap)))≤V)
    (page : ℕ) (loaded : ReadPage A paired role ar page) (dn : n≤A.demandCap) (sn : e≤A.supplyCap)
    (dw : ∀ i : Fin n,(physicalWidth A paired false i.val).val=live (dp i).1.1)
    (sw : ∀ i : Fin e,(physicalWidth A paired true i.val).val=histWidth tile.output v (sp i).1.1+r*tile.bits)
    (copies : ∀ i : Fin n,live (dp i).1.1≤base (dp i).1.1*r)
    (length : (partyMapCount A paired).val=size)
    (atNode : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) paired (fun _=>0)=(node:Word W))
    (fits : HistoryPartyPair.atPair A.party node 2<2^W)
    (emitted : Elected node tag A plan input paired ticks (pair L R).compile route) :
    ∃ z : ArmWrite W, ArmWrite.Real u node tag A (pair L R).compile route input z ∧
      z.ticks+tariff W A z.plan ≤ partyRate role*(W+1)^3*(1+r)+partyMapRate ref role*(1+r) := by
  have sz : size≤V:=by
    simp only [Nat.mul_add] at pins
    omega
  have bounded (q : Bool) (k : ℕ) (inside : k<cap A q) : (plan).width q k≤A.party.V := by
    change (physicalWidth A paired q k).val≤A.party.V
    rw [loc.volume]
    cases q with
    | false=>
      by_cases present:k<n
      · let i : Fin n:=⟨k,present⟩
        have own := indexed_amount_le_sum (fun a : Fin n => base (dp a).1.1) i
        have word : base (dp i).1.1 ≤ (H).arity := own.trans (Nat.le_add_left _ _)
        have digitLimit : base (dp i).1.1*r ≤ r*(H).arity :=
          (Nat.mul_le_mul_right r word).trans_eq (Nat.mul_comm _ _)
        have within : r*(H).arity ≤ size := by omega
        exact (dw i).le.trans ((copies i).trans (digitLimit.trans (within.trans sz)))
      · rw [padded_width_zero A paired D G j base tile dp sp di si ar page loaded false k inside (by simpa using Nat.le_of_not_gt present)]
        omega
    | true=>
      by_cases present:k<e
      · let i : Fin e:=⟨k,present⟩
        have a:=FixedMotifMaxWidth.histWidth_le tile.output v (sp i).1.1 tile.bitCap (fun l=>tile.output_le_cap l _)
        have digits : r*tile.bitCap≤e*(r*tile.bitCap):=Nat.le_mul_of_pos_left _ (by omega)
        have selector : r*tile.bits≤r*(e*tile.bits):=Nat.mul_le_mul_left r (Nat.le_mul_of_pos_left _ (by omega))
        have within : histWidth tile.output v (sp i).1.1 + r*tile.bits ≤ size := by omega
        exact (sw i).le.trans (within.trans sz)
      · rw [padded_width_zero A paired D G j base tile dp sp di si ar page loaded true k inside (by simpa using Nat.le_of_not_gt present)]
        omega
  let write : ArmWrite W:=⟨paired,plan,ticks⟩
  refine ⟨write,⟨emitted,bounded,private_map_base A node paired atNode fits,?_,?_⟩,?_⟩
  · change (partyMapCount A paired).val≤A.party.V
    rw [length,loc.volume]
    exact sz
  · exact elected_room_away tape valid symbol tp cp A.party node input t quota readC readP room loc
      (by omega) gates pins
  · exact Nat.add_le_add (elected_pair_tariff tape valid symbol tp cp A.party node input t quota readC readP room)
      (tile_partyMapRate A paired payload D G j base live tile dp sp di si v old fresh
        ref mode dem sup ar page loaded dn sn dw sw copies length)


set_option maxRecDepth 20000 in
set_option maxHeartbeats 2600000 in
/-- A positive party in the chronological shrink roster. All page, width and
copy facts come from `emit_recorded_party` at the same issued memory. -/
theorem CapturedArm.paid (page : ℕ)
    (issued : CapturedArm role page ar r (fun i=>live (dp i).1.1) (fun i=>base (dp i).1.1)
      (fun i=>histWidth tile.output v (sp i).1.1+r*tile.bits) size tag A node plan input paired ticks
      (pair L R).compile route (ElectedRoom tape valid symbol tp cp A.party node input t quota readC readP))
    (ref : HistoryGatherBody.Layout) (mode : A.mode=ref.mode) (dem : A.demandCap=ref.demandCap)
    (sup : A.supplyCap=ref.supplyCap) (loc : PartyWindow u A.party)
    (count : 23*(r+max s e)≤V) (gates : 8*((L).rows+(R).rows)≤V)
    (pins : (r*(e*tile.bits+s)+s*(r+(r+r)))+
      (r*((H).arity+(e*tile.bitCap+e*tile.bitCap))+e*(r*tile.bitCap+(r*tile.bitCap+r*tile.bitCap)))≤V) :
    ∃ z : ArmWrite W, ArmWrite.Real u node tag A (pair L R).compile route input z ∧
      z.ticks+tariff W A z.plan≤partyRate role*(W+1)^3*(1+r)+partyMapRate ref role*(1+r) :=
  real_recorded_arm A node D G j base live tile dp sp di si v old fresh tp cp input t readC readP
    ref mode dem sup issued.room loc count gates pins page issued.pageRead issued.demands issued.supplies
    issued.oldWords issued.freshWords issued.repetitions issued.mapCount issued.atNode issued.pairAddress issued.election


end
end ThreeFlat.RAM.HistoryShrinkEmitter

namespace ThreeFlat.RAM.HistoryShrinkEmitter
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal Diagonal.PhysicalStage Diagonal.TickWorkspace HistoryStageBody.Physical
open HistoryRefreshEmitter HistoryPartyBatch HistoryPartyBatchExec HistoryPartySpecialization
open scoped Classical Fin.CommRing
noncomputable section

set_option maxRecDepth 18000 in
set_option maxHeartbeats 2900000 in
/-- The elected seed for each of the actual two boots of the occupied shrink
party. The directory gives three archive intervals, and the finite ROM gives
all kind, compactor, counter and scalar-table intervals. -/
theorem RecordedBoot.seed {F : Type} [Field F] [Fintype F] (B : Block F)
    {u K start height n parties : ℕ} (G : Grid F) (cells : Fin n→Fin parties→Party F)
    (pre tail : List (Grid F)) (gridAt : grids B=pre++G::tail) (rowsAt : G.rows=HistoryStageBody.Physical.grid cells)
    (g : ℕ) (i : Fin n) (j : Fin parties) (ck : Bool) (mem : Memory (16*u^10)) (node r : ℕ)
    (t : Fin (height+1)) {letters : ℕ} (quot : Fin letters→ℕ) (inc counts : ℕ)
    (age : 16≤u) (nodeFit : node<(volume u)^2)
    (whole : archiveWindow u start (libraryWords B height)) :
    let fam:=G.family (Mounted.base B height start pre)
    let arc:=archive B start height K
    let A:=(rawParty (layout u arc fam) g j.val).party
    let k:=(cells i j).kind (arity B)
    let X : Build (16*u^10):=⟨A,ck,k,mem⟩
    RecordedBoot X (HistoryStaticArchive.all F (arity B)) r t quot inc
        (fam.kinds+7*(i.val*parties+j.val)) counts →
    fam.parties=parties → g<fam.motifs → (fam.motifs+2)*(fam.parties+2)*8*32≤volume u →
    numeric mem A.cursor-1=node →
    archiveWindow u (A.nodes+8*node) 8 → archiveWindow u (kernel A (numeric mem)) 5 →
    archiveWindow u inc 6 → archiveWindow u counts k.letters →
    r≤volume u → (∀a:Fin 7,k.words a≤volume u) →
    2^t.val≤volume u → StableCompactNativeBudget.budget t.val≤volume u → ElectedSeed u X := by
  intro fam arc A k X recorded hp rawMotif capacity cur nodeWindow kernelWindow incWindow countWindow
    small kindFits size work
  let party : Fin fam.parties:=Fin.cast hp.symm j
  have pages:=selected_archive_windows u B gridAt rowsAt i j whole
  have regs:=mounted_arch_registers u B whole
  let row:=fam.kinds+7*(i.val*parties+j.val)
  have gridWindow:archiveWindow u row 7:=pages.2.2.2.1
  have atCell {b l a : ℕ} (win : archiveWindow u b l) (lo:b≤a) (hi:a<b+l) :
      (a<base u 12 ∨ base u 18≤a) ∧ a<2^(16*u^10) := by
    rcases win with ⟨top,left|right⟩
    · exact ⟨.inl (by omega),by omega⟩
    · exact ⟨.inr (by omega),by omega⟩
  have high : 1024≤volume u:=Nat.pow_le_pow_right (by decide : 0<2)
    ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) u))
  have strideHigh : volume u ≤ TickWorkspace.stride u :=
    Nat.le_self_pow (by decide : 4 ≠ 0) (volume u)
  have cursorFit:base u 18<2^(16*u^10):=(Nat.le_add_right ..).trans_lt
    (word_space (u:=u) (i:=18) (by omega) (by omega))
  have probe (a : ℕ) (on : HistoryPartyBootExec.SeedRead A ck (numeric mem) a) :
      (a<base u 12 ∨ base u 18≤a) ∧ a<2^(16*u^10) := by
    cases on with
    | cursor=>exact ⟨.inr le_rfl,cursorFit⟩
    | node=>rw [cur];exact atCell nodeWindow (by omega) (by omega)
    | motifCount=>exact atCell kernelWindow (by omega) (by omega)
    | incidentPtr _=>exact atCell kernelWindow (by omega) (by omega)
    | partyMask _=>rw [recorded.record];exact atCell incWindow (by omega) (by omega)
    | kindIndex _=>rw [recorded.record];exact atCell incWindow (by omega) (by omega)
    | copyCount _=>rw [recorded.record];exact atCell incWindow (by omega) (by omega)
    | digitWidth _=>rw [recorded.table];exact atCell gridWindow (by omega) (by omega)
    | kindCount _=>
      rw [recorded.table];apply atCell gridWindow (by omega)
      cases ck <;> simp [Bool.toNat] <;> omega
  let tab:=if ck then k.selectorPage else k.tilePage
  have tabFit:tab<HistoryStaticArchive.count F (arity B):=by
    have inhabited : 0 < HistoryStaticArchive.count F (arity B) := by
      change 0 < Fintype.card (HistoryStaticArchive.Entry F (arity B))
      exact Fintype.card_pos_iff.mpr ⟨⟨0, fun _ => 0⟩⟩
    cases ck <;> dsimp [tab,k,Party.kind] <;> split <;> first | exact Fin.isLt _ | exact inhabited
  apply elected_seed_of_reads u arc fam node g party ck X (HistoryStaticArchive.all F (arity B)) t r
    rfl rfl age nodeFit rawMotif capacity cur recorded.active recorded.count recorded.kindAt recorded.read recorded.grid probe
  · change archiveWindow u (incident X.layout (numeric X.input)) 4
    rw [recorded.record]
    exact incWindow.sub le_rfl (by omega)
  · change archiveWindow u (shape X.layout (numeric X.input)) 7
    rw [recorded.table]
    exact gridWindow
  · exact pages.2.2.2.2.1 ⟨tab,tabFit⟩
  · exact (pages.2.2.2.2.2 t).1
  · change archiveWindow u (numeric X.input (incident X.layout (numeric X.input)+1)) X.kind.letters
    rw [recorded.histogram]
    exact countWindow
  · exact regs
  · exact (pages.2.2.2.2.2 t).2
  · exact small
  · exact kindFits
  · exact size
  · exact work
  · exact recorded.level


set_option maxRecDepth 18000 in
set_option maxHeartbeats 1600000 in
/-- Reconstruct either native boot from the issued incident and the directory
and catalogue words retained outside the current node. -/
theorem recorded_boot_after_frame {F : Type} [Field F] [Fintype F] (B : Block F)
    {u K start height n parties : ℕ} (G : Grid F) (cells : Fin n → Fin parties → Party F)
    (pre : List (Grid F)) (g : ℕ) (i : Fin n) (j : Fin parties) (ck : Bool)
    (initial m : Memory (16*u^10)) (node r : ℕ) (t : Fin (height+1))
    {letters : ℕ} (quota : Fin letters → ℕ) (inc counts : ℕ)
    (age : 16 ≤ u) (nr : node < (volume u)^2)
    (image : Mounted B height (16*u^10) start initial) (romHigh : base u 19 ≤ start)
    (whole : archiveWindow u start (libraryWords B height))
    (width : 2^t.val ≤ volume u) (work : StableCompactNativeBudget.budget t.val ≤ volume u)
    (same : ∀ x, OutsideNode u node x → m x = initial x) :
    let fam := G.family (Mounted.base B height start pre)
    let A := (rawParty (layout u (archive B start height K) fam) g j.val).party
    let k := (cells i j).kind (arity B)
    let row := fam.kinds+7*(i.val*parties+j.val)
    RecordedBoot (⟨A,true,k,initial⟩ : Build (16*u^10)) (HistoryStaticArchive.all F (arity B))
        r t quota inc row counts →
    (base u 19 ≤ kernel A (numeric initial) ∧ base u 19 ≤ inc ∧ base u 19 ≤ counts) →
    kernel A (numeric m) = kernel A (numeric initial) → A.seed+37 < 2^(16*u^10) →
    RecordedBoot (⟨A,ck,k,m⟩ : Build (16*u^10)) (HistoryStaticArchive.all F (arity B))
        r t quota inc row counts := by
  intro fam A k row issued above ker seedRoom
  obtain ⟨kernelHigh,incHigh,countsHigh⟩ := above
  let raw := numeric m
  let prior := numeric initial
  have kept (x : ℕ) (high : base u 19 ≤ x) : raw x = prior x :=
    congrArg Fin.val (same x (outside_of_region node age nr (.inr (.inl high))))
  have priorIncident : incident A prior = inc := issued.record
  have ir : incident A raw = inc := by
    change raw (kernel A raw+4)+6*A.motif = inc
    rw [show kernel A raw = kernel A prior from ker,
        kept (kernel A prior+4) (kernelHigh.trans (Nat.le_add_right ..))]
    exact priorIncident
  have incidentWord (off : ℕ) : raw (incident A raw+off) = prior (incident A prior+off) := by
    rw [ir,priorIncident]
    exact kept (inc+off) (incHigh.trans (Nat.le_add_right ..))
  have kernelCount : raw (kernel A raw+3) = prior (kernel A prior+3) := by
    rw [show kernel A raw = kernel A prior from ker]
    exact kept (kernel A prior+3) (kernelHigh.trans (Nat.le_add_right ..))
  have live : occupied A raw := by
    unfold occupied
    rw [kernelCount,incidentWord 5]
    exact issued.active
  have priorRow : shape A prior = row := issued.table
  have grid : shape A raw = row := by
    change A.kinds+7*(raw (incident A raw+2)*A.parties+A.party) = row
    rw [incidentWord 2]
    exact priorRow
  have rowHigh : base u 19 ≤ row := by
    change base u 19 ≤ start+StableCompactROMNative.size height+staticSize B+
      HistoryCompactorCounts.size height+(pre.map Grid.size).sum+7*(i.val*parties+j.val)
    omega
  have kind (a : Fin 7) : raw (shape A raw+a.val) = k.words a := by
    rw [grid,kept (row+a.val) (rowHigh.trans (Nat.le_add_right ..)),←priorRow]
    exact issued.kindAt a
  have amount : raw (incident A raw+3) = r := (incidentWord 3).trans issued.count
  have hread : raw (incident A raw+1) = counts := (incidentWord 1).trans issued.histogram
  have hcounts (a : Fin letters) : raw (counts+a.val) = quota a :=
    (kept (counts+a.val) (countsHigh.trans (Nat.le_add_right ..))).trans (issued.inputQuota a)
  have im := mounted_kept node B image age nr (.inr romHigh) same
  have lutRegs := mounted_arch_registers u B whole
  have big : 1024 ≤ volume u := Nat.pow_le_pow_right (by decide : 0 < 2)
    ((show 10 ≤ u by omega).trans (Nat.le_self_pow (by decide : 10 ≠ 0) u))
  have square : (volume u)^2 ≤ (volume u)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have extra : volume u+37 ≤ (volume u)^4 := by
    have twice := Nat.mul_le_mul_left (volume u) (show 2 ≤ volume u by omega)
    rw [← pow_two] at twice
    omega
  have sep : A.seed+37 ≤ base u 19 := by
    change base u 14+volume u+37 ≤ base u 19
    have dis := TickWorkspace.apart (u:=u) (by decide : 14 < 19)
    change base u 14+(volume u)^4 ≤ base u 19 at dis
    omega
  have word : volume u < 2^(16*u^10) := by
    have le := Nat.le_self_pow (by decide : 4 ≠ 0) (volume u)
    have space := TickWorkspace.word_space (u:=u) (i:=0) (by omega)
      (by change 0 < (volume u)^4; exact pow_pos (by omega) _)
    change base u 0+(volume u)^4 < 2^(16*u^10) at space
    omega
  have incFree : A.seed+37 ≤ incident A raw := by rw [ir]; exact sep.trans incHigh
  have kindFree : A.seed+37 ≤ shape A raw := by rw [grid]; exact sep.trans rowHigh
  have lutFree : A.seed+37 ≤ A.lutBase := by
    apply sep.trans
    change base u 19 ≤ start+StableCompactROMNative.size height
    omega
  have countFree : A.seed+37 ≤ A.countBase := by
    apply sep.trans
    change base u 19 ≤ start+StableCompactROMNative.size height+staticSize B
    omega
  have data := elected_reads A k m ck (HistoryStaticArchive.all F (arity B)) r k.digit t live amount
    (kind 4) issued.level (width.trans_lt word) seedRoom rfl lutRegs.2.1.le kind
    (stored_scalar B im.words) (stored_counts B im.words)
    (fun a => (compactor_counts_le F t a).trans_lt (work.trans_lt word))
    (.inr incFree) (.inr kindFree) (.inr lutFree) (.inr countFree)
  have bootQuota := elected_histogram A k m ck live seedRoom counts letters quota hread hcounts
    (.inr incFree) (.inr (sep.trans countsHigh))
  exact ⟨data.1,data.2,bootQuota,live,amount,kind,ir,grid,hread,hcounts,issued.level⟩

section PairBoots
open HistoryBoundedJoin HistoryPartyTapeRun Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms
open Diagonal.MotifSelectorChecks Diagonal.HistogramTileNetwork Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree

section PairResult
variable {F : Type} [Field F] [Fintype F] {Hidden : Type}
    {u r s e k b d height arity : ℕ}
    (tile : Tile F Hidden e d b) (good : (Fin (e*k) → Bool) → Prop)
    (letter : (Fin (e*k) → Bool) → Fin s)
    (tp : b+(e*d+e*d) ≤ arity) (sp : e*k+s ≤ arity)
    (A : HistoryPartyBatch.Layout) (node : ℕ) (input : Memory (16*u^10))
    (t : Fin (height+1)) (hist : Histogram (Fin s) r)

/-- The payload witness is quantified in the precise family required by the two-boot room. -/
private def issuedPairResult : Prop :=
  let room := ElectedRoom tile good letter tp sp A node input t hist
  let output := electedOutput tile good letter tp sp A node input t hist
  ∃ c p, room c p ∧ (∀ x, OutsideNode u node x → output c p x = input x) ∧
    ∀ x, PartyAway u A node x → output c p x = input x

private theorem issuedPairResult_of_room
    (loc : PartyWindow u A) (count : r+max s e ≤ volume u)
    (rows : 8*((admission good letter (MotifNativeCompactors.partialInput F r t.val) hist).rows +
      (tiled tile (MotifNativeCompactors.partialInput F (r*d) t.val)).rows) ≤ volume u)
    (pins : (r*(e*k+s)+s*(r+(r+r)))+(r*(b+(e*d+e*d))+e*(r*d+(r*d+r*d))) ≤ volume u) :
    ∀ {c p}, ElectedRoom tile good letter tp sp A node input t hist c p →
      issuedPairResult tile good letter tp sp A node input t hist := by
  intro c p paid
  exact ⟨c, p, paid, elected_room_outside tile good letter tp sp A node input t hist c p paid loc count rows pins,
    elected_room_away tile good letter tp sp A node input t hist c p paid loc count rows pins⟩
end PairResult

variable {F : Type} [Field F] [Fintype F] (B : Block F)
    {u K start height n parties s e k b d r : ℕ} {Hidden : Type}
    (G : Grid F) (cells : Fin n→Fin parties→Party F) (pre tail : List (Grid F))
    (gridAt : grids B=pre++G::tail) (rowsAt : G.rows=HistoryStageBody.Physical.grid cells)
    (g : ℕ) (i : Fin n) (j : Fin parties)
local notation "ar" => arity B
local notation "W" => 16*u^10
local notation "V" => volume u
local notation "arc" => archive B start height K
local notation "fam" => G.family (Mounted.base B height start pre)
local notation "A₀" => (rawParty (layout u arc fam) g j.val).party
local notation "row₀" => (cells i j).kind ar
local notation "rowAddress" => (fam).kinds+7*(i.val*parties+j.val)
local notation "LUT" => HistoryStaticArchive.all F ar
variable (tile : Tile F Hidden e d b) (good : (Fin (e*k)→Bool)→Prop)
    (letter : (Fin (e*k)→Bool)→Fin s)
    (tp : b+(e*d+e*d) ≤ arity B) (sp : e*k+s ≤ arity B)
    (initial : Memory (16*u^10)) (node : ℕ) (t : Fin (height+1))
    (hist : Histogram (Fin s) r)
local notation "SC" => MotifNativeCompactors.partialInput F r t.val
local notation "PC" => MotifNativeCompactors.partialInput F (r*d) t.val
local notation "ch" => admission good letter SC hist
local notation "pa" => tiled tile PC
local notation "X" => electedBatch tile good letter tp sp A₀ initial true
local notation "steps" => components good letter SC hist
local notation "cRead" => HistoryPartySpecialization.Reads (X).regs (numeric (X).bootImage) LUT r t
open private liveCheckJobs from OAI.ThreeFlat.RAM.HistoryRefreshElectedJobs
local notation "dim" c:arg => checks_fields tile good letter tp sp (X).regs (numeric (X).bootImage) t c
local notation "jobs" c:arg => liveCheckJobs tile good letter tp sp A₀ initial t hist c
local notation "Y" c:arg => electedBatch tile good letter tp sp A₀ ((X).published (jobs c)) false

set_option maxHeartbeats 4500000 in
set_option maxRecDepth 20000 in
include gridAt rowsAt in
/-- Execute the two boots with the same issued row. The payload reader is
opened only on the output of the checks publisher, using its outside-node
frame. The committed pair preserves that same frame. -/
theorem recorded_pair_room (inc counts : ℕ)
    (sameKind : row₀=HistoryPartySpecialization.kind tile good letter tp sp)
    (image : Mounted B height W start initial) (romHigh : base u 19 ≤ start)
    (whole : archiveWindow u start (libraryWords B height))
    (hp:(fam).parties=parties) (rowLive:g<(fam).motifs)
    (age:16≤u) (nr:node<V^2) (cap:((fam).motifs+2)*((fam).parties+2)*8*32≤V)
    (mask:2^(fam).parties<2^W) (atNode:numeric initial (A₀).cursor-1=node)
    (nodeWin:archiveWindow u ((A₀).nodes+8*node) 8) (kw:archiveWindow u (kernel A₀ (numeric initial)) 5)
    (iw:archiveWindow u inc 6) (qw:archiveWindow u counts (row₀).letters)
    (above : base u 19≤kernel A₀ (numeric initial) ∧ base u 19≤ inc ∧ base u 19≤counts)
    (issued : RecordedBoot (⟨A₀,true,row₀,initial⟩:Build W) LUT r t (fun a:Fin s=>(hist.val a).val)
      inc rowAddress counts)
    (width:2^t.val≤V) (work:StableCompactNativeBudget.budget t.val≤V)
    (kindFit:∀a:Fin 7,(row₀).words a≤V) (rows:8*((ch).rows+(pa).rows)≤V)
    (pins:(r*(e*k+s)+s*(r+(r+r)))+(r*(b+(e*d+e*d))+e*(r*d+(r*d+r*d)))≤V)
    (count:23*(r+max s e)≤V) (hidden:(ch).bits+(pa).bits≤V)
    (tableTags:Fintype.card ((Fin 3→Bool)→F)≤2^W) :
    issuedPairResult (F:=F) (Hidden:=Hidden) (u:=u) (r:=r) (s:=s) (e:=e) (k:=k)
      (b:=b) (d:=d) (height:=height) (arity:=arity B)
      tile good letter tp sp A₀ node initial t hist := by
  classical
  let j₀ : Fin (fam).parties:=Fin.cast hp.symm j
  let frame (m:Memory W):=∀x,OutsideNode u node x→m x=initial x
  have win : PartyWindow u A₀ :=
    PartyWindow.of_layout arc fam g j.val age rowLive (by rw [hp];exact j.isLt) cap
  have cursorAt (m:Memory W) (same:frame m) : numeric m (A₀).cursor=numeric initial (A₀).cursor:=
    congrArg Fin.val (same _ (outside_of_region node age nr (.inr (.inr (.inl rfl)))))
  have kernelAt (m:Memory W) (same:frame m) : kernel A₀ (numeric m)=kernel A₀ (numeric initial):=by
      change numeric m ((A₀).nodes+8*(numeric m (A₀).cursor-1)+5)=_
      rw [cursorAt m same,atNode]
      have upper : base u 19≤(A₀).nodes+8*node+5:=by
        change base u 19≤base u 44+8*node+5
        have:=TickWorkspace.apart (u:=u) (by decide:19<44)
        omega
      change _=numeric initial ((A₀).nodes+8*(numeric initial (A₀).cursor-1)+5)
      rw [atNode]
      exact congrArg Fin.val (same _ (outside_of_region node age nr (.inr (.inl upper))))
  have readAt (side:Bool) (m:Memory W) (same:frame m) :
      RecordedBoot (⟨A₀,side,row₀,m⟩:Build W) LUT r t (fun a:Fin s=>(hist.val a).val) inc rowAddress counts :=
    recorded_boot_after_frame (K:=K) B G cells pre g i j side initial m node r t
      (fun a : Fin s => (hist.val a).val) inc counts age nr image romHigh whole width work same
      issued above (kernelAt m same) win.seed_room
  have seed (side:Bool) (m:Memory W) (same:frame m) :
      ElectedSeed u (electedBatch tile good letter tp sp A₀ m side) := by
    have cur:=cursorAt m same
    have here:=kernelAt m same
    have data:=readAt side m same
    have result:=RecordedBoot.seed (K:=K) B G cells pre tail gridAt rowsAt g i j side m node r t
      (fun a:Fin s=>(hist.val a).val) inc counts age nr whole data hp rowLive cap (by rw [cur,atNode]) nodeWin
      (by rw [here];exact kw) iw qw (by omega) kindFit width work
    simpa only [electedBatch,←sameKind] using result
  have idFrame : frame initial:=fun _ _=>rfl
  have c₀:=readAt true initial idFrame
  have c:cRead := by simpa only [electedBatch,←sameKind] using c₀.read
  have cseed:=seed true initial idFrame
  have dimC:=dim c
  have dims:=checks_dimensions tile good letter tp sp (X).regs (numeric (X).bootImage) t c hist
  have len:HistoryPartyTapeRun.batchRows (X).table=(ch).rows:=congrArg Info.factors
    (batch_info X _ (fun a=>(steps a).net) (fun a=>(steps a).wire) dimC.1 dimC.2.1 dims dimC.2.2.1 dimC.2.2.2.1)
  have checkRows : (X).table.r = r := dimC.1
  have quotaRows : (X).table.s = s := dimC.2.1
  have pinC:HistoryPartyTapeRun.batchPins (X).table=r*(e*k+s)+s*(r+(r+r)):=by
    have left : (X).table.left.arity = e*k+s :=
      congrArg Diagonal.HistoryContraction.Tree.BatchRows.Size.arity dimC.2.2.2.2.1
    have right : (X).table.right.arity = r+(r+r) :=
      congrArg Diagonal.HistoryContraction.Tree.BatchRows.Size.arity dimC.2.2.2.2.2
    rw [HistoryPartyTapeRun.batchPins, checkRows, quotaRows, left, right]
  have countC : (X).count ≤ V := by
    rw [←cseed.count, checkRows, quotaRows]
    exact (Nat.add_le_add_left (Nat.le_max_left s e) r).trans
      ((Nat.le_mul_of_pos_left _ (by decide : 0 < 23)).trans count)
  have dst:(X).table.stream=dest A₀ true node 0:=by change dest A₀ true (numeric initial (A₀).cursor-1) 0=_;rw [atNode]
  let reindex := Fin.cast (congrArg₂ Nat.add dimC.1 dimC.2.1)
  have mid:frame ((X).published (jobs c)):=fun x h =>
    (batch_outside_node X win h (fun a=>(steps (reindex a)).net) (fun a=>(steps (reindex a)).wire) tag
      atNode dst rfl countC (by omega) (by omega)).keeps win.seed_room
  have p₀:=readAt false _ mid
  have p:HistoryPartySpecialization.Reads (Y c).regs (numeric (Y c).bootImage) LUT r t:=by
    simpa only [electedBatch,←sameKind] using p₀.read
  have pseed:=seed false _ mid
  have pages:=selected_archive_windows u B gridAt rowsAt i j whole
  have lutWin:(arc).lut+staticSize B<2^W ∧ ((arc).lut+staticSize B≤base u 12 ∨ base u 19≤(arc).lut) :=
    ⟨pages.2.1.1,.inr (romHigh.trans (Nat.le_add_right ..))⟩
  have compWin:(arc).pages+StableCompactROMNative.size height<2^W ∧
      ((arc).pages+StableCompactROMNative.size height≤base u 12 ∨ base u 19≤(arc).pages):=⟨pages.1.1,.inr romHigh⟩
  have level:t.val=siteHeight r d:=by simpa only [sameKind,HistoryPartySpecialization.kind] using c₀.level
  have quota:∀a:Fin s,numeric (X).bootImage (numeric (X).bootImage ((X).regs.incident+1)+a.val)=(hist.val a).val:=by
    simpa only [electedBatch,←sameKind] using c₀.quota
  have eFit:e≤V:=by have h:=kindFit 0;rw [sameKind] at h;exact h
  have dFit:d≤V:=by have h:=kindFit 4;rw [sameKind] at h;exact h
  have big:1024≤V:=Nat.pow_le_pow_right (by decide:0<2) ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) u))
  have v2:V^2<2^W:=by
    have hh:=TickWorkspace.word_space (u:=u) (i:=0) (by omega) (by change 0<V^4;positivity)
    have small:V^2≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
    change base u 0+V^4<2^W at hh
    omega
  have vv:V≤V^2:=Nat.le_self_pow (by decide) V
  have bank:e*d<2^W:=by have h:=Nat.mul_le_mul eFit dFit;rw [←pow_two] at h;omega
  have stripe:r*d<2^W:=by have h:=Nat.mul_le_mul (by omega:r≤V) dFit;rw [←pow_two] at h;omega
  have room:=physical_elected_room tile good letter tp sp u arc fam g j₀ node initial t hist c p
    age nr rowLive cap mask atNode lutWin compWin (mounted_batch_archive B image) rfl rfl level
    (work.trans_lt (vv.trans_lt v2)) quota cseed pseed rows pins count hidden (fun a=>(Fintype.equivFin _ a).isLt.trans_le tableTags)
    bank stripe
  exact issuedPairResult_of_room (u:=u) tile good letter tp sp A₀ node initial t hist
    win (by omega) rows pins room

end PairBoots

section OccupiedShrink
open private colors_le from OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily
open private recordedRoleAt from OAI.ThreeFlat.RAM.HistoryShrinkBatchRecords
open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryGatherBody Diagonal.CompressorPacking Diagonal.CompressorPacking.PhysicalShrink
open Diagonal.CompressorPacking.Native Diagonal.CompressorPacking.Native.ShrinkStage Diagonal.RefreshDemandRows
open Diagonal.ShrinkStageNav Diagonal.NavigationDirectory Diagonal.NavigationPass Diagonal.HistogramTileNetwork
open Diagonal.MotifOuterTerms Diagonal.MotifOrderedCells Diagonal.MotifSelectorChecks

variable {F : Type} [Field F] [Fintype F] (B : Block F) (s D rem : ℕ) (hD : 0<D)
  (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "T₀" => B.shrink
local notation "M₀" => shrinkBinary T₀ s D rem hD small A
local notation "B₀" => shrinkRecordState s rem A
local notation "N₀" => Fintype.card (B₀).Base
local notation "P₀" => shrinkRecordPacking s rem A
local notation "d₀" => (2^s:ℕ)
local notation "hc₀" => colors_le s
local notation "S₀" => shrinkStage s D
local notation "t₀" => Diagonal.CompressorPacking.tagBits d₀
local notation "x₀" => Resident.dims S₀ N₀ t₀ rem
variable {u K : ℕ}
local notation "W" => 16*u^10
local notation "V" => volume u
variable (cur ctr : Word (16*u^10)) (before issued final post : Memory (16*u^10)) (c : Cursor)
    (branch : Fin (shrinkBinary B.shrink s D rem hD small A).rules.count)
local notation "issuedWords" => shrinkIssuedWords T₀ s D rem hD small A branch
local notation "lay₀" => ShrinkMotif.chooseWidths issuedWords
local notation "en₀" => allocate K c (.shrink x₀)
local notation "f₀" => DescriptorSpan.fields K c x₀ lay₀
variable (hdr : ℕ) (H : ShrinkOutput (K:=K) B.shrink s D rem hD small A cur before c branch issued)
    (saved : let x := Resident.dims (shrinkStage s D) (Fintype.card (shrinkRecordState s rem A).Base)
                         (Diagonal.CompressorPacking.tagBits (2^s)) rem
             let next := (allocate K c (.shrink x)).next
             SavedFrame cur ctr hdr next.header next.heap issued final)
    (site : Computability.VPVNP.Compression.Site (shrinkRecordState s rem A).Base
      (BitWord (Diagonal.CompressorPacking.tagBits (2^s))) (BitWord rem))
    (O : Incidents.SiteOrder (S:=shrinkStage s D) (shrinkRecordPacking s rem A)
      (shrinkRecordState s rem A).order
      (ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)) site (16*u^10))
    (slot : Fin (Incidents.siteKeys (S:=shrinkStage s D) (w:=16*u^10) (shrinkRecordPacking s rem A)
      (shrinkRecordState s rem A).order
      (ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch)) site).length)
local notation "m₀" => (O.equiv slot).val
local notation "prior" => shrinkRecordWidth s rem A
local notation "du" => PhysicalShrink.b P₀ prior (shrinkRecordCode s rem A) hc₀
local notation "bestIndex" => RefreshDemandRows.tileNumber (du m₀) ((T₀).base ∘ (T₀).row)
local notation "ordinal" => (shrinkRecordOrder s rem A m₀).val
local notation "baseRow" => f₀ 36+6*(Incidents.capacity S₀*Incidents.siteNumber (B₀).order site+slot.val)

variable {height start : ℕ} {pre tail : List (Grid F)} (level : Fin B.levels)
    (stage : grids B=pre++shrinkGrid B level::tail)
local notation "fam" => (shrinkGrid B level).family (Mounted.base B height start pre)
local notation "arc" => archive B start height K
variable (part : {j : Fin 6 // partySite (shrinkRecordPacking s rem A)
    (ShrinkMotif.chooseWidths (shrinkIssuedWords B.shrink s D rem hD small A branch))
    (O.equiv slot).val j=site})
local notation "arm" => rawParty (layout u arc fam) slot.val part.val.val
local notation "alpha" => (Fintype.equivFin (shrinkRecordTile T₀ s rem A m₀).Alphabet)
local notation "sym" => Fintype.card (shrinkRecordTile T₀ s rem A m₀).Alphabet
local notation "tileAt" => shrinkRecordTile T₀ s rem A m₀
local notation "copy" => shrinkRecordCopies T₀ s rem A m₀
local notation "reps" => shrinkIssuedBranch T₀ s D rem hD small A branch m₀
local notation "baseAt" => PhysicalShrink.widths T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀
local notation "dp" => (Fintype.equivFin (demandGraph.Port part.val)).symm
local notation "sp" => (Fintype.equivFin (supplyGraph.Port part.val)).symm
local notation "row₀" => (shrinkParty T₀ bestIndex part.val).kind (arity B)
local notation "kernel0" => f₀ 34+5*Incidents.siteNumber (B₀).order site
local notation "counts" => c.dense+ordinal*K

private theorem selectedIncidentWord {w : ℕ} (first capacity siteIndex slotIndex : ℕ) :
    (first : Word w) + 6*((capacity : Word w)*(siteIndex : Word w)+(slotIndex : Word w)) =
      ((first+6*(capacity*siteIndex+slotIndex) : ℕ) : Word w) := by
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]

set_option maxHeartbeats 4500000 in
set_option maxRecDepth 20000 in
/-- On this accepted shrink branch the checks boot, second boot and pair
use the minimizing tile, the issued histogram and the physical row address.
Numerical bounds refer to this one party. -/
abbrev selected_shrink_pair :=
  fun (oldCaps : ShrinkOldCaps s rem W) (baseFit : N₀≤2^W)
    (capFits : Incidents.capacity S₀<2^W) (offset : 0<c.width) (node : ℕ)
    (age : 16≤u) (nr : node<V^2) (hp:siteHeight copy (tileAt).bitCap≤height)
    (mounted:Mounted B height W start post) (whole:archiveWindow u start (libraryWords B height))
    (romHigh : TickWorkspace.base u 19 ≤ start) (curNode:numeric post (arm).party.cursor-1=node)
    (rowLive:slot.val<(fam).motifs) (capacity:((fam).motifs+2)*((fam).parties+2)*8*32≤V)
    (rawKernel:kernel (arm).party (numeric post)=kernel0)
    (natPtr:incident (arm).party (numeric post)=baseRow)
    (live:slot.val<numeric post (kernel (arm).party (numeric post)+3))
    (ptr:(selected arm post).incident=(baseRow:Word W))
    (apart:∀j:Fin 6,baseRow+j.val≠cur.val ∧ baseRow+j.val≠ctr.val ∧ hdr≤baseRow+j.val)
    (kept:∀j:Fin 6,post (baseRow+j.val)=final (baseRow+j.val))
    (dense:∀(i:Fin (shrinkBinaryFamily T₀ s D rem hD small A).motifs)
        (a:(shrinkBinaryFamily T₀ s D rem hD small A).alphabet i),
      let addr:=c.dense+i.val*K+(Fintype.equivFin _ a).val
      addr≠c.header+27 ∧ addr≠cur.val ∧ addr≠ctr.val ∧ hdr≤addr ∧ addr<(en₀).next.heap ∧ post addr=final addr)
    (nodeWin:archiveWindow u ((arm).party.nodes+8*node) 8)
    (kw:archiveWindow u kernel0 5) (iw:archiveWindow u baseRow 6) (qw:archiveWindow u counts (row₀).letters)
    (high:base u 19≤kernel0 ∧ base u 19≤baseRow ∧ base u 19≤counts)
    (width:2^(siteHeight copy (tileAt).bitCap)≤V) (work:StableCompactNativeBudget.budget (siteHeight copy (tileAt).bitCap)≤V)
    (kindSmall:∀a:Fin 7,(row₀).words a≤V)
    (tableTags:Fintype.card ((Fin 3→Bool)→F)≤2^W) =>
  let t:Fin (height+1):=⟨siteHeight copy (tileAt).bitCap,by omega⟩
  letI:Nonempty (tileAt).Alphabet:=(tileAt).hasLetter
  let hd:Header (demandGraph.Port part.val) (tileAt).Alphabet (fun q=>baseAt q.val.1)
      (tileAt).bits (Fintype.card (demandGraph.Port part.val)):=⟨dp,(tileAt).encode⟩
  let gd:=headerGood ShrinkMotif.supply part.val sp hd.code
  let lt:=headerLetter ShrinkMotif.supply part.val sp alpha hd.code
  let tape:=HistogramTileNetwork.tile demandGraph ShrinkMotif.supply part.val baseAt hd sp (tileAt).output
    (fun a e=>(tileAt).output_le_cap a _) (tileAt).entry
  let gmem:shrinkGrid B level ∈ grids B:=by rw [stage];simp
  let bounds:=arity_fits B gmem (show shrinkParty T₀ bestIndex part.val ∈ (shrinkGrid B level).rows from grid_has _ _ _)
  let term:(T₀).row bestIndex=PhysicalShrink.picked T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀:=
    (T₀).row_chosen (du m₀)
  let chosenParty : shrinkParty T₀ bestIndex part.val =
      recordedRoleAt T₀ (PhysicalShrink.picked T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀) part.val :=
    congrArg (fun row => recordedRoleAt T₀ row part.val) term
  let fit:hd.arity+(Fintype.card (supplyGraph.Port part.val)*(tileAt).bitCap+
    Fintype.card (supplyGraph.Port part.val)*(tileAt).bitCap)≤arity B ∧
    Fintype.card (supplyGraph.Port part.val)*(tileAt).bits+sym≤arity B:=by
      rw [chosenParty] at bounds
      exact bounds
  let win:=PartyWindow.of_layout arc fam slot.val part.val.val age rowLive (show part.val.val<(fam).parties from part.val.isLt) capacity
  have big:1024≤V:=Nat.pow_le_pow_right (by decide:0<2) ((show 10≤u by omega).trans (Nat.le_self_pow (by decide) u))
  have vFit:V<2^W:=by
    have hh:=TickWorkspace.word_space (u:=u) (i:=0) (by omega) (by change 0<V^4;positivity)
    have small:=Nat.le_self_pow (by decide:4≠0) V
    change base u 0+V^4<2^W at hh
    omega
  have wide : 8 ≤ W := by
    have hu : u ≤ u^10 := Nat.le_self_pow (by decide) u
    omega
  have sep:(arm).party.seed+37≤base u 19:=by
    change base u 14+V+37≤base u 19
    have dis:=TickWorkspace.apart (u:=u) (by decide:14<19)
    change base u 14+V^4≤base u 19 at dis
    have square:V^2≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
    nlinarith only [big,square,dis]
  have ghigh : start ≤ (fam).kinds := by
    change start ≤ start + StableCompactROMNative.size height + staticSize B +
      HistoryCompactorCounts.size height + (pre.map Grid.size).sum
    omega
  let boot:=recorded_batch B s D rem hD small A cur ctr before issued final post c branch hdr H saved site O slot arm
    oldCaps baseFit wide capFits offset
    (ptr.trans (selectedIncidentWord (f₀ 36) (Incidents.capacity S₀)
      (Incidents.siteNumber (B₀).order site) slot.val))
    apart kept level mounted stage part true hp rfl rfl rfl natPtr live iw.1.le
    (fun a=>(kindSmall a).trans_lt vFit) win.seed_room rfl rfl rfl (mounted_arch_registers u B whole).2.1.le
    (width.trans_lt vFit) (fun j=>(compactor_counts_le F t j).trans_lt (work.trans_lt vFit))
    (.inr (sep.trans high.2.1))
    (.inr ((sep.trans (romHigh.trans ghigh)).trans (Nat.le_add_right _ _)))
    (.inr ((sep.trans romHigh).trans (Nat.le_add_right _ _)))
    (.inr (((sep.trans romHigh).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)))
    (.inr (sep.trans high.2.2)) dense
  have same:(row₀)=HistoryPartySpecialization.kind tape gd lt fit.1 fit.2:=by
    rw [chosenParty]
    exact Party.kind_ofTile demandGraph ShrinkMotif.supply part.val baseAt tileAt dp sp
      (fun i=>(dp i).1.1.val) (fun i=>(sp i).1.1.val) fit
  fun rowSpace pinSpace countSpace hiddenSpace=>
    recorded_pair_room (K:=K) B (shrinkGrid B level) (shrinkParty T₀) pre tail stage rfl slot.val bestIndex part.val
      tape gd lt fit.1 fit.2 post node t (numberHistogram alpha reps) baseRow counts same mounted romHigh whole
      rfl rowLive age nr capacity (by change 2^6<2^W;exact Nat.pow_lt_pow_right (by decide) (by omega))
      curNode nodeWin (rawKernel.symm ▸ kw) iw qw ⟨rawKernel.symm ▸ high.1,high.2⟩ boot
      width work kindSmall rowSpace pinSpace countSpace hiddenSpace tableTags

local notation "pageHeight" => siteHeight copy (tileAt).bitCap
local notation "pageParty" => recordedRoleAt T₀
  (PhysicalShrink.picked T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀) part.val
local notation "pageHeader" => (⟨dp,(tileAt).encode⟩ : Header (demandGraph.Port part.val) (tileAt).Alphabet
  (fun q=>baseAt q.val.1) (tileAt).bits (Fintype.card (demandGraph.Port part.val)))
local notation "pageTile" => HistogramTileNetwork.tile demandGraph ShrinkMotif.supply part.val baseAt pageHeader sp
  (tileAt).output (fun a _=>(tileAt).output_le_cap a _) (tileAt).entry
local notation "pageChecks" => Diagonal.HistoryContraction.Tree.admission (headerGood ShrinkMotif.supply part.val sp (tileAt).encode)
  (headerLetter ShrinkMotif.supply part.val sp alpha (tileAt).encode)
  (MotifNativeCompactors.partialInput F copy pageHeight) (numberHistogram alpha reps)
local notation "pagePayload" => Diagonal.HistoryContraction.Tree.tiled pageTile (MotifNativeCompactors.partialInput F (copy*(tileAt).bitCap) pageHeight)

omit [Fintype F] in
private theorem selectedPageAlphabet (catalogue : ShrinkMotif.Table F) (row : catalogue.Row) :
    Nonempty (catalogue.block row).Alphabet :=
  (catalogue.block row).hasLetter

private abbrev selectedRowPageBounds (catalogue : ShrinkMotif.Table F) (row : catalogue.Row)
    (port : Fin 6) (r ar age price : ℕ) (hist : Histogram (catalogue.block row).Alphabet r)
    (gridAt : Grid F) (cell : recordedRoleAt catalogue row port ∈ gridAt.rows) (copies : r ≤ price)
    (margin : gridPageRate ar gridAt * ((price+1)*(16*age^10+1)^3) ≤ volume age) :=
  let demand := (Fintype.equivFin (demandGraph.Port port)).symm
  let supply := (Fintype.equivFin (supplyGraph.Port port)).symm
  And.intro (page_height_at_age ar age price r gridAt (recordedRoleAt catalogue row port) cell copies margin)
    (party_page_caps_at_age demandGraph ShrinkMotif.supply port (catalogue.base row) (catalogue.block row)
      demand supply (fun i => (demand i).1.1.val) (fun i => (supply i).1.1.val)
      hist ar age price gridAt cell copies margin)

private abbrev selectedGridPageBounds (block : Block F) (gridLevel : Fin block.levels)
    (winner : Fin (block.shrink.more.length+1)) (port : Fin 6) (row : block.shrink.Row)
    (selected : block.shrink.row winner = row) (r age price : ℕ)
    (hist : Histogram (block.shrink.block row).Alphabet r) (copies : r ≤ price)
    (margin : gridPageRate (arity block) (shrinkGrid block gridLevel) *
      ((price+1)*(16*age^10+1)^3) ≤ volume age) :=
  have member : shrinkParty block.shrink winner port ∈ (shrinkGrid block gridLevel).rows :=
    grid_has (shrinkParty block.shrink) winner port
  have same : shrinkParty block.shrink winner port = recordedRoleAt block.shrink row port :=
    congrArg (fun r₀ => recordedRoleAt block.shrink r₀ port) selected
  have cell := (congrArg (fun p : Party F => p ∈ (shrinkGrid block gridLevel).rows) same).mp member
  have pages := selectedRowPageBounds block.shrink row port r (arity block) age price hist
    (shrinkGrid block gridLevel) cell copies margin
  have kindWords := (congrArg (fun p : Party F =>
    ∀ j : Fin 7, (p.kind (arity block)).words j ≤ volume age) same).mpr pages.2.kindSmall
  And.intro pages.1 (And.intro kindWords pages.2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1800000 in
/-- A priced incident in the shrink grid fits the checks and payload allocations
at the row minimizing its issued demands. -/
theorem selected_shrink_page_caps (price : ℕ) (copies : copy≤price)
    (margin : gridPageRate (arity B) (shrinkGrid B level)*((price+1)*(W+1)^3)≤V) :
    letI := selectedPageAlphabet B.shrink (PhysicalShrink.picked T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀)
    pageHeight≤W ∧ (∀ a : Fin 7,(row₀).words a≤V) ∧
      PartyPageCaps V (arity B) pageParty copy pageHeight
        ((pageChecks).rows+(pagePayload).rows) ((pageChecks).bits+(pagePayload).bits) := by
  classical
  let := selectedPageAlphabet B.shrink (PhysicalShrink.picked T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀)
  exact selectedGridPageBounds B level bestIndex part.val
    (PhysicalShrink.picked T₀ P₀ prior (shrinkRecordCode s rem A) hc₀ m₀)
    ((T₀).row_chosen (du m₀)) copy u price reps copies margin

include stage in
/-- The selected kind and port row lie in the actual permanent archive. Its payload
words fit at the same age that pays the elected local arrays. -/
theorem selected_shrink_page_rom (whole : archiveWindow u start (libraryWords B height))
    (smallRate : gridPageRate (arity B) (shrinkGrid B level)<2^W) :
    let winner := RefreshDemandRows.tileNumber
      (PhysicalShrink.b (shrinkRecordPacking s rem A) (shrinkRecordWidth s rem A)
        (shrinkRecordCode s rem A) (colors_le s) (O.equiv slot).val) (B.shrink.base ∘ B.shrink.row)
    let G := shrinkGrid B level
    let pos := winner.val*6+part.val.val
    let page := G.family (Mounted.base B height start pre)
    page.kinds+7*pos+7≤2^W ∧ page.ports+G.stride*pos+G.stride<2^W ∧
      ∀k:Fin G.stride,(shrinkParty B.shrink winner part.val).port.at G.demand G.supply k.val<2^W := by
  intro winner G pos page
  have row : G.rows[pos]?=some (shrinkParty B.shrink winner part.val) := by
    change (grid (shrinkParty B.shrink))[winner.val*6+part.val.val]?=_
    rw [Nat.mul_comm winner.val 6]
    exact grid_row (shrinkParty B.shrink) winner part.val
  obtain ⟨atRow,_⟩:=List.getElem?_eq_some_iff.mp row
  have kind:=Nat.mul_le_mul_left 7 (Nat.succ_le_of_lt atRow)
  have ports:=Nat.mul_le_mul_left G.stride (Nat.succ_le_of_lt atRow)
  rw [Nat.mul_succ] at kind ports
  have cut : (pre.map Grid.size).sum+G.size≤gridSize B := by
    simp [G,gridSize,stage]
  have startEnd : gridStart B start height+gridSize B<2^W := by
    simpa only [gridStart,libraryWords,Nat.add_assoc] using whole.1
  have pageEnd : Mounted.base B height start pre+G.size<2^W := by
    unfold Mounted.base
    rw [Nat.add_assoc]
    exact (Nat.add_le_add_left cut _).trans_lt startEnd
  change Mounted.base B height start pre+(7+G.stride)*G.rows.length<2^W at pageEnd
  rw [Nat.add_mul] at pageEnd
  change Mounted.base B height start pre+7*pos+7≤2^W ∧
    Mounted.base B height start pre+7*G.rows.length+G.stride*pos+G.stride<2^W ∧ _
  exact ⟨by omega,by omega,fun k=>(port_word_le_grid (arity B) G
    (List.mem_of_getElem? row) k).trans_lt smallRate⟩

end OccupiedShrink


end
end ThreeFlat.RAM.HistoryShrinkEmitter

end OAI
