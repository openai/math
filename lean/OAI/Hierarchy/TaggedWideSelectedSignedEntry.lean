import OAI.Hierarchy.TaggedWideFundedSelectedPacket
import OAI.Hierarchy.ProbeFixedFundedSignedRow
import OAI.Hierarchy.TaggedWideCalendarControlRoom

namespace OAI
/-! # The signed repaired row on the returned original gate memory -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive CatalogueRows Tagged WireTelescope CalendarTape TaggedShorterBudget TaggedShorterSupergroups
open TaggedPrune Tagged.WideStack Filter ThreeFlat.RAM CoreBoard.PhysicalTerm
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
set_option cleanup.letToHave false
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
    {N : ℕ} (x : WideParent κ A) (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x)
    (rate : v.sharpPaidUnit≤unitCost) (support : v.SelectedReturnSupport m ell short u δ ξ unitCost rate x)
local notation "h" => x.h
local notation "width" => x.w
local notation "d" => 2^v.W
local notation "g" => v.wideDated h width ell unitCost
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "Sfit" => (v.wide_installed_tape_bounds x m ell unitCost g).2.2
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
    (v.wide_dated_sites h width ell unitCost) (v.wide_dated_edges h width ell unitCost) (fun _=>0)
local notation "reader" => v.wideSelector h width cpu.age cpu.ready.credit cpu.ready.size_le
local notation "sl" => (reader).format.slot
local notation "es" => events v.mesh
local notation "menu" => (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ
local notation "slots" => purchaseSlots h v.W k v.wideJobs ell
variable (prices : v.PhysicalCounts u A δ ξ m) {C : ℝ} (pricePos : 0≤κ)
    (buy : ∀t:Fin (m+1),Purchased F ((typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ) x t (purchaseSlots x.h v.W k v.wideJobs ell)
      (purchaseCandidates x.h v.W k v.wideJobs (purchaseSlots x.h v.W k v.wideJobs ell) ((((typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ)).height t x) (purchaseModules v.W u δ ξ ((typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ) x t))
      (purchaseModules v.W u δ ξ ((typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ) x t) C)
    (groupsFit : GroupRoom v.W k v.wideJobs u δ ξ ((typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ) x)
    (metadata : ∀t:Fin (m+1),1+(((typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ)).height t x+(((typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ)).height t x≤(((typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ)).payload t x)
    (lanesFit : v.wideInstalledCap unitCost≤2^ell)
variable {b : Fin k→ℕ} (e : OpenPins x.h x.w b→Bool) (perm : Equiv.Perm (Tagged.Row x.h))
    (tag : (perm : Tagged.Row x.h→Tagged.Row x.h)=Tagged.tag (fun i=>e (.inl i)))
local notation "base" => v.wideOrigin h width S seed perm
variable (j : Path (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot (events v.mesh)
    (v.wideOrigin x.h x.w (v.wideInstalledSize x m ell unitCost (v.wideDated x.h x.w ell unitCost))
      (v.wideInstalledHeader x m ell short u δ ξ unitCost (v.wideDated x.h x.w ell unitCost)
        (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)) perm))
local notation "bought" => v.wide_selected_local_return m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j

local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "first" => (lay).pruneScratch+(lay).pruneRows+1
local notation "rootROM" => v.wideInstalledRoot x
local notation "rankEnd" => v.wideSpillRankEnd h width v.maxBits first
variable (t : Fin (events v.mesh).length) (a : Attempt) (onDate : (events v.mesh).get t=.attempt a)

local notation "extent" => (v.wide_funded_extent h width v.maxBits).trans Sfit
local notation "chosen" => Prefix.pathVisitAt j t onDate
local notation "date" => v.wide_funded_date_with h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior (chosen).choice (chosen).future
local notation "reference" => v.wide_reference_date h width S extent perm seed cpu.age cpu.ready.credit
  cpu.ready.size_le (chosen).prior
local notation "memo" => v.wide_selected_ballot_snapshots m ell short u δ ξ unitCost x cpu rate support
  prices pricePos buy groupsFit metadata lanesFit e perm tag j false t a onDate


open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WideControlJoin WireTelescope.PassMatrix WideCPU
local notation "G₀" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "W₀" => Native.wordBits h d Native.copies
local notation "S₀" => siteLast h d k+1
local notation "R₀" => (reference).2
local notation "age₀" => support.size.tenderAge
local notation "floor₀" => support.size.widthFloor
local notation "sector" => v.wideSpillDates h width ell unitCost v.maxBits first
local notation "sw" => (sector).roleRoot rankEnd 2
local notation "returned" => (bought).2.2.2.choose
local notation "dmd" => fun l=>((R₀).row extent age₀ floor₀ l).input
local notation "rewired" => fun l=>((R₀).tender extent age₀ floor₀ l).post ((chosen).choice l)
local notation "degree" => v.widePacketDegree
local notation "cap" => v.wideNeighborCap width unitCost
local notation "sh" => v.widePacketShape h width (.attempt a)

variable {Sel Data : Type} [Fintype Sel] [Fintype Data]
local notation "V₀" => SitePins (OpenPins h width b) Sel Data G₀

private theorem finiteRoomOnEqualSize {sizeA sizeB : ℕ} (target : ℕ → Prop)
    (sizes : sizeA = sizeB) (values : ∀ label : Fin sizeA, target label.val)
    (label : Fin sizeB) : target label.val := values (label.cast sizes.symm)

private theorem selectedPrintedWordOnEqualWidth (modulus page site column nativeWidth publishedWidth : ℕ)
    (readWord : ℕ → Fin modulus) (stored : Fin modulus) (widths : nativeWidth = publishedWidth)
    (printed : readWord (page+1+site*publishedWidth+column) = stored) :
    (readWord (page+1+site*nativeWidth+column)).val = stored.val := by
  rw [widths]
  exact congrArg Fin.val printed

open Lean Elab Term Meta in
local elab "selectedPrintedWord " table:term " atSite " site:term " atColumn " field:term
    " usingWidths " same:term " andAddress " "[" positions:term,* "]" : term => do
  let claims ← elabTerm table none
  let i ← elabTerm site none
  let j ← elabTerm field none
  let reads := mkAppN claims #[i, j]
  let some reading ← whnfUntil (← inferType reads) ``Eq
    | throwErrorAt table "expected the selected returned packet table at this site and column"
  let row := reading.getAppArgs
  let some finType ← whnfUntil row[0]! ``Fin
    | throwErrorAt table "the returned packet must consist of native words"
  let alignment ← elabTerm same none
  let some widthEq ← whnfUntil (← inferType alignment) ``Eq
    | throwErrorAt same "expected the selected and printed column counts to agree"
  let columns := widthEq.getAppArgs
  let loc ← positions.getElems.mapM (fun item => elabTerm item none)
  unless loc.size == 3 && row[1]!.isApp do throwError "the published value must be a read from the selected memory"
  return mkAppN (← mkConstWithFreshMVarLevels ``selectedPrintedWordOnEqualWidth)
    (#[finType.getAppArgs.back!] ++ loc ++ #[columns[1]!, columns[2]!, row[1]!.appFn!, row[2]!, alignment, reads])

open Lean Elab Term Meta in
local elab "selectedPhysicalReceipt " head:ident "[" operands:term,* "]" : term => do
  let args ← operands.getElems.mapM (fun operand => elabTerm operand none)
  let name ← resolveGlobalConstNoOverload head
  return mkAppN (← mkConstWithFreshMVarLevels name) args

open Lean Elab Term Meta in
local elab "signedAtSelectedFundedDates " earlier:term " and " laterDate:term
    " forAttempt " eventAttempt:term " fromSnapshot " snapshot:term " fromFacts " factsTerm:term
    " layout " "[" layoutArgs:term,* "]" " bounds " "[" boundsArgs:term,* "]"
    " gates " "[" gateArgs:term,* "]" : term => do
  let referenceEvidence ← elabTerm earlier none
  let selectedEvidence ← elabTerm laterDate none
  let some referenceType ← whnfUntil (← inferType referenceEvidence) ``FundedDate
    | throwErrorAt earlier "the reference must identify a funded date"
  let some selectedType ← whnfUntil (← inferType selectedEvidence) ``FundedDate
    | throwErrorAt laterDate "the accepted continuation must identify a funded date"
  let e ← elabTerm eventAttempt none
  let originalSnapshot ← elabTerm snapshot none
  let evidence ← elabTerm factsTerm none
  let right := fun (p : Lean.Expr) => Lean.Expr.proj ``And 1 p
  let left := fun (p : Lean.Expr) => Lean.Expr.proj ``And 0 p
  let rom := left (right (right (right originalSnapshot)))
  let low := left (right evidence)
  let some lowType ← whnfUntil (← inferType low) ``PrefixAgreement.Low
    | throwErrorAt factsTerm "the selected packet facts must identify the funded checkout"
  let held := lowType.getAppArgs
  unless held.size == 4 do throwError "unexpected selected checkout arity {held.size}"
  let refArgs := referenceType.getAppArgs
  let selArgs := selectedType.getAppArgs
  unless refArgs.size == 22 && selArgs.size == refArgs.size do
    throwError "unexpected original funded date signature: {refArgs.size} / {selArgs.size}"
  let geometry ← layoutArgs.getElems.mapM (fun t => elabTerm t none)
  let bounds ← boundsArgs.getElems.mapM (fun t => elabTerm t none)
  let gates ← gateArgs.getElems.mapM (fun t => elabTerm t none)
  unless geometry.size == 8 && bounds.size == 2 do throwError "incomplete selected physical data"
  let dateArgs := refArgs.extract 0 17 ++ #[e] ++ refArgs.extract 18 22
    ++ #[selArgs.back!, referenceEvidence, selectedEvidence]
  let body := dateArgs ++ geometry ++ #[held[2]!, low, rom,
      left (right (right evidence)), left (right (right (right evidence)))]
    ++ bounds ++ gates
  let entry ← mkConstWithFreshMVarLevels ``FundedDate.signed_row_entry
  let required ← whnf (← inferType (mkAppN entry (body.extract 0 34)))
  let some _ ← whnfUntil required.bindingDomain! ``PrefixAgreement.Low
    | throwError "the original signed row must require a prefix agreement"
  return mkAppN entry body

/-- The selected reference packet and its accepted continuation use the same
physical ballot words at the returned memory. The remaining arguments are
the two original role partitions, their lookups and the actual wired bits. -/
abbrev selected_signed_entry (limits : SignedSites.CalendarControlRoom (cpu:=cpu))
    (word : v.PartyWordBounds h width unitCost)
    (s : Fin S₀) (wire : Bool→Fin degree→Fin cap→V₀⊕Bool) (sel : Sel→Bool) (data : Data→Bool)
    (rest : Widths S₀) (x₀ : State (rest+∑l,dmd l) s) (y₀ : State (rest+∑l,rewired l) s)
    (l : PassiveWindow.Parts ((portGraph S₀).Port s) (Fin degree) cap (fun p=>(rest+∑i,dmd i) p.val.1))
    (r' : PassiveWindow.Parts ((portGraph S₀).Port s) (Fin degree) cap (fun p=>(rest+∑i,rewired i) p.val.1)) :=
  let scene := selectedPhysicalReceipt wide_selected_ballot_snapshots
      [F, (inferInstance : Field F), k, p, q, Q, σ, Λ, κ, A, v, m, ell, short, u, δ, ξ, unitCost, N, x, cpu, rate, support, prices, C, pricePos, buy, groupsFit, metadata, lanesFit, b, e, perm, tag, j, false, t, a, onDate]
  let facts := selectedPhysicalReceipt wide_selected_packet_reads
      [F, (inferInstance : Field F), k, p, q, Q, σ, Λ, κ, A, v, m, ell, short, u, δ, ξ, unitCost, N, x, cpu, rate, support, prices, C, pricePos, buy, groupsFit, metadata, lanesFit, b, e, perm, tag, j, false, t, a, onDate]
  let posted := selectedPhysicalReceipt wide_selected_returned_packet_table
      [F, (inferInstance : Field F), k, p, q, Q, σ, Λ, κ, A, v, m, ell, short, u, δ, ξ, unitCost, N, x, cpu, rate, support, prices, C, pricePos, buy, groupsFit, metadata, lanesFit, b, e, perm, tag, j, false, t, a, onDate]
  have same : ((g).ballot t)=sh := congrArg (v.widePacketShape h width) onDate
  have affordable (f : Fin (sh).columns) : ballotAddress g sw t s f.val<(G₀).u := by
    let small (code : ℕ) := ballotAddress g sw t s code < (G₀).u
    apply finiteRoomOnEqualSize small (congrArg Shape.columns same) _ f
    exact (SignedSites.calendar_words (u:=u) (δ:=δ) (ξ:=ξ) (x:=x) (N:=N) v m ell short unitCost cpu).1 s t
  have degreeFit : degree<2^W₀ :=
    (Nat.le_add_left degree (2*v.widePacketRoles h)).trans_lt ((v.party_role_room h).trans_le word.role)
  let tags:=support.size.partyTags a
  signedAtSelectedFundedDates R₀ and date forAttempt a fromSnapshot scene fromFacts facts
    layout [extent, age₀, floor₀, ProtocolRAMPurchaseSampler.bits (v.widePacketShelf h),
      (g).siteROM rootROM, (g).siteStride rootROM, (g).roleStart S t.castSucc, (sector).dateRole rankEnd t 0]
    bounds [tags.1, tags.2]
    gates [OpenPins h width b, Sel, Data, (inferInstance : Fintype (OpenPins h width b)),
      (inferInstance : Fintype Sel), (inferInstance : Fintype Data),
      unitCost, ell, G₀, (rfl : (G₀).W = W₀), sw, t, s, wire, returned, e, sel, data,
      rest, x₀, y₀, l, r', (fun i : Fin (G₀).u => (rfl : ((G₀).addr i).val=i.val)),
      limits.signedRead s t, limits.mode s t, Nat.clog 2 (v.signedPartyCount h a+1),
      (v.signed_tag_digits h a).1, (v.signed_tag_digits h a).2.1.trans limits.tag, limits.lane,
      word, v.wide_selected_row_count m ell short u δ ξ unitCost x cpu, degreeFit, affordable,
      (fun f : Fin (sh).columns => selectedPrintedWord posted atSite s atColumn f
        usingWidths (congrArg Shape.columns same) andAddress [(g).ballotStart sw t, s.val, f.val])]

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "selected_signed_entry"
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
