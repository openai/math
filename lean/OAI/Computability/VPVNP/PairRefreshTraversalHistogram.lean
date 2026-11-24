import OAI.Computability.VPVNP.PairRefreshTraversalAction

/-!
# Histogram of a successful terminal refresh

A successful refresh changes each private histogram cell by the number of
occurrences of its parameter in the emitted list. The statement applies to
arbitrary incoming DFS scratch, including the counters accumulated by earlier visits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.RefreshResidentImage.Plan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe OperandInputs PairSimulation NodeArguments MotifConversion NewSlots RefreshMapOperands
open MotifEntry MotifDemandPadding MotifSelector LocalHistory
open scoped Fin.CommRing

variable {bits g t hist shared : ℕ} {k : Type} [_root_.Field k] {S : BlockSchedule k}
  {B : S.Templates} (T : Plan B t hist shared)
  (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent)) (A : Arena) (child parent : ℕ)

local notation "D" => 2 ^ S.portExponent
local notation "H" => 2 ^ S.expanderExponent
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
  (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh S.port_order
  (And.right S.degree_bounds) choice

variable (old : X.network.Half (oldSite X v))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh S.port_order
    S.degree_bounds.2 choice).network.Half (promotedSites v))

local notation "I" => entryInput B X choice v old new
local notation "z" => demandGrid B.refresh (fun _ => zero_lt_one) (EntryInput.demand I)
local notation "L" => MapInline.layout B.refresh z (Prod.snd v)
local notation "u" => repetitions B.refresh (EntryInput.demand I)
local notation "d" => demandBits tieSource tieTarget (Prod.snd v) (EntryInput.demandBits I)
local notation "x" => mapHalf S.portSupply (fun _ => inputBits) (EntryInput.supplyBits I)
local notation "entry" => runEntry B.refresh (fun _ => zero_lt_one) (EntryInput.demand I)
  (EntryInput.payload I) (Prod.snd v) d x
local notation "names" => Option.map (List.map (Plan.ordinal T)) (Prod.fst entry)

set_option maxHeartbeats 1800000 in
-- The label array and the row evaluator use the same dependent field buffers.
theorem mapUpper_histogram {n limit : ℕ} (top maxWidth directory histBase : ℕ)
    (oldEnd : A.base child + (packed X (oldSite X v) old).length ≤ top)
    (newEnd : A.base parent + (packed Y (promotedSites v) new).length ≤ top)
    (oldWidth : X.maxWireWidth ≤ maxWidth) (newWidth : (Y).maxWireWidth ≤ maxWidth)
    (inputsEnd : top + 2 * maxWidth ≤ directory) (histEnd : histBase + hist ≤ directory)
    (workEnd : directory + MapCallWords.headCapacity D H + 2 * u ≤ limit)
    (capacity : MapWorkspace.Capacity B.refresh bits n limit) (copyBound : u ≤ n)
    (tableWidth : MapConstants.widthThreshold B.refresh ≤ bits)
    {endAddr : ℕ} (saved : DFS.Scratch bits endAddr) (good : (names).isSome = true)
    (l : Fin hist) (above : endAddr ≤ (word (bits := bits) (histBase + l.val)).val) :
    T.mapUpper X choice v A child parent old new top maxWidth directory histBase
      oldEnd newEnd oldWidth newWidth inputsEnd histEnd workEnd capacity copyBound
      tableWidth endAddr saved ⟨word (histBase + l.val), above⟩ =
      saved ⟨word (histBase + l.val), above⟩ + (((names).getD []).count l : W bits) := by
  let R := MapCallWords.regions B X choice v A child parent old new directory histBase
  let loc := (L).corePC (L).locations
  let ord := MapCallWords.regions_ordered B X choice v A child parent old new z (L).core loc
    top maxWidth directory histBase limit oldEnd newEnd oldWidth newWidth inputsEnd histEnd workEnd
  let Wk := MapWorkspace.workspace (MapInline.callProgram L) R d x capacity copyBound ord
  let mem : PrivateScratch.Memory bits := fun q => if h : endAddr ≤ q.val then saved ⟨q,h⟩ else 0
  let sel := MapConstants.selectorWord B.refresh
    (MapConstants.fits_of_threshold B.refresh tableWidth).2.2.2
  let a : W bits := word (histBase + l.val)
  have aVal : a.val = histBase + l.val := Nat.mod_eq_of_lt (by
    have := l.isLt
    have := capacity.room
    omega)
  have array (base len : ℕ) (lo : directory ≤ base) (hi : base + len ≤ limit)
      (values : Fin len → W bits) (before : PrivateScratch.Memory bits) :
      PrivateScratch.write (base : W bits) values before a = before a := by
    apply dite_eq_right
    rintro ⟨i, hit⟩
    rw [← Nat.cast_add] at hit
    have inRange := (Nat.add_lt_add_left i.isLt base).trans_le hi
    have eq := (Nat.mod_eq_of_lt (inRange.trans capacity.room)).symm.trans
      ((congrArg Fin.val hit).trans aVal)
    have := l.isLt
    omega
  have argc : Fintype.card (MapCallSetup.Arg (Tie D) (Fin D × Fin H)) ≤
      MapCallWords.headCapacity D H := le_max_right _ _
  have published : MapScratch.published (L).core (L).args loc Wk (word directory) mem a = mem a :=
    array directory (Fintype.card (MapCallSetup.Arg (Tie D) (Fin D × Fin H))) le_rfl (by omega) _ mem
  have portsEnd := ord.directoryEnd
  change directory + (MapPortAgreement.ports S.portSupply v.2 (L).core.edgeOrder).length ≤
    directory + MapCallWords.headCapacity D H at portsEnd
  have directoryMem (before : PrivateScratch.Memory bits) :
      MapCallSetup.directoryMemory (L).core loc Wk before a = before a :=
    array directory _ le_rfl (by omega) _ before
  have sourceLo : directory ≤ Wk.source := Nat.le_add_right ..
  have targetLo : directory ≤ Wk.target := sourceLo.trans (Nat.le_add_right ..)
  have sourceEnd : Wk.source + u ≤ limit := by
    change directory + MapCallWords.headCapacity D H + u ≤ limit
    omega
  have targetEnd : Wk.target + u ≤ limit := by
    change directory + MapCallWords.headCapacity D H + u + u ≤ limit
    omega
  have run : (MotifEntry.run tieSource tieTarget (baseDemand B.refresh z) (EntryInput.demand I)
      S.portSupply (basePayload B.refresh) (lookup B.refresh z) (selectorTable B.refresh)
      (selectorCode B.refresh) (EntryInput.payload I) v.2 d x).1.isSome = true := by
    change (entry).1.isSome = true
    simpa only [Option.isSome_map] using good
  obtain ⟨θ, pick, valid⟩ := MapScratch.sequence_of_success run
  change MapScratch.successMemory (L).core (L).args loc Wk (word directory) sel T.ordinal mem a = _
  rw [MapScratch.successMemory, pick, Option.elim_some, MapEntry.Program.successMemory]
  change PrivateLabels.accumulate Wk.hist _ _ (word (Wk.hist + l.val)) = _
  erw [PrivateLabels.accumulate_at Wk.hist _ _ Wk.histogramFit l,
    array Wk.target u targetLo targetEnd, array Wk.source u sourceLo sourceEnd,
    directoryMem, published]
  have start : mem a = saved ⟨a, above⟩ := dite_eq_left above
  erw [start]
  congr 1
  unfold runEntry
  erw [MapFinish.entry_value, pick, Option.bind_some, ite_eq_left valid, Option.map_some,
    Option.getD_some, List.map_ofFn]
  rfl

end CompressorRecords.PortRefresh.RefreshResidentImage.Plan

namespace CompressorRecords.PortRefresh.TraversalPlan

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PhaseRecipe PairSimulation NewSlots
open RefreshMapOperands LocalHistory NetworkKernel
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {t hist bits g : ℕ}
  (ties : Fin t ≃ Tie (2 ^ S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent)) (degree n rowEnd child parent : ℕ)
  (room : Room B X choice v degree n rowEnd child parent hist bits)
  (old : X.network.Half (oldSite X v))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))

local notation "hb" => LeafArena.Regions.histBase (TerminalLayout.privateRegions degree n rowEnd hist)
local notation "names" => emitted B order X choice v old new

set_option maxHeartbeats 1400000 in
-- Specialize the two dependent node buffers and the terminal scratch layout.
theorem upper_histogram {endAddr : ℕ} (s : DFS.Scratch bits endAddr) (good : (names).isSome = true)
    (l : Fin hist) (above : endAddr ≤ (word (bits := bits) (hb + l.val)).val) :
    canonicalUpper B ties stride order X choice v degree n rowEnd child parent room old new
      s ⟨word (hb + l.val), above⟩ =
      s ⟨word (hb + l.val), above⟩ + (((names).getD []).count l : W bits) := by
  unfold emitted at good ⊢
  split at good
  · rename_i diagonal
    rw [ite_eq_left diagonal]
    unfold canonicalUpper
    apply RefreshResidentImage.Plan.mapUpper_histogram
    exact good
  · contradiction

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
