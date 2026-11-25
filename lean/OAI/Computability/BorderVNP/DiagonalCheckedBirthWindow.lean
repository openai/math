import OAI.Computability.BorderVNP.DiagonalNativeCorePaths
import OAI.Computability.BorderVNP.PackedBottomRetainedReports
import OAI.Computability.BorderVNP.DiagonalSewnBirthInputs
import OAI.Computability.BorderVNP.DiagonalCheckedSeedReportRows
import OAI.Computability.BorderVNP.PackedBundleGroups

/-! # Original work and observations inside a passing physical cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing CellAddresses BottomReports Inherited Site.Programs Diagonal.CellEntries CellSparse
open DiagonalTallyCellReports DeckGrid.WiredWitness
open scoped Classical
open private bits_left from OAI.Computability.BorderVNP.PackedInheritedStaging
open private read_prefix off_fits from OAI.Computability.BorderVNP.PackedInheritedMergeRows

variable {D N₀ ns ne np n d blocks b h K s : ℕ} {P J Param Gadget Team : Type} [Fintype P]
    {widths : P → ℕ} (N : Network D P widths) (cell : N.Site → Fin N₀)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (birthWidth : ∀ j, (state (host j)).birth.work = mult j*(slabs j).stride)
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports widths)
    (number : Gadget ↪ ℕ) (tags : BottomChoices slabs mult → N.Tables (Entry Param Gadget))
    (model : ∀ z, TagModels N edgeID portID state (tags z) number (carryPred host (birthPredicate slabs mult z)))
    (q : Routed (b:=b) (s:=s) owners)
    (raw : (c : Fin N₀) → Fin (externalBase N cell c (placedSize N state)) → Bool)
    (ok : CorePassed N cell siteID edgeID portID state host slabs mult birthWidth owners slot ports number tags model q raw)

local notation3 (prettyPrint := false) "size" => placedSize N state
local notation3 (prettyPrint := false) "supply" => pathSupply N cell edgeID portID owners slot ports
local notation3 (prettyPrint := false) "z₀" => extractBottom N cell siteID size owners slabs mult
  (fun (_ : Routed (b:=b) (s:=s) owners) j => retainedLocation N state host slabs mult birthWidth j) q raw
local notation3 (prettyPrint := false) "g₀" c => privateWires N cell size c (raw c)
local notation3 (prettyPrint := false) "u₀" c => privateStaging N cell size c (raw c)
local notation3 (prettyPrint := false) "path₀" => rawPath N cell edgeID state owners q raw

include ok in
/-- Read the successful original observation on this precise recovered routed
path, using the original work in the raw physical cell before picking its report. -/
theorem CorePassed.raw_birth_observed (v : N.Site) :
    let L := state v
    let input := inputWords N edgeID portID v (pathEdges slot path₀ v) (fun f => ports f.val) ∘ Fin.cast L.size
    let work := rawBirth N cell siteID state raw v
    (L.birth.observe (bits work (L.retention.readInput input))).isSome = true := by
  intro L input work
  let c := cell v
  let u : {v : N.Site // cell v=c} := ⟨v,rfl⟩
  let read := tagReadAt N cell edgeID portID state host slabs mult owners supply number tags model z₀ q c (g₀ c) u
  let localInput := Placement.canonical N cell c edgeID portID u (g₀ c) (supply q c) ∘ Fin.cast L.size
  obtain ⟨alive,placed⟩ := ok.2 c u
  have same : work = read.work :=
    (congrArg L.originalWord placed).trans (L.originalWord_complete localInput read.work)
  have observed := (read.read read.work read.observations read.chosen).mpr ⟨alive,rfl,rfl⟩
  have localWords : localInput = input := by
    change (inputWords N edgeID portID v (localWire N cell edgeID portID owners supply q c (g₀ c) u)
      (localPort N cell edgeID portID owners supply q c u)) ∘ Fin.cast L.size = _
    rw [localWire_path,localPort_path]
  rw [same,←localWords,observed]
  rfl

/-- Every original work bit is read from its physical site interval in the
whole cell bank, including when the validator has appended the report tape. -/
theorem raw_birth_lookup (v : N.Site) (supplyBits : Fin (suppliedSize N cell (cell v)) → Bool)
    (tail : List Bool) (k : Fin (state v).birth.work) :
    let c := cell v
    let physical := bank N cell c size (g₀ c) (u₀ c) supplyBits ++ tail
    lookup physical (siteBase N cell c siteID size ⟨v,rfl⟩ + k.val) =
      rawBirth N cell siteID state raw v k := by
  intro c physical
  let u : {j : N.Site // cell j=c} := ⟨v,rfl⟩
  let L := state v
  let i := (k.castLE L.retention.work_le).castAdd L.program.incoming
  have bound := (Nat.add_lt_add_left i.isLt (siteBase N cell c siteID size u)).trans_le
    (off_fits N cell c siteID (fun j => (state j).program) u)
  exact (read_prefix N cell c (fun j => (state j).program) (g₀ c) (u₀ c) supplyBits tail _ bound).trans
    (site_at N cell c size siteID (g₀ c) (u₀ c) supplyBits u i)

include birthWidth in
/-- Each retained original verifier copy reads its actual physical private
region, including all staged uses, and its independent bottom digits. The
extra tape and the pulled-back incidence inputs may be arbitrary here. -/
theorem raw_birth_copy_window (j : J) (tail : List Bool)
    (input : Fin (state (host j)).birth.incoming → Bool) :
    let v := host j
    let c := cell v
    let base := siteBase N cell c siteID size ⟨v,rfl⟩
    let physical := lookup (bank N cell c size (g₀ c) (u₀ c) (supply q c) ++ tail)
    let original := bits (rawBirth N cell siteID state raw v) input
    (∀ (i : Fin (mult j)) (k : Fin (slabs j).stride),
      physical (base+i.val*(slabs j).stride+k.val) = original (i.val*(slabs j).stride+k.val)) ∧
    (∀ (i : Fin (mult j)) (k : Fin (slabs j).guessed),
      original (i.val*(slabs j).stride+k.val)=z₀ j i k) := by
  intro v c base physical original
  have digit {k : ℕ} (hk : k < (slabs j).stride) (i : Fin (mult j)) :
      i.val*(slabs j).stride+k < (state v).birth.work := by
    rw [birthWidth]
    exact (Nat.add_lt_add_left hk _).trans_le (by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ i.isLt)
  constructor
  · intro i k
    let a : Fin (state v).birth.work := ⟨_,digit k.isLt i⟩
    rw [Nat.add_assoc]
    exact (raw_birth_lookup N cell siteID state raw v (supply q c) tail a).trans
      (bits_left (rawBirth N cell siteID state raw v) input a).symm
  · intro i k
    have hs : k.val < (slabs j).stride := by
      have fit := (slabs j).fineFits
      have hk := k.isLt
      simp only [Slab.stride,Slab.orig,bottomStride]
      omega
    let a : Fin (state v).birth.work := ⟨_,digit hs i⟩
    have eq := extracted_compatible slabs mult N cell siteID state host birthWidth owners q raw v j rfl i k
    rw [extendWork,dite_eq_left a.isLt] at eq
    exact (bits_left (rawBirth N cell siteID state raw v) input a).trans eq

include ok in
/-- A full returning private core and a physically passing checked report
supply the immutable observation and every rebased report row of this original
host on the decoded path. The original work is read from the actual raw bits. -/
noncomputable def CorePassed.retainedReport (j : J) (D₀ : Directory) (b₀ : Bundle)
    {l : ReportLayout} (out : ReportCell l) (preRows postRows : List Bundle)
    (record : ReportBundle) (before after : List ReportBundle) (parts : out.bundles=before++record::after)
    (prefixCount : (preRows.map Bundle.useBits).sum=(before.map ReportBundle.useCount).sum) :
    let v := host j
    let c := cell v
    let pre := bank N cell c size (g₀ c) (u₀ c) (supply q c)
    let base := siteBase N cell c siteID size ⟨v,rfl⟩
    let input := inputWords N edgeID portID v (pathEdges slot path₀ v) (fun f => ports f.val) ∘ Fin.cast (state v).size
    let original := bits (rawBirth N cell siteID state raw v) ((state v).retention.readInput input)
    pre.length=out.privateWires+out.supplied →
    b₀.header.boxBase=base ∧ b₀.header.orig=(slabs j).orig ∧ b₀.header.cap=(slabs j).capReport ∧
      b₀.header.copies=mult j →
    ∀ obs, (appendRows D₀ (supplements (pre.length+l.gadgets*l.countWidth) (preRows++b₀::postRows))).guardedObservations
      (lookup (pre++out.bits))=some obs →
    SeedBirthReceipt (mult j) base (slabs j) (state v).birth b₀.factors record (lookup (pre++out.bits)) (z₀ j) l original := by
  intro v c pre base input original extent header obs accepted
  obtain ⟨window,digits⟩ := raw_birth_copy_window N cell siteID edgeID portID state host slabs mult birthWidth owners slot ports
    q raw j out.bits ((state v).retention.readInput input)
  exact SeedBirthReceipt.ofDirectory record out before after parts pre extent D₀ preRows postRows b₀ header rfl prefixCount
    accepted (z₀ j) original window digits
    (CorePassed.raw_birth_observed N cell siteID edgeID portID state host slabs mult birthWidth owners slot ports
      number tags model q raw ok v)

include ok in
/-- Obtain the receipt at any original row of the decoded stable global
directory. Its chronological neighbors and cursor follow from the original
row enumeration, also when two bundles have identical contents. -/
theorem CorePassed.groupedSeedReport {M₀ : ℕ} (origin : Fin M₀ → J) (j : Fin M₀)
    (D₀ : Directory) (source : Fin M₀ → Bundle) (record : Fin M₀ → ReportBundle)
    {l : ReportLayout} (out : ReportCell l) (width : ∀ a,(record a).useCount=(source a).useBits) :
    let v := host (origin j)
    let c := cell v
    let pre := bank N cell c size (g₀ c) (u₀ c) (supply q c)
    let base := siteBase N cell c siteID size ⟨v,rfl⟩
    let sourceRows := BundleDirectory.sourceRows (fun a => cell (host (origin a))) c.val
    let input := inputWords N edgeID portID v (pathEdges slot path₀ v) (fun f => ports f.val) ∘ Fin.cast (state v).size
    let original := bits (rawBirth N cell siteID state raw v) ((state v).retention.readInput input)
    out.bundles=sourceRows.map record → pre.length=out.privateWires+out.supplied →
    (source j).header.boxBase=base ∧ (source j).header.orig=(slabs (origin j)).orig ∧
      (source j).header.cap=(slabs (origin j)).capReport ∧ (source j).header.copies=mult (origin j) →
    ∀ obs, (appendRows D₀ (supplements (pre.length+l.gadgets*l.countWidth) (sourceRows.map source))).guardedObservations
      (lookup (pre++out.bits))=some obs →
    Nonempty (SeedBirthReceipt (mult (origin j)) base (slabs (origin j)) (state v).birth (source j).factors (record j)
      (lookup (pre++out.bits)) (z₀ (origin j)) l original) := by
  intro v c pre base order input original grouped extent header obs accepted
  have member : j ∈ order := BundleDirectory.mem_sourceRows.mpr rfl
  obtain ⟨prior,later,split⟩ := List.append_of_mem member
  have parts : out.bundles=prior.map record++record j::later.map record := by
    rw [grouped,split,List.map_append,List.map_cons]
  have sizes : ((prior.map source).map Bundle.useBits).sum=((prior.map record).map ReportBundle.useCount).sum := by
    simp only [List.map_map]
    exact congrArg List.sum (List.map_congr_left fun _ _ => (width _).symm)
  refine ⟨CorePassed.retainedReport N cell siteID edgeID portID state host slabs mult birthWidth owners slot ports number
    tags model q raw ok (origin j) D₀ (source j) out (prior.map source) (later.map source) (record j)
    (prior.map record) (later.map record) parts sizes extent header obs ?_⟩
  simpa only [split,List.map_append,List.map_cons] using accepted

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
