import OAI.Computability.BorderVNP.PackedRetainedProfileImage
import OAI.Computability.BorderVNP.CellPacketGeometryTerminalReturn
import OAI.Computability.BorderVNP.CellPacketGeometryNativePlaces
import OAI.Computability.BorderVNP.FiniteEvaluatorGeometryFieldRuntime
import OAI.Computability.BorderVNP.FiniteEvaluatorReturnedRowOperands

/-! # Field-valued private operands from a returning native terminal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.Terminal

open Crossing Shortening Shortening.PublicCapacity Packing Packing.Inherited FrozenTape CellSparse Packet
open CellAddressCircuit CellAddressPhysical CellAddresses VPVNP.VerifierNetwork ParseBatchSort LiveWords SiteWords
open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM PackedHistoryCircuit
open Packing.RoutingOutputs FiniteEvaluator RoutingISA.CellPacket RoutingISA.CellPacket.Supplement
open RoutingISA.TypedTaskBuilder

variable {s : Shape} {n C d k w t cap q J P active reserve control g digits : ℕ}
variable {X Y Z H R B Orig Saved : Type}
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype H] [Fintype R] [Fintype B] [Fintype Saved]
variable (F : Fields s.sites s.edges n C d k w (Z ⊕ Bool)) (occupied : Fin s.edges → Z ⊕ Bool) (portUsed : Fin n → Bool)
variable (boxes : Fin s.sites → List (Source.Box Orig))
variable (old : VPVNP.VerifierNetwork.Frame ((Z ⊕ Bool) ⊕ H) (FrozenTape.Pins R B t))
variable (original : Fin J → Fin s.sites) (arena stride gap desc : ℕ) (valid : Z ⊕ Bool)
local notation3 (prettyPrint := false) "fields" => FiniteFields.liveFrame (H:=H) F boxes original arena stride gap desc g digits
variable (S : FrozenTape.Schema R B)
local notation3 (prettyPrint := false) "L₀" => FinalTies.tieSchema s.edges n w
local notation3 (prettyPrint := false) "f₀" => feeds F occupied portUsed boxes old fields valid
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, ((FinalTies.tieSchema s.edges n w).tags r).length≤cap)
local notation3 (prettyPrint := false) "priv" => FiniteFields.priv (C:=C) (entries:=J) g digits
local notation3 (prettyPrint := false) "reports" => FiniteFields.rep (C:=C) (entries:=J) g digits
local notation3 (prettyPrint := false) "T₀" => template S (FinalTies.tieSchema s.edges n w) boxes sh lh priv reports
variable (hs : ∀ r, S.width r≤w) (oldKey : t≤q) (bindKey : d≤q) (siteRoom : s.sites<2^q) (keyRoom : C+1<2^k)
variable (base : Fin (roster s.sites S (FinalTies.tieSchema s.edges n w)).length → Fin (C+1))
variable (pointer : Orig → (template S (FinalTies.tieSchema s.edges n w) boxes sh lh
  (FiniteFields.priv (C:=C) (entries:=J) g digits) (FiniteFields.rep (C:=C) (entries:=J) g digits)).Fields)
variable (pad : (roster s.sites S (FinalTies.tieSchema s.edges n w)).length<2^q) (hdr : ℕ)

variable (hk : k≤w) (livePorts : Fin P → Fin n) (controls : Fin control → Fin (2^w))
variable (src : VPVNP.VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ Saved) (Z ⊕ Bool))
variable (keep : VPVNP.VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ Saved) H)
variable (aug : VPVNP.VerifierNetwork.Frame (X ⊕ Y) (Saved ⊕ Unit)) (ord : Y ≃ Fin active) (fit : active≤reserve)
variable (x : X → Bool) (word : Fin reserve → Bool) (cp : 0<C)
local notation3 (prettyPrint := false) "y₀" => Retained.branch aug ord fit x word
local notation3 (prettyPrint := false) "z₀" => src.eval y₀
local notation3 (prettyPrint := false) "h₀" => keep.eval y₀
local notation3 (prettyPrint := false) "read₀" => Sum.elim z₀ h₀
local notation3 (prettyPrint := false) "c₀" => TerminalTable.cell F cp z₀
local notation3 (prettyPrint := false) "off₀" => TerminalTable.bitStart F z₀
local notation3 (prettyPrint := false) "box₀" => TerminalTable.boxStart F boxes cp z₀
local notation3 (prettyPrint := false) "field₀" => fun (i : Fin (roster s.sites S (FinalTies.tieSchema s.edges n w)).length) =>
  scalarArgs (cap := cap) S (FinalTies.tieSchema s.edges n w) (old.eval read₀) ((f₀).binding.eval read₀) off₀ box₀
    ((roster s.sites S (FinalTies.tieSchema s.edges n w)).get i)
local notation3 (prettyPrint := false) "G₀" => directory S (FinalTies.tieSchema s.edges n w) boxes sh lh priv reports
  ((f₀).arguments read₀) (old.eval read₀) ((f₀).binding.eval read₀) c₀ off₀ box₀

variable {D : ℕ} {Port : Type} [Fintype Port] {bits : Port → ℕ} (N : Network D Port bits)
variable (rows : Rows s N) (ports : Port ↪ Fin n) (A : Type) (semantic : N.Site → A) (number : A ≃ Fin C) (state : N.Site → Site)
local notation3 (prettyPrint := false) "cell" => number ∘ semantic
variable {W : ℕ} {pub : Arg → Word W} {mac : TeamOpcode.Macros W 8} {bank after : RoutingISA.Bank W}
variable {mem result : Memory W} {fresh dest clock : ℕ} {es : List (TeamRAM.Event W)}
local notation3 (prettyPrint := false) "packetAt" => Retained.packetBase dest s.edges C J P control
local notation3 (prettyPrint := false) "emit₀" => (f₀).ordered S (FinalTies.tieSchema s.edges n w) boxes sh lh priv reports oldKey bindKey siteRoom
  (Nat.lt_trans (Nat.lt_succ_self C) keyRoom) hs (fun _ => le_rfl) base pointer pad packetAt hdr

/-- Extend a physical real-or-spare cell table to the native natural-numbered scan. -/
def placeAt {O : Type} (p : Fin (C+1) → Placed O) (j : ℕ) : Placed O :=
  p ⟨min j C,Nat.lt_succ_of_le (min_le_right ..)⟩

private theorem placeAt_slot {O : Type} (p : Fin (C+1) → Placed O) (c : Fin (C+1)) :
    placeAt p c.val = p c :=
  congrArg p (Fin.ext (Nat.min_eq_left (Nat.le_of_lt_succ c.isLt)))

set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

private theorem reported_operands {ram : ℕ → ℕ} (fs : Orig → List Factor)
    (physical : Represents N cell (fun v => (state v).size) rows.site rows.edge ports F z₀)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c < 2^w)
(slot : Orig → ℕ) (address : ∀ j, (T₀).arguments ((f₀).arguments read₀) field₀ (pointer j)=slot j)
    (externalBase scratch burst : Fin (C+1) → ℕ) (external : Fin (C+1) → List Bool)
    (published : Published G₀ (T₀).publicDepth (T₀).chunkDepth packetAt hdr pointer
      ((T₀).arguments ((f₀).arguments read₀) field₀) ram)
    (canonical : ∀ c : Fin C, ∀ sl pb db eb sb bb ext,
      ((G₀).placed c.castSucc hdr sl fs pb db eb sb bb ext).directory =
        FinalCell.directory (fun j => (c₀ j).val) N (fun v => (cell v).val) rows.site rows.edge ports state
          c.val ((G₀).reports c.castSucc)) :
    ∃ fitPublic fitDescriptors,
      let places := atRanges (p := (T₀).publicDepth) (d := (T₀).chunkDepth) (dest := packetAt) (H := hdr) G₀ pointer fitPublic fitDescriptors
        ram slot fs externalBase scratch burst external
      (∀ j, CellMemory (places j) ((places j).publicBase+
          ((Supplement.prefixParts (places j)).flatMap Source.Part.publicBuffer).length)
        (descriptorBank packetAt (T₀).publicDepth+ram (descriptorBank packetAt (T₀).publicDepth+
          (2^(T₀).chunkDepth+(Markers.stop fitDescriptors j).val))) ram) ∧
      ∀ (l : CellControlRows.Layout) (source : ℕ → ℕ) (geom : ℕ → ℕ) (i : ℕ) (c : A),
        globalCell l.toLayout source i = (number c).val →
        (Merged.site N semantic c rows.site rows.edge ports state).size+digits*g ≤ 2^w →
        let p := (Batch.produced l source (placeAt places) geom (fun _ => []) i).placed
        let logical := Merged.site N semantic c rows.site rows.edge ports state
        p.directory = Placement.packet N semantic c rows.site rows.edge ports state (Reports.fields logical.size g digits) ∧
          p.privateWires = logical.work := by
  obtain ⟨fitPublic,fitDescriptors,real,memory⟩ := published.places G₀ pointer ram
    slot fs externalBase scratch burst external address
  refine ⟨fitPublic,fitDescriptors,?_⟩
  intro places
  refine ⟨memory,?_⟩
  intro l source geom i c owned countFit p logical
  have shape : TypedBatch.SourceShape (fun c : Fin (C+1) => placeAt places c.val) G₀ := by
    simpa only [placeAt_slot] using real
  have factors : (placeAt places (number c).val).factors=fs := by
    rw [show (number c).val = (number c).castSucc.val from rfl,placeAt_slot]
    rfl
  have actual := canonical (number c) (fun _ => 0) 0 0 0 0 0 []
  have numeric := FiniteFields.directory_named F boxes original arena stride gap desc g digits N semantic number state
    rows.site rows.edge ports physical sizeFit S (L₀) sh lh (old.eval read₀) ((f₀).binding.eval read₀)
    c₀ off₀ box₀ c countFit
  have args : (f₀).arguments read₀ = FiniteFields.operand F boxes original arena stride gap desc g digits (x:=z₀) := by
    funext v
    apply congrArg (ParseBatchSort.value (w:=w))
    funext bit
    exact FiniteFields.liveFrame_eval F boxes original arena stride gap desc g digits z₀ h₀ (v,bit)
  apply Merged.produced_row_operands N semantic number rows.site rows.edge ports state c₀
    (fun v => TerminalTable.cell_live F N cell rows.site rows.edge ports state cp physical v)
    G₀ (placeAt places) shape fs g digits c l source geom i owned factors actual
  rw [args]
  exact numeric

/-- The real geometry subroutine fixes the marker memory and launch operands of every compact finite-field row. -/
theorem returned_finite_operands (fs : Orig → List Factor)
    (hist : S.Image (old.eval read₀) (rows.site.trans Fin.valEmbedding) state)
    (physical : Represents N cell (fun v => (state v).size) rows.site rows.edge ports F z₀)
    (resolved : ∀ i, (boxes i).map (Source.factors fs) = FinalCell.slots rows.site (fun v => (state v).boxes) i)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c < 2^w)
    (incoming : ∀ v, (state v).incoming=Inherited.incoming N v) (ordinal : ∀ i, (F.sites i).val=i.val)
    (live : ∀ i, z₀ (occupied i)=true ↔ i∈Set.range rows.edge)
    (used : ∀ i, portUsed i=true ↔ i∈Set.range ports)
    (wide : 2^(T₀).recordDepth≤2^(w+k)) (boxRoom : (∑ i, (boxes i).length)<2^w)
    (rowRoom : S.rows.length+(L₀).rows.length<2^w) (capRoom : cap<2^w) (three : 3<2^w)
    (known : ∀ i n, n∈boxWords (boxes i) → n<2^w) (reportRows : ∀ c, (reports c).length<2^w)
    (vectors : ∀ c r, r∈reports c → r.length<2^w) (limit : Fin C → ℕ) (limitRoom : ∀ c, limit c<2^w)
    (bounds : ∀ c : Fin C, ∀ r ∈ (FinalCell.directory (fun i => (c₀ i).val) N (fun v => (cell v).val)
      rows.site rows.edge ports state c.val ((G₀).reports c.castSucc)).records, RecordFields r (limit c))
    (sourceRoom : packetAt+2^(T₀).publicDepth<2^w) (descRoom : 2^(T₀).chunkDepth≤2^w) (header : hdr<2^w)
    (width : w≤W) (run : GeometryReturn pub mac bank mem fresh dest clock
      (emittedWords aug ord fit (Retained.emitter F hk original livePorts (Retained.privateControls F original controls emit₀)
        src keep) x word) es after result)
    (slot : Orig → ℕ) (address : ∀ j, (T₀).arguments ((f₀).arguments read₀) field₀ (pointer j)=slot j)
    (externalBase scratch burst : Fin (C+1) → ℕ) (external : Fin (C+1) → List Bool) :
    ∃ fitPublic fitDescriptors,
      let places := atRanges (p := (T₀).publicDepth) (d := (T₀).chunkDepth) (dest := packetAt) (H := hdr) G₀ pointer fitPublic fitDescriptors
        (readings result) slot fs externalBase scratch burst external
      (∀ j, CellMemory (places j) ((places j).publicBase+
          ((Supplement.prefixParts (places j)).flatMap Source.Part.publicBuffer).length)
        (descriptorBank packetAt (T₀).publicDepth+readings result (descriptorBank packetAt (T₀).publicDepth+
          (2^(T₀).chunkDepth+(Markers.stop fitDescriptors j).val))) (readings result)) ∧
      ∀ (l : CellControlRows.Layout) (source : ℕ → ℕ) (geom : ℕ → ℕ) (i : ℕ) (c : A),
        globalCell l.toLayout source i = (number c).val →
        (Merged.site N semantic c rows.site rows.edge ports state).size+digits*g ≤ 2^w →
        let p := (Batch.produced l source (placeAt places) geom (fun _ => []) i).placed
        let logical := Merged.site N semantic c rows.site rows.edge ports state
        p.directory = Placement.packet N semantic c rows.site rows.edge ports state (Reports.fields logical.size g digits) ∧
          p.privateWires = logical.work := by
  have receive := returned F occupied portUsed boxes old fields valid S sh lh priv reports hs oldKey bindKey siteRoom
    keyRoom base pointer pad hdr hk original livePorts controls src keep aug ord fit x word cp N rows ports cell state fs
    hist physical resolved sizeFit incoming ordinal live used wide boxRoom rowRoom capRoom three known reportRows vectors limit
    limitRoom bounds sourceRoom descRoom header width run
  exact reported_operands (F := F) (occupied := occupied) (portUsed := portUsed) (boxes := boxes)
    (old := old) (original := original) (arena := arena) (stride := stride) (gap := gap) (desc := desc)
    (valid := valid) (S := S) (sh := sh) (lh := lh) (pointer := pointer) (hdr := hdr)
    (src := src) (keep := keep) (aug := aug) (ord := ord) (fit := fit) (x := x) (word := word) (cp := cp)
    (N := N) (rows := rows) (ports := ports) (A := A) (semantic := semantic) (number := number) (state := state)
    fs physical sizeFit slot address externalBase scratch burst external receive.2.1 receive.2.2

/-- The complete front-receipt words determine the same finite-field launch data. -/
theorem returned_finite_operands_of_words (fs : Orig → List Factor)
    (hist : S.Image (old.eval read₀) (rows.site.trans Fin.valEmbedding) state)
    (physical : Represents N cell (fun v => (state v).size) rows.site rows.edge ports F z₀)
    (resolved : ∀ i, (boxes i).map (Source.factors fs) = FinalCell.slots rows.site (fun v => (state v).boxes) i)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c < 2^w)
    (incoming : ∀ v, (state v).incoming=Inherited.incoming N v) (ordinal : ∀ i, (F.sites i).val=i.val)
    (live : ∀ i, z₀ (occupied i)=true ↔ i∈Set.range rows.edge)
    (used : ∀ i, portUsed i=true ↔ i∈Set.range ports)
    (wide : 2^(T₀).recordDepth≤2^(w+k)) (boxRoom : (∑ i, (boxes i).length)<2^w)
    (rowRoom : S.rows.length+(L₀).rows.length<2^w) (capRoom : cap<2^w) (three : 3<2^w)
    (known : ∀ i n, n∈boxWords (boxes i) → n<2^w) (reportRows : ∀ c, (reports c).length<2^w)
    (vectors : ∀ c r, r∈reports c → r.length<2^w) (limit : Fin C → ℕ) (limitRoom : ∀ c, limit c<2^w)
    (bounds : ∀ c : Fin C, ∀ r ∈ (FinalCell.directory (fun i => (c₀ i).val) N (fun v => (cell v).val)
      rows.site rows.edge ports state c.val ((G₀).reports c.castSucc)).records, RecordFields r (limit c))
    (sourceRoom : packetAt+2^(T₀).publicDepth<2^w) (descRoom : 2^(T₀).chunkDepth≤2^w) (header : hdr<2^w)
    (width : w≤W)
    (constants : ∀ bit, src.eval y₀ (.inr bit)=bit)
    (front : ∀ i, readings result (dest+i.val) = ParseBatchSort.value (fun j =>
      (Retained.emitter F hk original livePorts (Retained.privateControls F original controls emit₀)
        src keep).eval y₀ (i,j)))
    (slot : Orig → ℕ) (address : ∀ j, (T₀).arguments ((f₀).arguments read₀) field₀ (pointer j)=slot j)
    (externalBase scratch burst : Fin (C+1) → ℕ) (external : Fin (C+1) → List Bool) :
    ∃ fitPublic fitDescriptors,
      let places := atRanges (p := (T₀).publicDepth) (d := (T₀).chunkDepth) (dest := packetAt) (H := hdr) G₀ pointer fitPublic fitDescriptors
        (readings result) slot fs externalBase scratch burst external
      (∀ j, CellMemory (places j) ((places j).publicBase+
          ((Supplement.prefixParts (places j)).flatMap Source.Part.publicBuffer).length)
        (descriptorBank packetAt (T₀).publicDepth+readings result (descriptorBank packetAt (T₀).publicDepth+
          (2^(T₀).chunkDepth+(Markers.stop fitDescriptors j).val))) (readings result)) ∧
      ∀ (l : CellControlRows.Layout) (source : ℕ → ℕ) (geom : ℕ → ℕ) (i : ℕ) (c : A),
        globalCell l.toLayout source i = (number c).val →
        (Merged.site N semantic c rows.site rows.edge ports state).size+digits*g ≤ 2^w →
        let p := (Batch.produced l source (placeAt places) geom (fun _ => []) i).placed
        let logical := Merged.site N semantic c rows.site rows.edge ports state
        p.directory = Placement.packet N semantic c rows.site rows.edge ports state (Reports.fields logical.size g digits) ∧
          p.privateWires = logical.work := by
  have sectionWords := Retained.packet_image_of_words F hk width original livePorts controls emit₀ src keep
    y₀ constants dest result front
  have receive := published_words F occupied portUsed boxes old fields valid S sh lh priv reports hs oldKey bindKey
    siteRoom keyRoom base pointer pad hdr (control := control) src keep aug ord fit x word cp N rows ports cell state
    fs hist physical resolved sizeFit incoming ordinal live used wide boxRoom rowRoom capRoom three known reportRows
    vectors limit limitRoom bounds sourceRoom descRoom header sectionWords.2.2.2
  exact reported_operands (F := F) (occupied := occupied) (portUsed := portUsed) (boxes := boxes)
    (old := old) (original := original) (arena := arena) (stride := stride) (gap := gap) (desc := desc)
    (valid := valid) (S := S) (sh := sh) (lh := lh) (pointer := pointer) (hdr := hdr)
    (src := src) (keep := keep) (aug := aug) (ord := ord) (fit := fit) (x := x) (word := word) (cp := cp)
    (N := N) (rows := rows) (ports := ports) (A := A) (semantic := semantic) (number := number) (state := state)
    fs physical sizeFit slot address externalBase scratch burst external receive.1 receive.2

/-- The returned packet words in an arbitrary native memory image determine all field launch operands. -/
theorem returned_finite_operands_in_ram (fs : Orig → List Factor)
    (hist : S.Image (old.eval read₀) (rows.site.trans Fin.valEmbedding) state)
    (physical : Represents N cell (fun v => (state v).size) rows.site rows.edge ports F z₀)
    (resolved : ∀ i, (boxes i).map (Source.factors fs) = FinalCell.slots rows.site (fun v => (state v).boxes) i)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c < 2^w)
    (incoming : ∀ v, (state v).incoming=Inherited.incoming N v) (ordinal : ∀ i, (F.sites i).val=i.val)
    (live : ∀ i, z₀ (occupied i)=true ↔ i∈Set.range rows.edge)
    (used : ∀ i, portUsed i=true ↔ i∈Set.range ports)
    (wide : 2^(T₀).recordDepth≤2^(w+k)) (boxRoom : (∑ i, (boxes i).length)<2^w)
    (rowRoom : S.rows.length+(L₀).rows.length<2^w) (capRoom : cap<2^w) (three : 3<2^w)
    (known : ∀ i n, n∈boxWords (boxes i) → n<2^w) (reportRows : ∀ c, (reports c).length<2^w)
    (vectors : ∀ c r, r∈reports c → r.length<2^w) (limit : Fin C → ℕ) (limitRoom : ∀ c, limit c<2^w)
    (bounds : ∀ c : Fin C, ∀ r ∈ (FinalCell.directory (fun i => (c₀ i).val) N (fun v => (cell v).val)
      rows.site rows.edge ports state c.val ((G₀).reports c.castSucc)).records, RecordFields r (limit c))
    (sourceRoom : packetAt+2^(T₀).publicDepth<2^w) (descRoom : 2^(T₀).chunkDepth≤2^w) (header : hdr<2^w)
    (ram : ℕ → ℕ) (packetWords : ∀ i : Fin (Total (T₀).publicDepth (T₀).chunkDepth), ram (packetAt+i.val) =
      ParseBatchSort.value (fun j => (emit₀).eval read₀ (.inl (i,j))))
    (slot : Orig → ℕ) (address : ∀ j, (T₀).arguments ((f₀).arguments read₀) field₀ (pointer j)=slot j)
    (externalBase scratch burst : Fin (C+1) → ℕ) (external : Fin (C+1) → List Bool) :
    ∃ fitPublic fitDescriptors,
      let places := atRanges (p := (T₀).publicDepth) (d := (T₀).chunkDepth) (dest := packetAt) (H := hdr) G₀ pointer fitPublic fitDescriptors
        ram slot fs externalBase scratch burst external
      (∀ j, CellMemory (places j) ((places j).publicBase+
          ((Supplement.prefixParts (places j)).flatMap Source.Part.publicBuffer).length)
        (descriptorBank packetAt (T₀).publicDepth+ram (descriptorBank packetAt (T₀).publicDepth+
          (2^(T₀).chunkDepth+(Markers.stop fitDescriptors j).val))) ram) ∧
      ∀ (l : CellControlRows.Layout) (source : ℕ → ℕ) (geom : ℕ → ℕ) (i : ℕ) (c : A),
        globalCell l.toLayout source i = (number c).val →
        (Merged.site N semantic c rows.site rows.edge ports state).size+digits*g ≤ 2^w →
        let p := (Batch.produced l source (placeAt places) geom (fun _ => []) i).placed
        let logical := Merged.site N semantic c rows.site rows.edge ports state
        p.directory = Placement.packet N semantic c rows.site rows.edge ports state (Reports.fields logical.size g digits) ∧
          p.privateWires = logical.work := by
  have receive := published_ram F occupied portUsed boxes old fields valid S sh lh priv reports hs oldKey bindKey
    siteRoom keyRoom base pointer pad hdr (control := control) src keep aug ord fit x word cp N rows ports cell state
    fs hist physical resolved sizeFit incoming ordinal live used wide boxRoom rowRoom capRoom three known reportRows
    vectors limit limitRoom bounds sourceRoom descRoom header ram packetWords
  exact reported_operands (F := F) (occupied := occupied) (portUsed := portUsed) (boxes := boxes)
    (old := old) (original := original) (arena := arena) (stride := stride) (gap := gap) (desc := desc)
    (valid := valid) (S := S) (sh := sh) (lh := lh) (pointer := pointer) (hdr := hdr)
    (src := src) (keep := keep) (aug := aug) (ord := ord) (fit := fit) (x := x) (word := word) (cp := cp)
    (N := N) (rows := rows) (ports := ports) (A := A) (semantic := semantic) (number := number) (state := state)
    fs physical sizeFit slot address externalBase scratch burst external receive.1 receive.2

/-- After placement uses the scratch prefix, the retained packet suffix still determines each field-valued launch. -/
theorem returned_finite_operands_of_packet_words (fs : Orig → List Factor)
    (hist : S.Image (old.eval read₀) (rows.site.trans Fin.valEmbedding) state)
    (physical : Represents N cell (fun v => (state v).size) rows.site rows.edge ports F z₀)
    (resolved : ∀ i, (boxes i).map (Source.factors fs) = FinalCell.slots rows.site (fun v => (state v).boxes) i)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c < 2^w)
    (incoming : ∀ v, (state v).incoming=Inherited.incoming N v) (ordinal : ∀ i, (F.sites i).val=i.val)
    (live : ∀ i, z₀ (occupied i)=true ↔ i∈Set.range rows.edge)
    (used : ∀ i, portUsed i=true ↔ i∈Set.range ports)
    (wide : 2^(T₀).recordDepth≤2^(w+k)) (boxRoom : (∑ i, (boxes i).length)<2^w)
    (rowRoom : S.rows.length+(L₀).rows.length<2^w) (capRoom : cap<2^w) (three : 3<2^w)
    (known : ∀ i n, n∈boxWords (boxes i) → n<2^w) (reportRows : ∀ c, (reports c).length<2^w)
    (vectors : ∀ c r, r∈reports c → r.length<2^w) (limit : Fin C → ℕ) (limitRoom : ∀ c, limit c<2^w)
    (bounds : ∀ c : Fin C, ∀ r ∈ (FinalCell.directory (fun i => (c₀ i).val) N (fun v => (cell v).val)
      rows.site rows.edge ports state c.val ((G₀).reports c.castSucc)).records, RecordFields r (limit c))
    (sourceRoom : packetAt+2^(T₀).publicDepth<2^w) (descRoom : 2^(T₀).chunkDepth≤2^w) (header : hdr<2^w)
    (packetWords : ∀ i : Fin (Total (T₀).publicDepth (T₀).chunkDepth), readings result (packetAt+i.val) =
      ParseBatchSort.value (fun j => (emit₀).eval read₀ (.inl (i,j))))
    (slot : Orig → ℕ) (address : ∀ j, (T₀).arguments ((f₀).arguments read₀) field₀ (pointer j)=slot j)
    (externalBase scratch burst : Fin (C+1) → ℕ) (external : Fin (C+1) → List Bool) :
    ∃ fitPublic fitDescriptors,
      let places := atRanges (p := (T₀).publicDepth) (d := (T₀).chunkDepth) (dest := packetAt) (H := hdr) G₀ pointer fitPublic fitDescriptors
        (readings result) slot fs externalBase scratch burst external
      (∀ j, CellMemory (places j) ((places j).publicBase+
          ((Supplement.prefixParts (places j)).flatMap Source.Part.publicBuffer).length)
        (descriptorBank packetAt (T₀).publicDepth+readings result (descriptorBank packetAt (T₀).publicDepth+
          (2^(T₀).chunkDepth+(Markers.stop fitDescriptors j).val))) (readings result)) ∧
      ∀ (l : CellControlRows.Layout) (source : ℕ → ℕ) (geom : ℕ → ℕ) (i : ℕ) (c : A),
        globalCell l.toLayout source i = (number c).val →
        (Merged.site N semantic c rows.site rows.edge ports state).size+digits*g ≤ 2^w →
        let p := (Batch.produced l source (placeAt places) geom (fun _ => []) i).placed
        let logical := Merged.site N semantic c rows.site rows.edge ports state
        p.directory = Placement.packet N semantic c rows.site rows.edge ports state (Reports.fields logical.size g digits) ∧
          p.privateWires = logical.work :=
  returned_finite_operands_in_ram F occupied portUsed boxes old original arena stride gap desc valid S sh lh hs
    oldKey bindKey siteRoom keyRoom base pointer pad hdr (control:=control) src keep aug ord fit x word cp N rows
    ports A semantic number state fs hist physical resolved sizeFit incoming ordinal live used wide boxRoom rowRoom
    capRoom three known reportRows vectors limit limitRoom bounds sourceRoom descRoom header (readings result) packetWords
    slot address externalBase scratch burst external

end CellPacketGeometry.History.Native.Terminal

end BorderVNP
end Computability
end OAI
