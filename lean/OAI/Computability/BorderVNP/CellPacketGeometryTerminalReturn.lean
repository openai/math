import OAI.Computability.BorderVNP.CellPacketGeometryTerminalFeeds
import OAI.Computability.BorderVNP.PackedTerminalAugmentedPins

/-! # The single retained terminal execution publishes every actual cell packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.Terminal

open Crossing Shortening Shortening.PublicCapacity Packing Packing.Inherited FrozenTape CellSparse Packet
open CellAddressCircuit CellAddressPhysical CellAddresses VPVNP.VerifierNetwork ParseBatchSort LiveWords SiteWords
open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM PackedHistoryCircuit
open Packing.RoutingOutputs

variable {s : Shape} {n C d k w t cap q J P active reserve control : ℕ}
variable {X Y Z H R B E Orig Saved : Type}
variable [Fintype X] [Fintype Y] [Fintype Z] [Fintype H] [Fintype R] [Fintype B] [Fintype E] [Fintype Saved]
variable (F : Fields s.sites s.edges n C d k w (Z ⊕ Bool)) (occupied : Fin s.edges → Z ⊕ Bool) (portUsed : Fin n → Bool)
variable (boxes : Fin s.sites → List (Source.Box Orig))
variable (old : VPVNP.VerifierNetwork.Frame ((Z ⊕ Bool) ⊕ H) (FrozenTape.Pins R B t))
variable (fields : VPVNP.VerifierNetwork.Frame ((Z ⊕ Bool) ⊕ H) (E × Fin w)) (valid : Z ⊕ Bool)
variable (S : FrozenTape.Schema R B)
local notation3 "L₀" => FinalTies.tieSchema s.edges n w
local notation3 "f₀" => feeds F occupied portUsed boxes old fields valid
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, ((FinalTies.tieSchema s.edges n w).tags r).length≤cap)
variable (priv : Fin (C+1) → E) (reports : Fin (C+1) → List (List E))
local notation3 (prettyPrint := false) "T₀" => template S (FinalTies.tieSchema s.edges n w) boxes sh lh priv reports
variable (hs : ∀ r, S.width r≤w) (oldKey : t≤q) (bindKey : d≤q) (siteRoom : s.sites<2^q) (keyRoom : C+1<2^k)
variable (base : Fin (roster s.sites S (FinalTies.tieSchema s.edges n w)).length → Fin (C+1))
variable (pointer : Orig → (template S (FinalTies.tieSchema s.edges n w) boxes sh lh priv reports).Fields)
variable (pad : (roster s.sites S (FinalTies.tieSchema s.edges n w)).length<2^q) (hdr : ℕ)

variable (hk : k≤w) (original : Fin J → Fin s.sites) (livePorts : Fin P → Fin n) (controls : Fin control → Fin (2^w))
variable (src : VPVNP.VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ Saved) (Z ⊕ Bool))
variable (keep : VPVNP.VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ Saved) H)
variable (aug : VPVNP.VerifierNetwork.Frame (X ⊕ Y) (Saved ⊕ Unit)) (ord : Y ≃ Fin active) (fit : active≤reserve)
variable (x : X → Bool) (word : Fin reserve → Bool) (cp : 0<C)
local notation3 "y₀" => Retained.branch aug ord fit x word
local notation3 "z₀" => src.eval y₀
local notation3 "h₀" => keep.eval y₀
local notation3 "read₀" => Sum.elim z₀ h₀
local notation3 "c₀" => TerminalTable.cell F cp z₀
local notation3 "off₀" => TerminalTable.bitStart F z₀
local notation3 "box₀" => TerminalTable.boxStart F boxes cp z₀
local notation3 "field₀" => fun (i : Fin (roster s.sites S (FinalTies.tieSchema s.edges n w)).length) =>
  scalarArgs (cap := cap) S (FinalTies.tieSchema s.edges n w) (old.eval read₀) ((f₀).binding.eval read₀) off₀ box₀
    ((roster s.sites S (FinalTies.tieSchema s.edges n w)).get i)
local notation3 (prettyPrint := false) "G₀" => directory S (FinalTies.tieSchema s.edges n w) boxes sh lh priv reports
  ((f₀).arguments read₀) (old.eval read₀) ((f₀).binding.eval read₀) c₀ off₀ box₀

variable {D : ℕ} {Port : Type} [Fintype Port] {bits : Port → ℕ} (N : Network D Port bits)
variable (rows : Rows s N) (ports : Port ↪ Fin n) (cell : N.Site → Fin C) (state : N.Site → Site)
variable {W : ℕ} {pub : Arg → Word W} {mac : TeamOpcode.Macros W 8} {bank after : RoutingISA.Bank W}
variable {mem result : Memory W} {fresh dest clock : ℕ} {es : List (TeamRAM.Event W)}
local notation3 "packetAt" => Retained.packetBase dest s.edges C J P control
local notation3 (prettyPrint := false) "emit₀" => (f₀).ordered S (FinalTies.tieSchema s.edges n w) boxes sh lh priv reports oldKey bindKey siteRoom
  (Nat.lt_trans (Nat.lt_succ_self C) keyRoom) hs (fun _ => le_rfl) base pointer pad packetAt hdr

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
/-- The semantic memory image at this stage is determined by exactly its returned packet words. -/
theorem published_ram (fs : Orig → List Factor)
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
    (ram : ℕ → ℕ) (words : ∀ i : Fin (Total (T₀).publicDepth (T₀).chunkDepth), ram (packetAt+i.val) =
      value (fun j => (emit₀).eval read₀ (.inl (i,j)))) :
    Published (G₀) (T₀).publicDepth (T₀).chunkDepth packetAt hdr pointer ((T₀).arguments ((f₀).arguments read₀) field₀)
      ram ∧
    ∀ c : Fin C, ∀ slot publicBase descBase extBase scratch burst external,
      ((G₀).placed c.castSucc hdr slot fs publicBase descBase extBase scratch burst external).directory =
        FinalCell.directory (fun i => (c₀ i).val) N (fun v => (cell v).val) rows.site rows.edge ports state c.val
          ((G₀).reports c.castSucc) := by
  have last := bindings F occupied portUsed boxes old fields valid z₀ h₀ N rows ports cell state physical sizeFit
    incoming (by omega) live used ordinal
  have room c : (BankBoxOrdinal.table (fun j => (c₀ j).val) boxes c).length < 2^w := by
    rw [BankBoxOrdinal.table_length]
    exact (Finset.sum_le_sum (fun i _ => by split <;> simp)).trans_lt boxRoom
  obtain ⟨tc,ts⟩ := table_values F occupied portUsed boxes old fields valid z₀ h₀ cp room
  obtain ⟨bits,ids⟩ := starts F boxes z₀ cp N rows ports cell state physical sizeFit fs resolved
  constructor
  · exact (f₀).buffers S (L₀) boxes sh lh priv reports read₀ c₀ off₀ box₀ N (fun v => (cell v).val)
      rows.site rows.edge ports state oldKey bindKey siteRoom keyRoom hs (fun _ => le_rfl) base pointer pad packetAt hdr
      fs hist last resolved bits ids tc ts wide boxRoom rowRoom capRoom three known reportRows vectors limit limitRoom
      bounds sourceRoom descRoom header _ words
  · intro c slot pb db eb sb bb ext
    exact placed_directory S (L₀) boxes sh lh priv reports ((f₀).arguments read₀) (old.eval read₀) ((f₀).binding.eval read₀)
      c₀ off₀ box₀ N (fun v => (cell v).val) rows.site rows.edge ports state c hdr slot fs pb db eb sb bb ext
      hist last resolved bits ids

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
/-- The contiguous packet result words identify every descriptor and every
real cell's network directory. This also applies after a longer native
preparation whose RAM contains these same words. -/
theorem published_words (fs : Orig → List Factor)
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
    (words : ∀ i : Fin (Total (T₀).publicDepth (T₀).chunkDepth), readings result (packetAt+i.val) =
      value (fun j => (emit₀).eval read₀ (.inl (i,j)))) :
    Published (G₀) (T₀).publicDepth (T₀).chunkDepth packetAt hdr pointer ((T₀).arguments ((f₀).arguments read₀) field₀)
      (readings result) ∧
    ∀ c : Fin C, ∀ slot publicBase descBase extBase scratch burst external,
      ((G₀).placed c.castSucc hdr slot fs publicBase descBase extBase scratch burst external).directory =
        FinalCell.directory (fun i => (c₀ i).val) N (fun v => (cell v).val) rows.site rows.edge ports state c.val
          ((G₀).reports c.castSucc) :=
  published_ram F occupied portUsed boxes old fields valid S sh lh priv reports hs oldKey bindKey
    siteRoom keyRoom base pointer pad hdr (control:=control) src keep aug ord fit x word cp N rows ports cell state
    fs hist physical resolved sizeFit incoming ordinal live used wide boxRoom rowRoom capRoom three known
    reportRows vectors limit limitRoom bounds sourceRoom descRoom header (readings result) words

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
/-- For the same native trace, expose the routing image and all per-cell packet
buffers, with exact identification of each real packet's network directory. -/
theorem returned (fs : Orig → List Factor)
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
        src keep) x word) es after result) :
    Image F original livePorts z₀ dest (readings result) ∧
    Published (G₀) (T₀).publicDepth (T₀).chunkDepth packetAt hdr pointer ((T₀).arguments ((f₀).arguments read₀) field₀)
      (readings result) ∧
    ∀ c : Fin C, ∀ slot publicBase descBase extBase scratch burst external,
      ((G₀).placed c.castSucc hdr slot fs publicBase descBase extBase scratch burst external).directory =
        FinalCell.directory (fun i => (c₀ i).val) N (fun v => (cell v).val) rows.site rows.edge ports state c.val
          ((G₀).reports c.castSucc) := by
  obtain ⟨img,words⟩ := Retained.packet_return hk original livePorts keep aug ord fit x word F controls emit₀ src width run
  refine ⟨img,?_⟩
  exact published_words F occupied portUsed boxes old fields valid S sh lh priv reports hs oldKey bindKey siteRoom
    keyRoom base pointer pad hdr (control := control) src keep aug ord fit x word cp N rows ports cell state fs hist physical
    resolved sizeFit incoming ordinal live used wide boxRoom rowRoom capRoom three known reportRows vectors limit limitRoom
    bounds sourceRoom descRoom header words

end CellPacketGeometry.History.Native.Terminal

end BorderVNP
end Computability
end OAI
