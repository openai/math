import OAI.Computability.BorderVNP.CellPacketGeometryTerminalReturn
import OAI.Computability.BorderVNP.PackedRetainedProfileImage
import OAI.Computability.BorderVNP.PackedHistoryReservedPaths

/-! # Cell packets and all control words on a complete native profile return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator

/-- The actual output memory of any returning pin-and-geometry path contains
the declared packet words. The proof also covers words on which acceptance is
discovered only by observing a return. -/
theorem ProfilePaths.words_of_return {w k o time dest : ℕ} {body : Code} {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {bank : Bank w} {mem : Memory w} {ok : Prop} {words : Fin o → ℕ}
    {resident : (Fin k → Bool) → Memory w → Prop}
    (paths : ProfilePaths body k pub mac bank mem ok time dest words resident)
    (run : Returns body pub mac bank mem) :
    ∀ i, readings run.val.2.2 (dest+i.val) = words i := by
  obtain ⟨p,h⟩ := paths.outputs (paths.passes.mp ⟨run⟩)
  obtain ⟨g,rfl⟩ := p.surjective run
  exact (h g).2.2.2

end PackedHistoryCircuit

namespace CellPacketGeometry.History.Native.Terminal

open Crossing Shortening Shortening.PublicCapacity Packing Packing.Inherited FrozenTape CellSparse Packet
open CellAddressCircuit CellAddressPhysical CellAddresses VPVNP.VerifierNetwork ParseBatchSort LiveWords SiteWords
open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM PackedHistoryCircuit
open Packing.RoutingOutputs VPVNP RoutingISA.Evaluator

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
/-- Full positive preparations, including any fresh pin choices, expose the
cell assignments, routing arrays, declared control operands, every public
packet word and every opaque descriptor reference at their actual RAM
addresses. This applies before subsequent private cells are evaluated. -/
theorem prepared_packet (fs : Orig → List Factor)
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
    (width : w≤W) (constants : ∀ bit, src.eval y₀ (.inr bit) = bit)
    {body : Code} {guess time : ℕ} {ok : Prop} {resident : (Fin guess → Bool) → Memory W → Prop}
    (paths : ProfilePaths body guess pub mac bank mem ok time dest
      (emittedWords aug ord fit (Retained.emitter F hk original livePorts (Retained.privateControls F original controls emit₀)
        src keep) x word) resident)
    (run : Returns body pub mac bank mem) :
    let out := readings run.val.2.2
    Image F original livePorts z₀ dest out ∧
    (∀ i : Fin (C+(J+C)), out (dest+s.edges*3+RoutingOutputs.count s.edges C J P+i.val) =
      value (fun j => (privateViews F original).eval z₀ (i,j))) ∧
    (∀ i, out (controlsBase dest s.edges C J P+i.val) = (controls i).val) ∧
    Published (G₀) (T₀).publicDepth (T₀).chunkDepth packetAt hdr pointer ((T₀).arguments ((f₀).arguments read₀) field₀)
      out ∧
    ∀ c : Fin C, ∀ slot publicBase descBase extBase scratch burst external,
      ((G₀).placed c.castSucc hdr slot fs publicBase descBase extBase scratch burst external).directory =
        FinalCell.directory (fun i => (c₀ i).val) N (fun v => (cell v).val) rows.site rows.edge ports state c.val
          ((G₀).reports c.castSucc) := by
  intro out
  have wordImage := paths.words_of_return run
  obtain ⟨routing,owners,ctl,bytes⟩ := Retained.packet_image_of_words F hk width original livePorts controls emit₀ src keep
    y₀ constants dest run.val.2.2 wordImage
  refine ⟨routing,owners,ctl,?_⟩
  exact published_words F occupied portUsed boxes old fields valid S sh lh priv reports hs oldKey bindKey siteRoom
    keyRoom base pointer pad hdr (control := control) src keep aug ord fit x word cp N rows ports cell state fs hist physical
    resolved sizeFit incoming ordinal live used wide boxRoom rowRoom capRoom three known reportRows vectors limit limitRoom
    bounds sourceRoom descRoom header bytes

end CellPacketGeometry.History.Native.Terminal

end BorderVNP
end Computability
end OAI
