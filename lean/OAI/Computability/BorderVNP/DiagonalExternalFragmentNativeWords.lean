import OAI.Computability.BorderVNP.DiagonalExternalFragmentHostWords
import OAI.Computability.BorderVNP.DiagonalExternalFragmentOwnedWords
import OAI.Computability.BorderVNP.DiagonalExternalFreeReceived
import OAI.Computability.BorderVNP.DiagonalExternalFragmentScatter
import OAI.Computability.BorderVNP.FragmentRowsArenaBounds

/-! # Sparse exterior sources in a genuine recovered owned-group execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open VPVNP BurstRAM Crossing TeamContraction RoutingISA RoutingISA.Transmission RoutingISA.Pins Routing
open Packing Packing.CellAddresses BorderVNP.Cube Cube.Physical Cube.Scatter Cube.NativeIntervals
open Cube.HostAddress Cube.HostScatter Cube.TeamRows Cube.Tally Scatter.Assignment
open Diagonal.Layout DiagonalTallyPacketEmit FiniteEvaluator

variable {R r t pins link inner n W V g entries desc D C m nP M : ℕ}
    {Edge : Type} {G : Wiring R r t pins link inner n Edge}
    {inputPin : Fin pins → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory W} {ib hb sb : Fin (R+1) → ℕ}
    {layout : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    {group : Fin ar.header.d → Fin (R+1)} {F : TeamRows.Returns (Fin (R+1)) ar W}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    {template : Frame} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {count : ℕ}

local notation "PL" => fun u => G.pinLayout u (ib u) (hb u) (sb u)
local notation "dir" => freeDirectory R r (G.program.length+t) link V g entries desc

variable {f : ReturnedDelivery G inputPin ext wire
    (freeDirectory R r (G.program.length+t) link V g entries desc) pp lp owner origin stride H
    (fun u => G.pinLayout u (ib u) (hb u) (sb u))}
    (writer : SharedWriters f layout src) (symbols : SymbolFrame layout (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f layout src ar decl group template id count F)
    {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows layout group) q)
    (N : Network D (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C)
    (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin nP)
    {il : NativeIntervals.Layout} (ord : N.CrossingEdge cell ≃ Fin M) {row : Fin M ↪o Fin il.count}
    (label : Fin C → Label (ar.n+1) ar.header.d)
    {before scan : Fin (R+1) → ℕ → ℕ} {hz : ar.header.d^(ar.n+1) = il.alphabet}

set_option quotPrecheck false in
local notation "axis" => chosen ar.b ar.s q.1
local notation "host" => hostLayout F.pub F.output

variable (tab : HostTables (blocks := ar.header.blocks) (b := ar.b) (h := ar.h) (K := ar.K) (s := ar.s)
    N cell edgeID portID il ord row label (chosen ar.b ar.s q.1) group Fin.valEmbedding F.pub F.output origin stride before scan hz)
    (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
      (crossWidth N cell ∘ ord.symm) u ≤ ar.header.blocks*(ar.h*ar.b))

set_option quotPrecheck false in
local notation "single" => fun x => lookup q.2 (.inl x)
set_option quotPrecheck false in
local notation "bitsAtEnd" => fun side j => readEnd single (demands q.2) side (packedSlotEmbedding N cell ord label ar.header.blocks (ar.h*ar.b) cap j)

include writer symbols handoff receipt tab in
/-- Every actual host destination contains the one recovered physical assignment's
endpoint bit or the program's true raw literal/substitution. The two ordered
fields need no input convention on their unused and padded lanes. -/
theorem native_source_words_at_inputs (hg : 0 < g) (room : r*(2*(G.program.length+t)+R*link) ≤ V*g)
    (place : LivePlacement N cell edgeID portID lp) (input : Fin pins → Bool)
    (subst : ∀ u, SubstitutionAt (PL u) (extendGuess input) (H u).initial)
    (assigned : ∀ z : FreePort R r (G.program.length+t),
      let c := cell (N.attach (freeLane hg room z).1)
      owner c.val=group (label c axis))
    (pointers : ∀ t, (host t).packets = ar.header.packetBase ∧ (host t).singles = ar.singleBank)
    (bank : origin = ar.cellBank) (step : stride = ar.cellStride) (cells : C ≤ ar.cells) :
    SourceWords N cell edgeID portID hg room lp origin stride (freeBits G input) bitsAtEnd
      (hostWords label axis group F.pub F.output) := by
  have packets : (fun t => (host t).packets) = fun _ => ar.header.packetBase := funext fun t => (pointers t).1
  have singles : (fun t => (host t).singles) = fun _ => ar.singleBank := funext fun t => (pointers t).2
  have banks : EndBanks axis group (fun t => (host t).packets) (fun t => (host t).singles)
      (fun t => readings (F.output t)) single (demands q.2) ar.K ar.s := by
    rw [packets,singles,←receipt.allocation]
    exact receipt.recovered.endBanks
  constructor
  · intro side e j
    exact host_crossing_word N cell edgeID portID il ord row label axis group Fin.valEmbedding F.pub F.output
      origin stride tab banks cap side e j
  · intro z a c
    let pos := laneAddress lp a
    let who := group (label c axis)
    let addr := origin+c.val*stride+pos.2
    have atCell : pos.1 = c.val := congrArg Prod.fst (place a.1)
    have atPos := placedOrdinal N cell edgeID portID place c ⟨a.1,rfl⟩ a.2
    change pos = _ at atPos
    have limit : pos.2 < suppliedSize N cell c := by rw [atPos]; exact Fin.isLt _
    have kept := host_prefix_free_lane N cell edgeID portID place (tab.cables who) origin stride
      (tab.bases who) tab.room (host who).count le_rfl a
    dsimp only at kept
    change (host who).prefix (readings (F.output who)) (host who).count
      (origin+pos.1*stride+pos.2) = readings (F.output who) (origin+pos.1*stride+pos.2) at kept
    rw [atCell] at kept
    have high : ar.publicBase ≤ origin := bank ▸ (ar.separated.2.2.2.1.trans (Nat.le_add_right ..))
    have below : addr < ar.stop := by
      change origin+c.val*stride+pos.2 < _
      rw [bank,step]
      exact FragmentRows.cell_address (c.isLt.trans_le cells) (step ▸ limit.trans_le (tab.room c))
    have old := writer.owned_delivery_word symbols handoff receipt who addr (by dsimp [addr]; omega) (.inl below)
    have field := received_free_word f hg room input subst z
    have posOwner : owner pos.1 = who := (congrArg owner atCell).trans (assigned z)
    dsimp only at field
    change (H (owner pos.1)).history.val.2.2 (origin+pos.1*stride+(lp (a.1.1.val*V+a.1.2.val)).2+a.2.val) =
      Fin.ofNat _ (freeBits G input z).toNat at field
    rw [posOwner,atCell,Nat.add_assoc] at field
    have word : (H who).history.val.2.2 addr = Fin.ofNat _ (freeBits G input z).toNat := field
    have lim : 1 < 2^W := Nat.one_lt_pow f.word.ne' (by decide)
    refine kept.trans ((congrArg Fin.val (old.trans word)).trans ?_)
    cases freeBits G input z <;> simp [Nat.mod_eq_of_lt lim]

include writer symbols handoff receipt tab in
/-- A global receiving schedule also supplies the lane-specific owner reads. -/
theorem native_source_words (hg : 0 < g) (room : r*(2*(G.program.length+t)+R*link) ≤ V*g)
    (place : LivePlacement N cell edgeID portID lp) (input : Fin pins → Bool)
    (subst : ∀ u, SubstitutionAt (PL u) (extendGuess input) (H u).initial)
    (assigned : ∀ c : Fin C, owner c.val = group (label c axis))
    (pointers : ∀ t, (host t).packets = ar.header.packetBase ∧ (host t).singles = ar.singleBank)
    (bank : origin = ar.cellBank) (step : stride = ar.cellStride) (cells : C ≤ ar.cells) :
    SourceWords N cell edgeID portID hg room lp origin stride (freeBits G input) bitsAtEnd
      (hostWords label axis group F.pub F.output) := by
  exact native_source_words_at_inputs writer symbols handoff receipt N cell edgeID portID ord label tab cap hg room place
    input subst (fun z => assigned (cell (N.attach (freeLane hg room z).1))) pointers bank step cells

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
