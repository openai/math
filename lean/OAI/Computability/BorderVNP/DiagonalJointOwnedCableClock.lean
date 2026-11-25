import OAI.Computability.BorderVNP.DiagonalJointReceivedArguments
import OAI.Computability.BorderVNP.CubeHostScatterScheduledRows
import OAI.Computability.BorderVNP.CubeScatterReturnedPadding

/-! # The occupied cable and padding rows on a jointly supported preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator Evaluator CellMacro.Generator Crossing NativeIntervals HostAddress

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {receive : ℕ → Fin (R+1)} {origin stride : ℕ}
    {hist : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext wire D pp lp receive origin stride hist pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {a : SignedTaskArena.Layout} {id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ}
    (U : Fin (R+1) → PinStart SparseExterior.driver n w) (p : PinStart.JointPrefix id U)
    {decl : LengthDeclaration a.cube.n a.cube.header.d} {group : Fin a.cube.header.d → Fin (R+1)}
    {A : Type*} [Fintype A] (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (width : A → ℕ)
    {template : DiagonalTallyPacketEmit.Frame} {count ctl : ℕ}

set_option quotPrecheck false
local notation "owners" => greedyOwner R a.cube.b a.cube.s label recv width
local notation "F" => PinStart.ownedVisits (ar:=a.cube) U p
local notation3 (prettyPrint := false) "V(" u ")" => PinStart.visits id U (p u)

set_option maxHeartbeats 1600000 in
/-- The occupied cable scans at the actual owned return see precisely the
owner chosen by the native assignment and the interval loads of the original
network. Team number, directory pointer and cable count come from the
protected primary header. -/
theorem SharedWriters.cables_on_joint_prefix (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) a.cube.header.blocks a.cube.K a.cube.h decl group)
    (handoff : OwnedHandoff f g src a.cube decl group template id count F)
    {q : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) owners}
    (receipt : ObservedOwned a.cube decl group F owners (f.receivedRows g group) q) (u : Fin (R+1))
    {bits : ℕ} {rr rt : Bank w} {initial last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory a.cube.n bits (hist u).pub (hist u).macros rr initial es rt last)
    (data : DataReady (hist u).pub W.dataInput)
    (records : (DataWriter.layout (readings (hist u).pub) (readings W.dataInput)).output=a.cube.records)
    (source : src u=readings W.sharedInput) (profile : ℕ → ℕ) :
    let head := readings (U u).pub 0
    let mem := readings (V(u)).owned.val.2.2
    let host := HostScatter.Layout.fromFrame head mem
    NativeEntry a.cube head ctl decl.1 R profile (readings initial) (readings W.dataInput) →
    GroupWeights.PhysicalImage (LocalRow.weightLayout a.cube head decl.1.val) profile
      a.cube.header.blocks a.cube.b a.cube.K a.cube.h decl label recv width →
    readings initial head=u.val → readings initial (head+7)=a.cube.cables → readings initial (head+72)=a.cube.hostDirectory →
    ∀ {dim m : ℕ} {P : Type} {bs : P → ℕ} (N : Network dim P bs) (cell : N.Site → Fin a.cube.cells)
        (il : NativeIntervals.Layout) (before interval : ℕ → ℕ) (ord : N.CrossingEdge cell ≃ Fin m)
        (row : Fin m ↪o Fin il.count) (code : Label (a.cube.n+1) a.cube.header.d ↪ Fin il.alphabet),
      PhysicalRows N cell il before ord row Fin.valEmbedding label code →
      HostScatter.ResidentRows host il before interval mem a.cube.n a.cube.header.d a.cube.header.blocks a.cube.b a.cube.h a.cube.K a.cube.s →
      (∀ pair, load (cablePair ord (crossSrc N cell) (crossDst N cell) label) (crossWidth N cell ∘ ord.symm) pair ≤ a.cube.header.blocks*(a.cube.h*a.cube.b)) →
      ∃ _ : host.ScheduledCables mem (a.cube.header.blocks*(a.cube.h*a.cube.b)) decl.1 (fun z => (group z).val),
        host.team=u.val ∧ host.count=a.cube.cables := by
  intro head mem host entry image team countWord cellPointer dim m P bs N cell il before interval ord row code rows resident cap
  have pubEq : (U u).pub=(hist u).pub := handoff.pub u
  have frame : head=readings (hist u).pub 0 := congrFun (congrArg readings pubEq) 0
  have keep := writer.owned_host_retention symbols handoff receipt u W data records source profile (frame ▸ entry)
  have saved (i : ℕ) (hi : i ∈ ([0,1,7,15,65,66,67,72,87,92] : List ℕ)) :
      mem (head+i)=readings initial (head+i) := by
    exact keep.open_frame _ hi
  have hosted : host.cells=a.cube.hostDirectory := (saved 72 (by decide)).trans cellPointer
  have stored := writer.bare_received_owner U p label recv width symbols handoff receipt u W data records source profile entry image
  have axis : chosen a.cube.b a.cube.s q.1=decl.1 := congrArg Prod.fst receipt.observed.1
  have cellOwner (c : Fin a.cube.cells) : mem (host.cells+2*c.val)=(group (label c decl.1)).val := by
    rw [hosted]
    exact (stored c).trans (by rw [axis,receipt.allocation])
  exact ⟨resident.scheduledCables rows (handoff.room u).alphabet decl.1 (fun z => (group z).val) cellOwner cap,
    (saved 0 (by decide)).trans team,(saved 7 (by decide)).trans countWord⟩

/-- One interval publication supplies both padding and cable rows: the
occupied widths used by the guard and the receiving endpoint words used by
the argument loop come from the same real writer and owned return. -/
theorem SharedWriters.owned_argument_rows (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) a.cube.header.blocks a.cube.K a.cube.h decl group)
    (handoff : OwnedHandoff f g src a.cube decl group template id count F)
    {q : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) owners}
    (receipt : ObservedOwned a.cube decl group F owners (f.receivedRows g group) q) (u : Fin (R+1))
    {bits broadcast : ℕ} {rr rt : Bank w} {initial last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory a.cube.n bits (hist u).pub (hist u).macros rr initial es rt last)
    (ready : DataReady (hist u).pub W.dataInput)
    (records : (DataWriter.layout (readings (hist u).pub) (readings W.dataInput)).output=a.cube.records)
    (source : src u=readings W.sharedInput)
    {dim m : ℕ} {P : Type} {bs : P → ℕ} (N : Network dim P bs) (cell : N.Site → Fin a.cube.cells)
    (il : NativeIntervals.Layout) (previous dir : ℕ → ℕ) {ord : N.CrossingEdge cell ≃ Fin m}
    {row : Fin m ↪o Fin il.count} (hz : a.cube.header.d^(a.cube.n+1)=il.alphabet)
    (rows : PhysicalRows N cell il previous ord row Fin.valEmbedding label (productCode a.cube.n a.cube.header.d il.alphabet hz))
    (interval : il.Image previous il.count dir) (fit : il.Fits w previous) (fields : il.Fields previous)
    (atFrame : il.frame=readings (hist u).pub 0) (space : HostScatter.CableColumns a.cube il.frame il previous)
    (widths : il.widths=a.cube.widthBase) (low : ∀ z<a.cube.publicBase, dir z=readings initial z)
    (fixed : CubeAllocation.HostPointers a.cube il.frame (readings initial))
    (team : readings initial il.frame=u.val) (cells : readings initial (il.frame+7)=a.cube.cables)
    (cap : ∀ pair, load (cablePair ord (crossSrc N cell) (crossDst N cell) label) (crossWidth N cell ∘ ord.symm) pair ≤ a.cube.header.blocks*(a.cube.h*a.cube.b))
    (entry : NativeEntry a.cube il.frame ctl decl.1 R (LocalRow.powerHeaderImage a.cube broadcast dir) (readings initial) (readings W.dataInput))
    (image : GroupWeights.PhysicalImage (LocalRow.weightLayout a.cube il.frame decl.1.val) (LocalRow.powerHeaderImage a.cube broadcast dir)
      a.cube.header.blocks a.cube.b a.cube.K a.cube.h decl label recv width) :
    let head := readings (U u).pub 0
    let mem := readings (V(u)).owned.val.2.2
    let host := HostScatter.Layout.fromFrame head mem
    Padding.Returned a.cube decl.1 group u head w mem (fun k => dir (il.widths+k)) ∧
      ∃ _ : host.ScheduledCables mem (a.cube.header.blocks*(a.cube.h*a.cube.b)) decl.1 (fun z => (group z).val),
        host.team=u.val ∧ host.count=a.cube.cables := by
  intro head mem host
  have base : head=il.frame := (congrFun (congrArg readings (handoff.pub u)) 0).trans atFrame.symm
  have pad := writer.returned_padding N cell il previous dir rows interval cap symbols handoff receipt u W ready records
    source fit fields atFrame space widths low entry fixed
  have resident := writer.owned_host_columns symbols handoff receipt u W ready records source il previous dir interval
    fit fields atFrame space widths low entry (fixed 91 (by decide) _ rfl) (fixed 93 (by decide) _ rfl) (fixed 94 (by decide) _ rfl)
  have ptr := fixed 72 (by decide) a.cube.hostDirectory rfl
  rw [←base] at entry image team cells ptr
  refine ⟨pad,?_⟩
  exact writer.cables_on_joint_prefix U p label recv width symbols handoff receipt u W ready records source _
    entry image team cells ptr
    N cell il previous dir ord row _ rows resident cap

end TeamContraction

end BorderVNP
end Computability
end OAI
