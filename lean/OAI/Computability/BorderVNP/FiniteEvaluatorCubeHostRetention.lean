import OAI.Computability.BorderVNP.CubeScatterOwnedHostColumns
import OAI.Computability.BorderVNP.PackedRoutingHeaders

/-! # Original geometry and true cell banks at the returned host memory

The data writer appends its real records and publishes their count. The
shared routing, deck installation and arbitrary owned-group return preserve
the earlier geometry and the true directory columns. This transports whole
profile bank regions as well as each scalar word that the host scatter needs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeAllocation

open RoutingISA Packing VPVNP.BurstRAM

/-- Returned physical words on the two public regions of the host pass. -/
structure HostRetention (a : CubeArena.Layout) (frame : ℕ) (initial written returned : ℕ → ℕ) : Prop where
  primary : frame+112 ≤ a.header.header
  lower : ∀ x < a.header.header, x≠frame+13 → x≠frame+46 → returned x=initial x
  tables : ∀ x, a.publicBase ≤ x → x<a.records → returned x=written x

variable {a : CubeArena.Layout} {frame : ℕ} {initial written returned : ℕ → ℕ}
variable (h : HostRetention a frame initial written returned)
include h

/-- The same retention starts at the genuine native directory output when
the immutable lower region is read there. Thus the bundle headers may use
the actual receiving bank written by the directory program. -/
theorem HostRetention.from_written (low : ∀ x<a.header.header, written x=initial x) :
    HostRetention a frame written written returned :=
  ⟨h.primary,fun x hx ne13 ne46 => (h.lower x hx ne13 ne46).trans (low x hx).symm,h.tables⟩

/-- The ten public frame fields of the signed post-ownership suffix. -/
theorem HostRetention.open_frame : ∀ j ∈ ([0,1,7,15,65,66,67,72,87,92] : List ℕ),
    returned (frame+j)=initial (frame+j) := by
  intro j hj
  have base := h.primary
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  apply h.lower <;> omega

/-- Every profile or packed cable word above the complete boot frame and below
the secondary header survives all the native programs. -/
theorem HostRetention.geometry {start : ℕ} (low : frame+112 ≤ start) : ∀ x, start ≤ x → x<a.header.header → returned x=initial x :=
  fun x hx high => h.lower x high (by omega) (by omega)

/-- Every routing-header pointer used at the host pass is still the real geometry pointer. -/
theorem HostRetention.header {origin J : ℕ} (hdr : RoutingOutputs.Header frame origin a.cables a.cells J initial) :
    RoutingOutputs.Header frame origin a.cables a.cells J returned := by
  have keep (j : ℕ) (hj : j<112) (n13 : j≠13) (n46 : j≠46) : returned (frame+j)=initial (frame+j) :=
    h.lower _ ((Nat.add_lt_add_left hj frame).trans_le h.primary) (by omega) (by omega)
  exact ⟨(keep 6 (by decide) (by decide) (by decide)).trans hdr.cables,
    (keep 7 (by decide) (by decide) (by decide)).trans hdr.edges,
    (keep 11 (by decide) (by decide) (by decide)).trans hdr.cells,
    (keep 64 (by decide) (by decide) (by decide)).trans hdr.privatePairs,
    (keep 65 (by decide) (by decide) (by decide)).trans hdr.livePairs,
    (keep 87 (by decide) (by decide) (by decide)).trans hdr.ends⟩

/-- All second words of the native two-word cell directory are still available. -/
theorem HostRetention.banks : ∀ c<a.cells, returned (a.hostDirectory+c*2+1)=written (a.hostDirectory+c*2+1) := by
  intro c hc
  obtain ⟨_,labels,weights,owners,pair,host,_,_⟩ := a.writer_order
  apply h.tables <;> omega

end FiniteEvaluator.CubeAllocation

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator Evaluator

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
variable {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
variable {group : Fin ar.header.d → Fin (R+1)} {F : TeamRows.Returns (Fin (R+1)) ar w}
variable {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
variable {template : Frame} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {count : ℕ}

/-- Read the earlier geometry and actual native directory image through the
observed transmission and arbitrary return of the owned program. -/
theorem SharedWriters.owned_host_retention (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) ar.header.blocks ar.K ar.h decl group)
    (handoff : OwnedHandoff f g src ar decl group template id count F)
    {q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners}
    (receipt : ObservedOwned ar decl group F owners (f.receivedRows g group) q) (u : Fin (R+1))
    {controls width : ℕ} {rr rt : Bank w} {initial last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory ar.n width (H u).pub (H u).macros rr initial es rt last)
    (ready : DataReady (H u).pub W.dataInput)
    (records : (DataWriter.layout (readings (H u).pub) (readings W.dataInput)).output=ar.records)
    (source : src u=readings W.sharedInput) (profile : ℕ → ℕ)
    (entry : NativeEntry ar (readings (H u).pub 0) controls decl.1 R profile (readings initial) (readings W.dataInput)) :
    CubeAllocation.HostRetention ar (readings (F.pub u) 0) (readings initial) (readings W.dataInput) (readings (F.output u)) := by
  let frame := readings (H u).pub 0
  have base : readings (F.pub u) 0=frame := congrFun (congrArg readings (handoff.pub u)) 0
  have primary := (handoff.room u).primary
  change frame+112 ≤ ar.header.header at primary
  have keep := writer.owned_data_input_static symbols handoff receipt u W ready records source
  rw [base]
  obtain ⟨header,labels,weights,owners,pair,host,_,_⟩ := ar.writer_order
  refine ⟨primary,fun x lo ne13 ne46 => (keep x (by omega) (.inl (by omega)) ne13 ne46).trans (entry.low x lo),?_⟩
  intro x low high
  exact keep x high (.inr low) (by omega) (by omega)

end TeamContraction

end BorderVNP
end Computability
end OAI
