import OAI.Computability.BorderVNP.CubeScatterReturnedPadding
import OAI.Computability.BorderVNP.DiagonalExternalFragmentWidthAgreement

/-! # Common native padding widths and the observed physical endpoint banks -/

namespace OAI
namespace Computability
namespace BorderVNP

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

open BorderVNP.Crossing NativeIntervals HostAddress VPVNP.MotifBase

variable {dim m : ℕ} {P : Type*} {bits : P → ℕ} {N : Network dim P bits} {cell : N.Site → Fin ar.cells}
variable {il : NativeIntervals.Layout} {before dir : Fin (R+1) → ℕ → ℕ} {ord : N.CrossingEdge cell ≃ Fin m}
variable {row : Fin (R+1) → Fin m ↪o Fin il.count} {label : Fin ar.cells → Label (ar.n+1) ar.header.d}
variable {hz : ar.header.d^(ar.n+1)=il.alphabet}
local notation "pad" u => Padding.Layout.fromFrame (readings (F.pub u) 0) (readings (F.output u))

/-- The endpoint banks of the recovered assignment have the two bases actually
read by the padding programs. The per-team true width tables also agree with
the original interval scan at any designated team, including empty bins. -/
theorem ObservedOwned.padding_family {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners}
    {raw : Symbols ar.header.d → List Bool} (receipt : ObservedOwned ar decl group F owners raw q)
    (rows : ∀ u, PhysicalRows N cell il (before u) ord (row u) Fin.valEmbedding label (productCode ar.n ar.header.d il.alphabet hz))
    (images : ∀ u, il.Image (before u) il.count (dir u))
    (localWords : ∀ u, Padding.Returned ar decl.1 group u (readings (F.pub u) 0) w (readings (F.output u)) (fun k => dir u (il.widths+k)))
    (representative : Fin (R+1)) :
    EndBanks decl.1 group (fun u => (pad u).packets) (fun u => (pad u).singles) (fun u => readings (F.output u))
      (fun z => lookup q.2 (.inl z)) (demands q.2) ar.K ar.s ∧
    ∀ u, Padding.TailHeader decl.1 group Fin.valEmbedding u (pad u) (readings (F.output u))
      (fun k => dir representative (il.widths+k)) ar.header.blocks ar.b ar.h ar.K ar.s := by
  have axis : chosen ar.b ar.s q.1 = decl.1 := congrArg Prod.fst receipt.observed.1
  have packet : (fun u => (pad u).packets) = fun _ => ar.header.packetBase := funext fun u => by rw [(localWords u).layout]; rfl
  have single : (fun u => (pad u).singles) = fun _ => ar.singleBank := funext fun u => by rw [(localWords u).layout]; rfl
  refine ⟨?_,?_⟩
  · rw [packet,single,←axis,←receipt.allocation]
    exact receipt.recovered.endBanks
  · intro u
    have localTail := (localWords u).tail
    refine { localTail with widths := ?_ }
    intro k hk
    apply (localTail.widths k hk).trans
    apply (rows u).same_widths (rows representative) (images u) (images representative)
    change k < (pad u).labels*(pad u).labels at hk
    simpa only [←hz,pow_two,localTail.alphabet.1] using hk

end TeamContraction

end BorderVNP
end Computability
end OAI
