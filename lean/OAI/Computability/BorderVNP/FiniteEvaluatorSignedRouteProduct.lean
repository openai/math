import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedProduct
import OAI.Computability.BorderVNP.FiniteEvaluatorSignedCubeDictionary

/-! # Native field contraction at a returned physical routing assignment

All teams read the actual common transmission words. Their constant installers
and owned-group scans identify the distributed private payload fiber. Each
remaining field continuation starts in its own verified memory, on the
fragment-inclusive task allocation and the true residual clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.Tally
open BorderVNP.Cube.TeamRows FiniteEvaluator RoutingISA RoutingISA.Transmission TeamContraction Routing
open VPVNP VPVNP.BurstRAM Diagonal.Layout DiagonalTallyPacketEmit
open scoped BigOperators Classical

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R)
variable (header profile cells cables maxRows stride : ℕ)
variable (table : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F)
variable (params : SignedTaskArena.Parameters)
local notation "ar" => planArena L R header profile cells cables maxRows stride
local notation "sa" => signedPlanArena L R header profile cells cables maxRows stride table params
local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "group" => V.owners R (Sigma.fst (Prod.fst raw))
local notation "number" => Fin.val ∘ group
local notation "decl" => Assignment.Routed.trueDeclaration L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "enc" => nativeWordsEquiv L.bitWidth L.supply (Sigma.fst (Prod.fst raw)) axis group
local notation "fresh" => CubeArena.Layout.stop ar
local notation "ptr" => CubeConstants.idBase fresh L.dimension L.bitWidth L.copies L.alternatives L.supply
local notation "packet" => CubeHeaderInstall.Inputs.packetBase (CubeArena.Layout.header ar)
local notation "single" => CubeArena.Layout.singleBank ar

variable {r t d link inner n : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
variable {dir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin sendStride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {delivery : ReturnedDelivery G pin ext wire dir pp lp owner origin sendStride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
local notation "pub" => fun u : Fin (R+1) => TeamHistory.pub (H u)
local notation "mac" => fun u : Fin (R+1) => TeamHistory.macros (H u)
local notation "regs" => fun u : Fin (R+1) => Prod.fst (Prod.snd (Subtype.val (TeamHistory.history (H u))))
local notation "original" => fun u : Fin (R+1) => Prod.snd (Prod.snd (Subtype.val (TeamHistory.history (H u))))

variable (length : ℕ) (ticks : Fin (R+1) → ℕ) (burst clock : ℕ)
local notation "lib" => Cells.library F
local notation "ret" => Cells.terminals F
local notation "fuel" => CompactMachine.nativeClock length
local notation "actual" => TeamSiteEvents.macros (w:=w) lib fuel
local notation "whole" => Code.seq (openCells table) (Code.seq prepareTasks privateReturns)

set_option synthInstance.maxSize 4096
set_option maxRecDepth 6000

section Codec

variable (codec : Cells.Codec)
local notation "clib" => Cells.library F codec
local notation "cret" => Cells.terminals F codec
local notation "cactual" => TeamSiteEvents.macros (w:=w) clib fuel

section Preparation

variable (prep : Code)
local notation "assembled" => Code.seq (openCells table) (Code.seq prep privateReturns)

set_option maxHeartbeats 1800000 in
/-- Codec-specific physical product of bounded field-program values after the returned routing
prefix. The attained private assignment index determines every continuation
and all actual signed-arena lookup operands at the same time. -/
theorem signed_route_product_stage
    (writer : SharedWriters delivery g src)
    (symbols : SymbolFrame g (src anchor) L.blocks L.alternatives L.copies decl group)
    (emits : sharedWords decl (Assignment.Routed.physicalShared (V.owners R) raw.1) = delivery.receivedRows g group)
    (count : ℕ) (offsets control : Fin (R+1) → ℕ)
    (banks : g.banks=(ar).pairBase) (spacing : g.stride=(ar).pairStride)
    (tab : ∀ u, delivery.table=(ar).table (readings ((pub) u) 0) count) (frame : ∀ u, g.frame=readings ((pub) u) 0)
    (room : ∀ u, (ar).ReplayRoom w (readings ((pub) u) 0))
    (scanner : ∀ u, (ar).ScannerWords (readings ((pub) u) 0) u.val (axis).val number (readings ((pub) u)) (src u) (decl).2)
    (pointers : ∀ u, LookupPointers ((sa).lookupFrame (V.teamPairs R raw u).length) (sa).after.ids
      (readings ((pub) u) 0) (src u))
    (fields : ∀ u, let f := (sa).lookupFrame (V.teamPairs R raw u).length
      CubeConstants.Fields (CubeConstants.inArena f fresh L.dimension L.bitWidth L.copies L.alternatives L.supply)
        (readings ((pub) u) 0) ptr (src u))
    (wide : CubeDeck.minimumWidth F L.dimension L.bitWidth L.copies L.alternatives L.supply ≤ w)
    (word : (sa).after.packed ≤ 2^w) (reportCap : ∀ u, (V.teamPairs R raw u).length ≤ params.report.vertices)
    (digits : argumentWidth L.dimension L.bitWidth L.copies L.alternatives L.supply ≤ params.report.cubeWidth)
    (fixed : ∀ p, L.table p=table)
    (model : ∀ u, (H u).macros=cactual)
    (roomTicks : ∀ u, (CubeDeck.install table).slots+V.ownedTicks R raw header profile cells cables maxRows stride pub u ≤ ticks u)
    (choice : 1 ≤ clock) :
    ∃ E : CubeTriple.Fiber raw.1.2 ≃ ((u : Fin (R+1)) → Evaluator.Returns (CubeTriple.installGroups table)
        ((pub) u) cactual ((regs) u) ((original) u)),
      ((∀ f, let next := V.withPrivate R raw f
        let Y := fun u => V.signedInputs R next u header profile cells cables maxRows stride table params
        (∀ u, let out := E f u
          DiagonalResidueRAM.TraceOK out.val.1 (((enc f.val).2 u).val) out.val.1.length ∧
            traceCost out.val.1 ≤ (CubeDeck.install table).slots+V.ownedTicks R raw header profile cells cables maxRows stride pub u ∧
            CubePacket.Prepared (Y u) ((pub) u) out.val.2.2 ∧
            CubePacket.Sources (Y u) ((sa).tasks u.val (readings ((pub) u) 0) (offsets u) (control u)) ∧
            ∀ x, group (x.row axis).1=u → (V.bankData R next packet single).Holds out.val.2.2 x) ∧
          (∏ u, ∏ i, (Y u).scalar i)=cubeTermWeight L.table (fun _ _ => 1) (V.read R next).2.2) ∧
      (∏ u, boundedWeight ((pub) u) clib cret fuel assembled ((regs) u) ((original) u) (ticks u) burst clock) =
        ∑ f : CubeTriple.Fiber raw.1.2, ∏ u, let z := E f u
          boundedWeight ((pub) u) clib cret fuel (OwnedContinuation.codeFor prep) z.val.2.1 z.val.2.2 (ticks u-traceCost z.val.1) burst clock) := by
  obtain ⟨E,hE⟩ := V.signed_route_dictionary R raw header profile cells cables maxRows stride table params
    writer symbols emits count offsets control banks spacing tab frame room scanner pointers fields wide word reportCap digits fixed
  let cast (u : Fin (R+1)) : Evaluator.Returns (CubeTriple.installGroups table) ((pub) u) ((mac) u) ((regs) u) ((original) u) ≃
      Evaluator.Returns (CubeTriple.installGroups table) ((pub) u) cactual ((regs) u) ((original) u) :=
    Equiv.subtypeEquivRight fun _ => by change Runs _ (H u).macros _ _ _ _ _ _ ↔ Runs _ cactual _ _ _ _ _ _; rw [model u]
  let live := E.trans (Equiv.piCongrRight cast)
  refine ⟨live,?_,?_⟩
  · intro f
    obtain ⟨hs,prod⟩ := hE f
    exact ⟨fun u => ⟨(hs u).1,(hs u).2.1,(hs u).2.2.1,(hs u).2.2.2.1,(hs u).2.2.2.2.1⟩,prod⟩
  · exact OwnedContinuation.routed_product_stage table length codec prep pub regs original ticks burst clock live
      (fun f u => ((hE f).1 u).2.1.trans (roomTicks u)) choice

end Preparation

set_option maxHeartbeats 1800000 in
/-- Codec-specific physical product of bounded field-program values after the returned routing
prefix. The attained private assignment index determines every continuation
and all actual signed-arena lookup operands at the same time. -/
theorem signed_route_product_for
    (writer : SharedWriters delivery g src)
    (symbols : SymbolFrame g (src anchor) L.blocks L.alternatives L.copies decl group)
    (emits : sharedWords decl (Assignment.Routed.physicalShared (V.owners R) raw.1) = delivery.receivedRows g group)
    (count : ℕ) (offsets control : Fin (R+1) → ℕ)
    (banks : g.banks=(ar).pairBase) (spacing : g.stride=(ar).pairStride)
    (tab : ∀ u, delivery.table=(ar).table (readings ((pub) u) 0) count) (frame : ∀ u, g.frame=readings ((pub) u) 0)
    (room : ∀ u, (ar).ReplayRoom w (readings ((pub) u) 0))
    (scanner : ∀ u, (ar).ScannerWords (readings ((pub) u) 0) u.val (axis).val number (readings ((pub) u)) (src u) (decl).2)
    (pointers : ∀ u, LookupPointers ((sa).lookupFrame (V.teamPairs R raw u).length) (sa).after.ids
      (readings ((pub) u) 0) (src u))
    (fields : ∀ u, let f := (sa).lookupFrame (V.teamPairs R raw u).length
      CubeConstants.Fields (CubeConstants.inArena f fresh L.dimension L.bitWidth L.copies L.alternatives L.supply)
        (readings ((pub) u) 0) ptr (src u))
    (wide : CubeDeck.minimumWidth F L.dimension L.bitWidth L.copies L.alternatives L.supply ≤ w)
    (word : (sa).after.packed ≤ 2^w) (reportCap : ∀ u, (V.teamPairs R raw u).length ≤ params.report.vertices)
    (digits : argumentWidth L.dimension L.bitWidth L.copies L.alternatives L.supply ≤ params.report.cubeWidth)
    (fixed : ∀ p, L.table p=table)
    (model : ∀ u, (H u).macros=cactual)
    (roomTicks : ∀ u, (CubeDeck.install table).slots+V.ownedTicks R raw header profile cells cables maxRows stride pub u ≤ ticks u)
    (choice : 1 ≤ clock) :
    ∃ E : CubeTriple.Fiber raw.1.2 ≃ ((u : Fin (R+1)) → Evaluator.Returns (CubeTriple.installGroups table)
        ((pub) u) cactual ((regs) u) ((original) u)),
      ((∀ f, let next := V.withPrivate R raw f
        let Y := fun u => V.signedInputs R next u header profile cells cables maxRows stride table params
        (∀ u, let out := E f u
          DiagonalResidueRAM.TraceOK out.val.1 (((enc f.val).2 u).val) out.val.1.length ∧
            traceCost out.val.1 ≤ (CubeDeck.install table).slots+V.ownedTicks R raw header profile cells cables maxRows stride pub u ∧
            CubePacket.Prepared (Y u) ((pub) u) out.val.2.2 ∧
            CubePacket.Sources (Y u) ((sa).tasks u.val (readings ((pub) u) 0) (offsets u) (control u)) ∧
            ∀ x, group (x.row axis).1=u → (V.bankData R next packet single).Holds out.val.2.2 x) ∧
          (∏ u, ∏ i, (Y u).scalar i)=cubeTermWeight L.table (fun _ _ => 1) (V.read R next).2.2) ∧
      (∏ u, boundedWeight ((pub) u) clib cret fuel whole ((regs) u) ((original) u) (ticks u) burst clock) =
        ∑ f : CubeTriple.Fiber raw.1.2, ∏ u, let z := E f u
          boundedWeight ((pub) u) clib cret fuel OwnedContinuation.code z.val.2.1 z.val.2.2 (ticks u-traceCost z.val.1) burst clock) :=
  V.signed_route_product_stage (codec:=codec) (prep:=prepareTasks) R raw header profile cells cables maxRows stride table params
    length ticks burst clock writer symbols emits count offsets control banks spacing tab frame room scanner pointers fields
    wide word reportCap digits fixed model roomTicks choice

end Codec

set_option maxHeartbeats 1800000 in
/-- Physical product of bounded field-program values after the returned routing
prefix. The attained private assignment index determines every continuation
and all actual signed-arena lookup operands at the same time. -/
theorem signed_route_product
    (writer : SharedWriters delivery g src)
    (symbols : SymbolFrame g (src anchor) L.blocks L.alternatives L.copies decl group)
    (emits : sharedWords decl (Assignment.Routed.physicalShared (V.owners R) raw.1) = delivery.receivedRows g group)
    (count : ℕ) (offsets control : Fin (R+1) → ℕ)
    (banks : g.banks=(ar).pairBase) (spacing : g.stride=(ar).pairStride)
    (tab : ∀ u, delivery.table=(ar).table (readings ((pub) u) 0) count) (frame : ∀ u, g.frame=readings ((pub) u) 0)
    (room : ∀ u, (ar).ReplayRoom w (readings ((pub) u) 0))
    (scanner : ∀ u, (ar).ScannerWords (readings ((pub) u) 0) u.val (axis).val number (readings ((pub) u)) (src u) (decl).2)
    (pointers : ∀ u, LookupPointers ((sa).lookupFrame (V.teamPairs R raw u).length) (sa).after.ids
      (readings ((pub) u) 0) (src u))
    (fields : ∀ u, let f := (sa).lookupFrame (V.teamPairs R raw u).length
      CubeConstants.Fields (CubeConstants.inArena f fresh L.dimension L.bitWidth L.copies L.alternatives L.supply)
        (readings ((pub) u) 0) ptr (src u))
    (wide : CubeDeck.minimumWidth F L.dimension L.bitWidth L.copies L.alternatives L.supply ≤ w)
    (word : (sa).after.packed ≤ 2^w) (reportCap : ∀ u, (V.teamPairs R raw u).length ≤ params.report.vertices)
    (digits : argumentWidth L.dimension L.bitWidth L.copies L.alternatives L.supply ≤ params.report.cubeWidth)
    (fixed : ∀ p, L.table p=table)
    (model : ∀ u, (H u).macros=actual)
    (roomTicks : ∀ u, (CubeDeck.install table).slots+V.ownedTicks R raw header profile cells cables maxRows stride pub u ≤ ticks u)
    (choice : 1 ≤ clock) :
    ∃ E : CubeTriple.Fiber raw.1.2 ≃ ((u : Fin (R+1)) → Evaluator.Returns (CubeTriple.installGroups table)
        ((pub) u) actual ((regs) u) ((original) u)),
      ((∀ f, let next := V.withPrivate R raw f
        let Y := fun u => V.signedInputs R next u header profile cells cables maxRows stride table params
        (∀ u, let out := E f u
          DiagonalResidueRAM.TraceOK out.val.1 (((enc f.val).2 u).val) out.val.1.length ∧
            traceCost out.val.1 ≤ (CubeDeck.install table).slots+V.ownedTicks R raw header profile cells cables maxRows stride pub u ∧
            CubePacket.Prepared (Y u) ((pub) u) out.val.2.2 ∧
            CubePacket.Sources (Y u) ((sa).tasks u.val (readings ((pub) u) 0) (offsets u) (control u)) ∧
            ∀ x, group (x.row axis).1=u → (V.bankData R next packet single).Holds out.val.2.2 x) ∧
          (∏ u, ∏ i, (Y u).scalar i)=cubeTermWeight L.table (fun _ _ => 1) (V.read R next).2.2) ∧
      (∏ u, boundedWeight ((pub) u) lib ret fuel whole ((regs) u) ((original) u) (ticks u) burst clock) =
        ∑ f : CubeTriple.Fiber raw.1.2, ∏ u, let z := E f u
          boundedWeight ((pub) u) lib ret fuel OwnedContinuation.code z.val.2.1 z.val.2.2 (ticks u-traceCost z.val.1) burst clock) :=
  V.signed_route_product_for (codec:=.dense) R raw header profile cells cables maxRows stride table params length ticks burst clock
    writer symbols emits count offsets control banks spacing tab frame room scanner pointers fields wide word reportCap digits
    fixed model roomTicks choice

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
