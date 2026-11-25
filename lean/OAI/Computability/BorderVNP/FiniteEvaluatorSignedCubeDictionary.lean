import OAI.Computability.BorderVNP.FiniteEvaluatorSignedLookupWriter
import OAI.Computability.BorderVNP.FiniteEvaluatorSignedCubeInputs
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeInstalledArena

/-! # Complete signed field cube histories from the actual returned transmission

Fix the exterior transmission and its decoded common rows. The signed
initializer and native team traversal run from the actual routing endpoint.
Their full return tuples are in bijection with the remaining private choices.
The task and lookup addresses include the genuine sparse fragment allocation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.Tally
open BorderVNP.Cube.Padding.Banks BorderVNP.Cube.TeamRows FiniteEvaluator RoutingISA RoutingISA.Transmission TeamContraction Routing
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

set_option maxHeartbeats 1600000 in
/-- All physical installer and owned-group paths on the observed exterior
and true signed allocation are represented exactly once. Their final lookup
operands and entire field product correspond to their recovered raw term. -/
theorem signed_route_dictionary
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
    (fixed : ∀ p, L.table p=table) :
    ∃ E : CubeTriple.Fiber raw.1.2 ≃ ((u : Fin (R+1)) → Evaluator.Returns (CubeTriple.installGroups table)
        ((pub) u) ((mac) u) ((regs) u) ((original) u)),
      ∀ f, let next := V.withPrivate R raw f
        let Y := fun u => V.signedInputs R next u header profile cells cables maxRows stride table params
        (∀ u, let out := E f u
          DiagonalResidueRAM.TraceOK out.val.1 (((enc f.val).2 u).val) out.val.1.length ∧
            traceCost out.val.1 ≤ (CubeDeck.install table).slots+V.ownedTicks R raw header profile cells cables maxRows stride pub u ∧
            CubePacket.Prepared (Y u) ((pub) u) out.val.2.2 ∧
            CubePacket.Sources (Y u) ((sa).tasks u.val (readings ((pub) u) 0) (offsets u) (control u)) ∧
            (∀ x : View L.dimension L.alphabet L.blocks (L.copies*L.bitWidth), group (x.row axis).1=u →
              (V.bankData R next packet single).Holds out.val.2.2 x) ∧
            (∃ mid : Memory w, CubeTriple.Readback
              (l:=(ar).scanner (readings ((pub) u) 0) u.val (axis).val (ar).rowSelectorBits)
              (V.bankData R next packet single) number (ar).powerBase (ar).vertexBase (ar).publicBase mid out.val.2.2 ∧
              ∀ a < fresh, mid a=(original) u a)) ∧
          (∏ u, ∏ i, (Y u).scalar i) = cubeTermWeight L.table (fun _ _ => 1) (V.read R next).2.2 := by
  let fr (u : Fin (R+1)) := (sa).lookupFrame (V.teamPairs R raw u).length
  let A := V.bankData R raw packet single
  have space (u : Fin (R+1)) : readings ((pub) u) 0+112 ≤ fresh ∧ CubeConstants.arenaEnd fresh (CubeDeck.entry table)<2^w := by
    have cap := (congrArg List.length (V.numbered_pairs R raw u)).symm ▸ CubeAllocation.team_count ar axis number u.val
    obtain ⟨lo,ds,_,_,rf,ids,top⟩ := (sa).lookup_rooms A rfl cap (reportCap u) digits (room u).primary word
    exact ⟨lo,ds.trans_lt (by omega)⟩
  have loadedFields u := writer.returned_constant_fields ar (readings ((pub) u) 0) count (tab u) (room u).primary
    (frame u) _ ptr u (fields u)
  have one (u : Fin (R+1)) : ∃ x : Evaluator.Returns (CubeDeck.install table) ((pub) u) ((mac) u) ((regs) u) ((original) u),
      DiagonalResidueRAM.TraceOK x.val.1 [] x.val.1.length ∧ traceCost x.val.1 ≤ (CubeDeck.install table).slots ∧
        CubeDeck.At table (fr u) fresh (readings x.val.2.2) ∧ ∀ a < fresh, x.val.2.2 a=(original) u a := by
    obtain ⟨es,z,mz,run,cost,deck,keep,clean⟩ := CubeDeck.install_run table (fr u) fresh ((pub) u) ((mac) u) ((regs) u)
      ((original) u) (space u).1 (space u).2 wide (loadedFields u)
    exact ⟨⟨(es,z,mz),run⟩,⟨rfl,List.flatMap_eq_nil_iff.mpr fun e he => (clean e he).1,fun e he => (clean e he).2⟩,cost,deck,keep⟩
  choose init ok cost deck kept using one
  let loaded (u : Fin (R+1)) := (init u).val.2.2
  let scan (u : Fin (R+1)) := (ar).scanner (readings ((pub) u) 0) u.val (axis).val (ar).rowSelectorBits
  let actual := (ar).header.header+13
  let claim := (ar).header.header+13+(ar).header.entries
  have setup (u : Fin (R+1)) : PhysicalSetup (l:=scan u) A number (ar).powerBase (ar).vertexBase (ar).publicBase actual claim
      (decl).2 ((pub) u) (loaded u) := by
    have fit := CubeDeck.fits table (fr u) fresh (readings ((pub) u) 0) (space u).1 (space u).2 wide
    obtain ⟨metadata,received⟩ := writer.replayInputs_after_install ar decl group symbols u (fr u) (CubeDeck.entry table) count
      banks spacing (room u) (tab u) (frame u) (scanner u) fit (loadedFields u) (init u).property
    exact (ar).replaySetup (V.owners R) Fin.valEmbedding raw.1 u ((pub) u) (loaded u) decl (delivery.receivedRows g group)
      rfl emits (room u) metadata received
  have primary (u : Fin (R+1)) (j : ℕ) (low : j<112) (other : j≠13) :
      readings (loaded u) (readings ((pub) u) 0+j)=src u (readings ((pub) u) 0+j) := by
    have a := (Nat.add_lt_add_left low (readings ((pub) u) 0)).trans_le (room u).primary
    have keep := congrArg Fin.val (kept u _ ((Nat.add_lt_add_left low (readings ((pub) u) 0)).trans_le (space u).1))
    exact keep.trans (writer.returned_static ar (readings ((pub) u) 0) count (tab u) u _
      (a.trans_le (Evaluator.secondary_le_records ar)) (by rw [frame u]; exact Nat.add_left_cancel.mt other))
  have originalFrame (u : Fin (R+1)) : Frame.resident {(fr u) with count:=readings (loaded u) (readings ((pub) u) 0+46)}
      (readings ((pub) u)) (readings (loaded u)) := by
    obtain ⟨ds,_,rf,wd,vt⟩ := pointers u
    obtain ⟨z,o,rec,_⟩ := fields u
    exact ⟨rfl,(primary u 78 (by decide) (by decide)).trans (scanner u).triples,(primary u 79 (by decide) (by decide)).trans rec,
      (primary u 80 (by decide) (by decide)).trans rf,(primary u 45 (by decide) (by decide)).trans ds,
      (primary u 81 (by decide) (by decide)).trans z,(primary u 82 (by decide) (by decide)).trans o,
      (primary u 83 (by decide) (by decide)).trans wd,(primary u 84 (by decide) (by decide)).trans vt⟩
  obtain ⟨E,cert⟩ := V.native_owned_dictionary R raw scan (fun _ => packet) (fun _ => single) (fun _ => (ar).powerBase)
    (fun _ => (ar).vertexBase) (fun _ => (ar).publicBase) (fun _ => actual) (fun _ => claim) (decl).2 pub mac
    (fun u => (init u).val.2.1) loaded setup
  let c := ownedGroups L.dimension L.bitWidth L.copies L.alternatives L.supply
  let J := Equiv.piCongrRight (fun u => CubeDeck.prepend table c (init u))
  refine ⟨E.trans J,fun f => ?_⟩
  let next := V.withPrivate R raw f
  obtain ⟨teams,product⟩ := cert f
  constructor
  · intro u
    obtain ⟨bits,charge,read,_⟩ := teams u
    have ready := V.signed_cube_of_readback R next u header profile cells cables maxRows stride table params ((pub) u)
      (loaded u) (E f u).val.2.2 (offsets u) (control u) read (deck u) (originalFrame u)
      ((primary u 47 (by decide) (by decide)).trans (fields u).2.2.2)
      ((primary u 71 (by decide) (by decide)).trans (pointers u).destination) (room u).primary word (reportCap u) digits
    change DiagonalResidueRAM.TraceOK ((init u).val.1++(E f u).val.1) _ ((init u).val.1++(E f u).val.1).length ∧
      traceCost ((init u).val.1++(E f u).val.1) ≤ _ ∧ _
    exact ⟨by simpa only [List.nil_append,List.length_append] using (ok u).append bits,
      (RAMBuckets.cost_append ..).trans_le (Nat.add_le_add (cost u) charge),ready.1,ready.2,
      fun x own => read.views x (congrArg Fin.val own),loaded u,read,kept u⟩
  · refine (Finset.prod_congr rfl fun u _ => ?_).trans product
    exact V.cubeInputs_product R next u packet _ rfl table fresh _ fixed

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
