import OAI.Computability.BorderVNP.FiniteProfileSlottedNetwork
import OAI.Computability.BorderVNP.CubeRouteJointPacket
import OAI.Computability.BorderVNP.RoutingISASignedFrame

/-! # The finite candidate's common routing, geometry and cube frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open PackedHistoryCircuit Packing RoutingOutputs GeometryAdvice DiagonalResidueRAM CubeHeaderInstall

variable {R r lit link inner n w o nt ng : ℕ} {Edge : Type} {Q Γ : Type} {K : Type*} [Field K]
variable (G : Wiring R r lit 0 link inner n Edge) (L : Routing.WireLayout (R+1) r link) (u : Fin (R+1))
variable (ext : Exterior R r link → Bool) (bank : Bank w)
variable (lib : Fin 8 → TeamSite.Macro Q Γ nt ng) (ret : FieldProcessor.Returns Q Γ K nt 8) (fuel : ℕ)

set_option maxRecDepth 4500 in
/-- One concrete wide extension supplies both the geometry output schema and
the true native cube-table pointers, including the host bank at word 72. -/
theorem FrontReceipt.routing_headers (task : SignedTaskArena.Layout) (D : Directory.Layout)
    (other : Arg → Word w) (old : Fin 81 → Word w)
    (raw subt start clock fresh origin profile gates outputs width off ell : ℕ)
    (hdr : List Bool) (words : Fin o → ℕ) :
    let A := ProfileArena.arena G L ([] : List (Word w))
    let extra := signedProfileExtension task old D origin task.cube.cables task.cube.cells raw u.val subt
      fresh profile gates outputs width off ell
    let B := ProfileArena.operands G L ([] : List (Word w)) extra Fin.elim0 start u
    let other' := withDemandBase (task.routeBank A.frame other) A.next
    let pub := B.bank (core other' origin task.cube.cables task.cube.cells)
    let F := G.processorFields u Fin.elim0 ext A.ibase A.hbase A.dense
    B.Fits w → A.next ≤ fresh → A.next < 2^w → task.cube.stop < 2^w →
    controlsBase origin task.cube.cables task.cube.cells D.entries (D.teams*D.sites)+8 < 2^w →
    ∀ z : Returns profileFront pub (TeamSiteEvents.macros lib fuel) bank (processorMemory F w),
    FrontReceipt G u ext A.ibase A.hbase A.dense L.header A.broadcastBase pub bank lib ret fuel z A.copied extra
      hdr clock fresh origin words →
      (pub 0).val=A.frame ∧ (extra 41).val=task.cube.hostDirectory ∧
      Header A.frame origin task.cube.cables task.cube.cells D.entries (readings z.val.2.2) ∧
      readings z.val.2.2 (A.frame+92)=controlsBase origin task.cube.cables task.cube.cells D.entries (D.teams*D.sites) ∧
      readings z.val.2.2 (A.frame+8)=A.next := by
  intro A extra B other' pub F fitted reserve small room control z receipt
  have frame : (pub 0).val=A.frame := B.frameBase_word _ fitted
  have fr : A.frame+112 ≤ A.broadcastBase := by change A.frame+112 ≤ A.frame+112+A.copied; omega
  have ib : A.broadcastBase+L.header=A.ibase := rfl
  have hb : A.ibase+A.count=A.hbase := rfl
  have nx : A.hbase+A.count=A.next := rfl
  obtain ⟨_,ordinary,extended⟩ := receipt.route_sources G u ext A.ibase A.hbase A.dense L.header
    A.broadcastBase pub bank lib ret fuel (frame ▸ fr) (by omega) (by omega) (by change A.ibase+A.count ≤ fresh; omega)
  let prev := pinFields (task.extension raw u.val subt old) (Allocation.stop fresh profile gates outputs width w)
    task.cube.header.d (task.cube.n+1) (task.cube.h*task.cube.b) task.cube.header.blocks profile
    (Cube.Physical.declarationCap task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.s)
  have before := routing_frame_of_words B other' (directoryFields prev D) origin task.cube.cables task.cube.cells D.entries
    (D.teams*D.sites) fresh profile gates outputs width off ell z.val.2.2 (by omega) ordinary (fun i => by
      rw [extended i]; exact congrFun (signedProfileExtension_geometry ..) i)
  have hostFit : task.cube.hostDirectory<2^w := by
    have ord := task.cube.writer_order
    omega
  have get : (extra 41).val=task.cube.hostDirectory := by
    rw [show extra 41=task.extension raw u.val subt old 41 from signedProfileExtension_taskWord task old D origin task.cube.cables task.cube.cells raw u.val subt fresh profile gates outputs width off ell 41 (by decide)]
    rw [task.extension_cube raw u.val subt old 41 (by decide)]
    exact Nat.mod_eq_of_lt hostFit
  have rawAt := congrArg Fin.val (ordinary (8 : Fin 31))
  have arg : (pub 9).val=A.next := Nat.mod_eq_of_lt small
  exact ⟨frame,get,frame ▸ before.header,frame ▸ before.control,frame ▸ rawAt.trans arg⟩

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
