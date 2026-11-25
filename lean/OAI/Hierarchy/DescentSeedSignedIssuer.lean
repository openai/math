import OAI.Hierarchy.DescentSeedSignedRaster
import OAI.Hierarchy.DescentSeedSignedFull

namespace OAI
/-! One executable first-stage signed census shared by every copy, block and histogram reader. -/
namespace Hierarchy.DescentPackedSeed.Signed.Plane
open DescentSeedRoot DescentInitialHost DescentKernelHistory DescentSixParty DescentColonies DescentSharedCableNames
open DescentSIMDLookup DescentSignedCableCodec DescentPackedColony
open Computability.BorderVNP.Crossing Catalyst CorrectionBatch
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F J : Type} [Field F] [Fintype J] [DecidableEq J] {k n R s r : ℕ}
    (X : Approximation F k n)
local notation "sockets" => 2*256
local notation "C" => Fintype.card (Vertex X)*(2*3)+1
local notation "b" => DescentSignedCableCodec.width 3 256

variable (G : PoweredGadget F) (digits : Fin R ≃ J×Block r) (c : (initialGroup X R s).Choice)
variable {ε : ℝ} (q : ℝ) (wire hist z : ℕ) (field : 0<r) (hq : 0<q)
    (hw : 0<wire) (hz : 0<z) (units : s=z*G.b) (room : 3*(wire*s)+hist≤256*(wire*s))
    (retained : (q*hist)*((R*Fintype.card X.network.copyGraph.Site:ℕ):ℝ)≤ε)
    (root : ((Fintype.card J*Fintype.card (Vertex X):ℕ):ℝ)*
      ((2:ℝ)^DescentHostDegree.packExponent 20 3*(q*((wire*s*256:ℕ):ℝ)))≤ε)
local notation "T" => source_group X G digits c q wire hist z field hq hw hz units room retained root

omit [Field F] [Fintype J] [DecidableEq J] in
private theorem chart_group_block (g : J) (x : Block r) (v : Vertex X) :
    vertexChart X digits (digits.symm (g,x),v) = ((g,v),x) := by
  change (((digits (digits.symm (g,x))).1,v),(digits (digits.symm (g,x))).2) = ((g,v),x)
  rw [digits.apply_symm_apply]

theorem issued {H groups M w i : ℕ} (base : ℕ) (v : Fin H→Vertex X) (m : Memory w)
    (bits : b*M≤w) (space : output X base H groups M+(sockets*H)*chunks groups M<2^w)
    (S : DescentCompiler.AtomSchedule)
    (ready : (source_group X G digits c q wire hist z field hq hw hz units room retained root).StateBounds S i)
    (groupRank : J↪ℕ)
    (groupsAt : Fin groups→J) (x : Block r) (s : Fin sockets) :
    Reads (page X base H groups M s)
      (fun h g=>DescentSignedCableCodec.encode (D:=3) (cap:=256)
        (Stage.signedPanel T (native X c) S ready (initialNames X (r:=r) groupRank) ((groupsAt g,v h),x) s))
      M (memory X (groups:=groups) (M:=M) base v m) := by
  have same (h : Fin H) (g : Fin groups) :
      Stage.signedPanel T (native X c) S ready (initialNames X (r:=r) groupRank) ((groupsAt g,v h),x) s=
        panelAt X (v h) s := by
    have eqn:=signed_at X G digits c q wire hist z field hq hw hz units room retained root S ready groupRank
      (digits.symm (groupsAt g,x)) (v h) s
    simpa only [chart_group_block] using eqn
  simpa only [same] using (run X base v m bits space).2.1 s

set_option maxHeartbeats 1200000 in
theorem padded_issued {H groups M w i : ℕ} (base : ℕ) (v : Fin H→Option (Vertex X)) (m : Memory w)
    (bits : b*M≤w) (space : output X base H groups M+(sockets*H)*chunks groups M<2^w)
    (S : DescentCompiler.AtomSchedule)
    (ready : (source_group X G digits c q wire hist z field hq hw hz units room retained root).StateBounds S i)
    (groupRank : J↪ℕ)
    (groupsAt : Fin groups→J) (x : Block r) (s : Fin sockets) :
    Reads (page X base H groups M s)
      (fun h g=>DescentSignedCableCodec.encode (D:=3) (cap:=256)
        ((v h).bind (fun vertex=>Stage.signedPanel T (native X c) S ready (initialNames X (r:=r) groupRank) ((groupsAt g,vertex),x) s)))
      M (paddedMemory X (groups:=groups) (M:=M) base v m) := by
  have same (h : Fin H) (g : Fin groups) :
      (v h).bind (fun vertex=>Stage.signedPanel T (native X c) S ready (initialNames X (r:=r) groupRank)
        ((groupsAt g,vertex),x) s)=(v h).bind (fun vertex=>panelAt X vertex s) :=by
    cases hv:v h with
    | none=>rfl
    | some vertex=>
      have eqn:=signed_at X G digits c q wire hist z field hq hw hz units room retained root S ready groupRank
        (digits.symm (groupsAt g,x)) vertex s
      simpa only [Option.bind_some,chart_group_block] using eqn
  have rows :
      (fun (h : Fin H) (g : Fin groups) => DescentSignedCableCodec.encode (D:=3) (cap:=256)
        ((v h).bind (fun vertex => Stage.signedPanel T (native X c) S ready
          (initialNames X (r:=r) groupRank) ((groupsAt g,vertex),x) s))) =
      (fun (h : Fin H) (_ : Fin groups) => DescentSignedCableCodec.encode
        ((v h).bind (fun vertex => panelAt X vertex s))) := by
    funext h g
    exact congrArg (DescentSignedCableCodec.encode (D:=3) (cap:=256)) (same h g)
  exact (congrArg (fun labels : Fin H → Fin groups → Cell b =>
    Reads (page X base H groups M s) labels M (paddedMemory X (groups:=groups) (M:=M) base v m))
    rows).mpr ((padded_run X base v m bits space).2.1 s)

end
end Hierarchy.DescentPackedSeed.Signed.Plane

end OAI
