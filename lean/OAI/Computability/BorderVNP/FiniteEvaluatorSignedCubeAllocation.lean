import OAI.Computability.BorderVNP.FiniteEvaluatorCubeReadLocation
import OAI.Computability.BorderVNP.RoutingISASignedTaskArena
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedCube

/-! # Field lookup addresses in the signed evaluator's physical allocation

Its task and lookup buffers follow the full compressed-fragment allocation,
the report metadata and the actual private task windows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks
open FiniteEvaluator VPVNP.BurstRAM DiagonalTallyAllocation DiagonalTallyPacketEmit
open private packet_end_le from OAI.Computability.BorderVNP.CubeScatterPaddingBanksSide

/-- The field lookup frame at the actual post-fragment task pointers. -/
noncomputable def Layout.lookupFrame (l : Layout) (count : ℕ) : Frame :=
  ⟨count,l.cube.vertexBase,l.cube.stop+2,l.after.lookupRefs,l.after.lookupRows,l.cube.stop,l.cube.stop+1,
    argumentWidth l.cube.n l.cube.b l.cube.h l.cube.K l.cube.s,Fintype.card (Vertex (l.cube.n+1))⟩

variable (l : Layout)

private theorem lookup_order : l.cube.header.header ≤ l.cube.header.packetBase ∧
    l.cube.header.packetBase ≤ l.cube.packetEnd ∧ l.cube.packetEnd ≤ l.cube.vertexBase ∧
    l.cube.publicBase ≤ l.cube.stop ∧ l.cube.stop ≤ CubeConstants.arenaEnd l.cube.stop l.id ∧
    CubeConstants.arenaEnd l.cube.stop l.id ≤ l.before.limit ∧ l.before.limit ≤ l.after.start := by
  have parts := l.cube.separated
  have before : l.before.start ≤ l.before.limit := by rw [BeforeTasks.footprint]; omega
  refine ⟨?_,Nat.le_add_right ..,?_,parts.2.2.2.1.trans ((Nat.le_add_right ..).trans parts.2.2.2.2.2),
    ?_,l.constants_le_before.trans before,?_⟩
  · unfold CubeHeaderInstall.Inputs.packetBase; omega
  · apply le_trans _ parts.2.1
    unfold CubeArena.Layout.singleBank
    omega
  · unfold CubeConstants.arenaEnd CubeConstants.idBase; omega
  · dsimp only [Layout.after,TypedTaskBuilder.Layout.windowsEnd]; omega

/-- The live triples and all packet payloads are below the installed field deck. The
real fragment area, report metadata and private tasks then separate that deck from
the actual generated descriptor, reference and ID arrays. -/
theorem Layout.lookup_rooms {w base count : ℕ}
    (A : Data l.cube.n l.cube.header.d l.cube.header.blocks l.cube.b l.cube.h l.cube.K l.cube.s)
    (placed : A.packetBase = l.cube.header.packetBase) (tripleCap : count ≤ l.cube.vertexCap)
    (reportCap : count ≤ l.p.report.vertices) (digits : argumentWidth l.cube.n l.cube.b l.cube.h l.cube.K l.cube.s ≤ l.p.report.cubeWidth)
    (primary : base+112 ≤ l.cube.header.header) (fit : l.after.packed ≤ 2^w) :
    let f := l.lookupFrame count
    base+112 ≤ l.cube.stop ∧ CubeConstants.arenaEnd l.cube.stop l.id ≤ f.descriptors ∧
      f.triples+3*f.count ≤ f.descriptors ∧
      (∀ p, A.packetAddr p+bankWidth l.cube.n l.cube.b l.cube.h l.cube.K l.cube.s ≤ f.descriptors) ∧
      f.descriptors+2*f.count ≤ f.refs ∧ f.refs+f.count*f.width ≤ l.after.ids ∧ l.after.ids+f.count < 2^w := by
  intro f
  obtain ⟨head,pack,ends,pub,deck,limit,tasks⟩ := lookup_order l
  have high : l.cube.vertexBase+3*count ≤ l.cube.publicBase := Nat.add_le_add_left (Nat.mul_le_mul_left 3 tripleCap) _
  have verts : l.cube.vertexBase ≤ l.cube.publicBase := Nat.le_add_right ..
  have cap : count ≤ l.after.bound.vertices := reportCap
  have separate := l.after.lookup_separated cap
  have space : f.refs+count*f.width ≤ f.refs+count*l.after.bound.cubeWidth :=
    Nat.add_le_add_left (Nat.mul_le_mul_left count digits) _
  change base+112 ≤ l.cube.stop ∧ CubeConstants.arenaEnd l.cube.stop l.id ≤ l.after.start ∧
    l.cube.vertexBase+3*count ≤ l.after.start ∧ (∀ p, A.packetAddr p+_ ≤ l.after.start) ∧ _ ∧ _ ∧ _
  refine ⟨by omega,by omega,by omega,?_,separate.1,space.trans separate.2.1,separate.2.2.1.trans_le fit⟩
  intro p
  have bound := packet_end_le A p
  rw [placed] at bound
  change A.packetAddr p+_ ≤ l.cube.packetEnd at bound
  omega

/-- All lookup inputs precede the genuine signed team's call and task outputs. -/
theorem Layout.lookup_sources {count : ℕ} (team frame offsets control : ℕ)
    (A : Data l.cube.n l.cube.header.d l.cube.header.blocks l.cube.b l.cube.h l.cube.K l.cube.s)
    (placed : A.packetBase = l.cube.header.packetBase) (cap : count ≤ l.cube.vertexCap) :
    let t := l.tasks team frame offsets control
    let endDeck := CubeConstants.arenaEnd l.cube.stop l.id
    t.SourceRange l.cube.stop (endDeck-l.cube.stop) ∧ t.SourceRange l.cube.vertexBase (3*count) ∧
      ∀ p, t.SourceRange (A.packetAddr p) (bankWidth l.cube.n l.cube.b l.cube.h l.cube.K l.cube.s) := by
  intro t endDeck
  obtain ⟨_,_,ends,pub,deck,limit,_⟩ := lookup_order l
  have bound : l.cube.vertexBase+3*count ≤ l.cube.publicBase := Nat.add_le_add_left (Nat.mul_le_mul_left 3 cap) _
  have keep (base len : ℕ) (low : base+len ≤ l.before.limit) : t.SourceRange base len :=
    ⟨low.trans (by dsimp [t,Layout.tasks,TypedTaskBuilder.Layout.windows]; omega),.inl low⟩
  refine ⟨keep _ _ (by dsimp only [endDeck]; omega),keep _ _ (by omega),fun p => keep _ _ ?_⟩
  have packet := packet_end_le A p
  rw [placed] at packet
  change A.packetAddr p+_ ≤ l.cube.packetEnd at packet
  omega

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
