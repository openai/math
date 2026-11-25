import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleFold
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeDeck
import OAI.Computability.BorderVNP.CubeTeamOwnedArenaFacts
import OAI.Computability.BorderVNP.RoutingISATypedTaskWindows
import OAI.Computability.BorderVNP.DiagonalTallyReportAllocation

/-! # Joint physical allocation for the finite-field cube lookup

The immutable cube deck follows the routed input arena. Report controls follow
that deck, then the signed task windows and the three cube lookup arrays.
All reservations use the original public length capacities. Only the owned
vertex prefix is written and read by the team.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeAllocation

open RoutingISA BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open BorderVNP.Cube.Padding.Banks DiagonalTallyAllocation DiagonalTallyPacketEmit
open private packet_end_le from OAI.Computability.BorderVNP.CubeScatterPaddingBanksSide

variable {F : Type*} [Fintype F] (a : CubeArena.Layout)
variable (table : TableEntry a.n a.b a.h a.K a.s → F) (B : Bounds) (l : TypedTaskBuilder.Layout) (sw bw : ℕ)

local notation "stop" => CubeConstants.arenaEnd a.stop (CubeDeck.entry table)
local notation "width" => argumentWidth a.n a.b a.h a.K a.s
local notation "bank" => bankWidth a.n a.b a.h a.K a.s

/-- Use the true cube shape and the maximal public vertex count in the report allocation. -/
noncomputable def sizes : Bounds := {B with vertices := a.vertexCap, cubeWidth := width}

/-- The report controls and supplemental row source banks begin after the fixed field deck. -/
noncomputable def before : BeforeTasks := ⟨stop,sizes a B⟩

/-- All writable cell call, task, scratch and burst words follow the public inputs. -/
noncomputable def tasks : TypedTaskBuilder.Layout := l.windows (before a table B).limit sw bw

/-- Lookup rows, bit references and selected scalar words follow all signed task windows. -/
noncomputable def after : AfterTasks := ⟨l.windowsEnd (before a table B).limit sw bw,sizes a B⟩

/-- Frame supplied to the scalar cube lookup. The dynamic count is exactly the
published number of owned triples. -/
noncomputable def frame (count : ℕ) : Frame :=
  ⟨count,a.vertexBase,a.stop+2,(after a table B l sw bw).lookupRefs,(after a table B l sw bw).lookupRows,
    a.stop,a.stop+1,width,Fintype.card (Vertex (a.n+1))⟩

/-- Native counts of the real ordered roles fit the preallocated triple column. -/
theorem team_count (axis : Fin (a.n+1)) (owner : Fin a.header.d → ℕ) (t : ℕ) :
    (CubeVisits.teamList axis a.header.blocks owner t).length ≤ a.vertexCap := by
  let scan := a.scanner 0 t axis.val 0
  let total := scan.d*scan.d
  have c := CubeTriple.prefix_length (l:=scan) axis a.header.blocks owner total le_rfl
  have full : CubeTriple.visited axis a.header.blocks owner t total = CubeVisits.teamList axis a.header.blocks owner t := by
    simp only [CubeTriple.visited,CubeVisits.teamList,total,scan,CubeArena.Layout.scanner,
      List.take_of_length_le (show (List.finRange (a.header.d*a.header.d)).length ≤ a.header.d*a.header.d by simp)]
  have published := (congrArg List.length full).symm.trans c
  have cap := a.scanner_capacity 0 t axis.val 0 (TeamRows.wordOwner owner)
  change a.vertexBase+3*TeamRows.vertexPrefix scan (TeamRows.wordOwner owner) a.n a.header.blocks total ≤ a.vertexBase+3*a.vertexCap at cap
  exact published.le.trans (show TeamRows.vertexPrefix scan (TeamRows.wordOwner owner) a.n a.header.blocks total ≤ a.vertexCap by omega)

private theorem order : a.header.header ≤ a.header.packetBase ∧ a.header.packetBase ≤ a.packetEnd ∧
    a.packetEnd ≤ a.singleBank ∧ a.singleBank ≤ a.vertexBase ∧ a.publicBase ≤ a.stop ∧
    a.stop ≤ stop ∧ stop ≤ (before a table B).limit ∧ (before a table B).limit ≤ (after a table B l sw bw).start := by
  have sep := a.separated
  have pair : a.pairBase ≤ a.cellBank := Nat.le_add_right ..
  refine ⟨?_,Nat.le_add_right ..,?_,sep.2.1,sep.2.2.2.1.trans (pair.trans sep.2.2.2.2.2),?_,?_,?_⟩
  · unfold CubeHeaderInstall.Inputs.packetBase; omega
  · unfold CubeArena.Layout.singleBank; omega
  · unfold CubeConstants.arenaEnd CubeConstants.idBase; omega
  · rw [BeforeTasks.footprint]; dsimp only [before]; omega
  · dsimp only [after,TypedTaskBuilder.Layout.windowsEnd]; omega

/-- The deck, triple directory and every true packet-bank interval all precede
the cell call table and scratch arena, for this one fixed allocation. -/
theorem sources (A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s)
    (placed : A.packetBase = a.header.packetBase) {count : ℕ} (cap : count ≤ a.vertexCap) :
    let C := tasks a table B l sw bw
    C.SourceRange a.stop (stop-a.stop) ∧ C.SourceRange a.vertexBase (3*count) ∧
      ∀ p, C.SourceRange (A.packetAddr p) bank := by
  intro C
  obtain ⟨_,_,packetHi,singleHi,publicHi,deckStart,limit,_⟩ := order a table B l sw bw
  have vertexHi : a.vertexBase+3*count ≤ a.publicBase := Nat.add_le_add_left (Nat.mul_le_mul_left 3 cap) _
  have vertexLo : a.vertexBase ≤ a.publicBase := Nat.le_add_right ..
  have keep (base len : ℕ) (h : base+len ≤ (before a table B).limit) : C.SourceRange base len :=
    ⟨h.trans (by dsimp [C,tasks,TypedTaskBuilder.Layout.windows]; omega),.inl h⟩
  refine ⟨keep _ _ (by omega),keep _ _ (by omega),fun p => keep _ _ ?_⟩
  have row := packet_end_le A p
  rw [placed] at row
  change A.packetAddr p+bank ≤ a.packetEnd at row
  omega

/-- Every bound used by the native field lookup holds on the allocated addresses.
Only the top word needs to fit in the actual machine width. -/
theorem rooms (A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s)
    (placed : A.packetBase = a.header.packetBase) {w count origin : ℕ} (cap : count ≤ a.vertexCap)
    (frameRoom : origin+112 ≤ a.header.header) (space : (after a table B l sw bw).packed ≤ 2^w) :
    let f := frame a table B l sw bw count
    let dst := (after a table B l sw bw).ids
    origin+112 ≤ a.stop ∧ stop ≤ f.descriptors ∧ f.triples+3*f.count ≤ f.descriptors ∧
      (∀ p, A.packetAddr p+bank ≤ f.descriptors) ∧
      f.descriptors+2*f.count ≤ f.refs ∧ f.refs+f.count*width ≤ dst ∧ dst+f.count < 2^w := by
  intro f dst
  obtain ⟨head,packetLo,packetHi,singleHi,publicHi,deckStart,limit,afterStart⟩ := order a table B l sw bw
  have vertexHi : a.vertexBase+3*count ≤ a.publicBase := Nat.add_le_add_left (Nat.mul_le_mul_left 3 cap) _
  have vertexLo : a.vertexBase ≤ a.publicBase := Nat.le_add_right ..
  have start : stop ≤ f.descriptors := limit.trans afterStart
  have ref : f.refs = f.descriptors+2*a.vertexCap := rfl
  have pos : dst = f.refs+a.vertexCap*width := rfl
  have words : dst+a.vertexCap+1 ≤ 2^w := space
  change origin+112 ≤ a.stop ∧ stop ≤ f.descriptors ∧ a.vertexBase+3*count ≤ f.descriptors ∧
      (∀ p, A.packetAddr p+bank ≤ f.descriptors) ∧
      f.descriptors+2*count ≤ f.refs ∧ f.refs+count*width ≤ dst ∧ dst+count < 2^w
  refine ⟨by omega,start,by omega,fun p => ?_,by omega,?_,by omega⟩
  · have row := packet_end_le A p
    rw [placed] at row
    change A.packetAddr p+bank ≤ a.packetEnd at row
    omega
  · rw [pos]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ cap) _

end FiniteEvaluator.CubeAllocation

end BorderVNP
end Computability
end OAI
