import OAI.Computability.BorderVNP.PackedTerminalSignedGridEmitterCost
import OAI.Computability.BorderVNP.DiagonalSignedPublishedSections
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenRoom
import OAI.Computability.BorderVNP.CubeRouteDataLayouts
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomDirectories

/-! # The two original-bundle banks following the selected signed cell packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open CellPacketGeometry Packing.RoutingOutputs GeometryAdvice TerminalCells

/-- The original-bundle payloads and their inverse ranks begin after every
word of the signed cell packet. The next arena can start at the real geometry
allocation's stop. This bounds all three sort regions at the same word
width used by the actual output instruction. -/
theorem signed_bundle_bank_room (fresh reserve gates cables cells originals live p d depth field w : ℕ) :
    let ordinary := signedGridOutputCount cables cells originals live 37 (Total p d)
    let outputs := ordinary+(2^depth+2^depth)
    let dest := Allocation.dest fresh reserve gates outputs field
    let ctrl := controlsBase dest cables cells originals live
    let start := packetBase dest cables cells originals live 37
    let payload := start+Total p d
    let inverse := payload+2^depth
    let next := Allocation.stop fresh reserve gates outputs field w
    next < 2^w →
      start=ctrl+37 ∧ payload=dest+ordinary ∧ inverse+2^depth=dest+outputs ∧
      ctrl+37 ≤ next ∧ payload+2^depth ≤ next ∧ inverse+2^depth ≤ next ∧
      start+2^p < 2^w ∧ 2^d ≤ 2^w ∧ start+Total p d < 2^w ∧ 2^depth ≤ 2^w := by
  intro ordinary outputs dest ctrl start payload inverse next fit
  have last : dest+outputs ≤ next := by
    change dest+outputs ≤ dest+outputs+_+_
    omega
  have packet : payload=dest+ordinary := by
    dsimp only [payload,start,ordinary,signedGridOutputCount,packetBase,controlsBase,bases,count]
    omega
  have endBanks : inverse+2^depth=dest+outputs := by dsimp only [inverse,outputs]; omega
  have positive : 0<(2:ℕ)^depth := by positivity
  have pubPositive : 0<(2:ℕ)^p := by positivity
  have descPositive : 0<(2:ℕ)^d := by positivity
  have ranks : inverse=payload+2^depth := rfl
  have total : start+((2^p+2^p)+(2^d+2^d))=payload := rfl
  have history : start=ctrl+37 := rfl
  omega

open RoutingISA.SignedTaskArena

/-- The real output offsets fill the open cell scanner's entire address
rectangle, including both original-bundle banks. Its only later allocation
bound is the task's own end, supplied by the selected signed task range. -/
theorem openRoom_of_appended_banks (t : Layout)
    (frame fresh reserve gates originals live p d depth field w chunks : ℕ) :
    let ordinary := signedGridOutputCount t.cube.cables t.cube.cells originals live 37 (Total p d)
    let outputs := ordinary+(2^depth+2^depth)
    let dest := Allocation.dest fresh reserve gates outputs field
    let ptr := bases dest t.cube.cables t.cube.cells originals
    let ctrl := controlsBase dest t.cube.cables t.cube.cells originals live
    let start := packetBase dest t.cube.cables t.cube.cells originals live 37
    let dirs := GeometryDirectories.published start p d (t.cube.cells+1) chunks ctrl (Total p d) depth
    let next := Allocation.stop fresh reserve gates outputs field w
    frame+112 ≤ fresh → t.cube.header.header = next → next<2^w →
      t.p.bundlePayload = dirs.bundlePayload → t.p.bundleInverse = dirs.bundleInverse →
      t.cube.cells+6*originals+t.cube.cells ≤ 2^depth → t.cube.cells ≤ t.p.report.cells →
      originals ≤ t.p.report.bundles → t.before.limit < 2^w →
      t.OpenRoom frame ptr.ends ctrl ptr.livePairs live originals (2^depth) w := by
  intro ordinary outputs dest ptr ctrl start dirs next low head stop first second markers cells bundles top
  have room := signed_bundle_bank_room fresh reserve gates t.cube.cables t.cube.cells originals live p d depth field w stop
  have after : fresh ≤ dest := by dsimp only [dest,Allocation.dest,Allocation.temp]; omega
  have address : ctrl+37 ≤ t.cube.header.header := head.symm ▸ room.2.2.2.1
  have host : t.cube.header.header ≤ t.cube.hostDirectory := by
    obtain ⟨_,_,_,_,_,_,_,_⟩ := t.cube.writer_order
    omega
  have crop : dest ≤ ptr.ends ∧ ptr.ends+2*t.cube.cables+t.cube.cells ≤ ctrl ∧
      dest ≤ ptr.livePairs ∧ ptr.livePairs+2*live+t.cube.cells ≤ ctrl := by
    dsimp only [ctrl,ptr,controlsBase,bases]
    omega
  have bank := t.open_table_order.1
  have lower := low.trans after
  have roomP : t.p.bundlePayload+2^depth ≤ t.cube.header.header := by
    rw [first,head]
    exact room.2.2.2.2.1
  have roomI : t.p.bundleInverse+2^depth ≤ t.cube.header.header := by
    rw [second,head]
    exact room.2.2.2.2.2.1
  exact ⟨by omega,by omega,by omega,by omega,by omega,address,roomP,roomI,markers,cells,bundles,top⟩

end PackedHistoryCircuit.Retained

end BorderVNP
end Computability
end OAI
