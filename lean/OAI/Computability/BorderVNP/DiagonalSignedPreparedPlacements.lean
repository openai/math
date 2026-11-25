import OAI.Computability.BorderVNP.DiagonalSignedNativePacketSeeds
import OAI.Computability.BorderVNP.DiagonalSignedPublishedSections

/-! # The signed placement table before the actual typed-task builder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock
open CellSparse CellSparse.Packet CellSparse.Packet.Source SiteWords CellPacket CellPacket.Supplement
open FragmentRows SignedTaskArena DiagonalTallyCellReports DiagonalTallyAllocation

variable {w n p d H description frame ctl offsets : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout}
    {O E : Type} (G : SiteWords.Directory (Fin n) O (a.cube.cells+1)) (ptr : O → E)
    (base : ℕ → ℕ) (slot : O → ℕ) (fs : O → List Factor) (l : CellControlRows.Layout) (raw : ℕ → ℕ)
set_option quotPrecheck false
local notation "top" => descriptorBank (ctl+37) p
local notation "pubRoom" => a.cube.cells+1+G.words.length+(a.cube.cells+1)≤2^p
local notation "descRoom" => a.cube.cells+1+(Schema.coords (G.referenceRows ptr).length).length+(a.cube.cells+1)≤2^d

/-- Use the runtime receiving-bank words and exactly the same scratch and burst
pointers as the native task builder. Every geometric source address comes from
the literal start marker returned by the public emitter. -/
noncomputable def signedPlaces (hf : pubRoom) (hs : descRoom) : Fin (a.cube.cells+1) → Placed O :=
  atRanges (dest:=ctl+37) (H:=H) G ptr hf hs base slot fs
    (fun c => raw (l.banks+2*c.val+1)) (fun c => l.scratch+l.scratchStride*c.val)
    (fun c => l.bursts+l.burstStride*c.val) (fun c => denseReportBits l.toLayout raw c.val)

variable {pub : Arg → Word w} {m : Memory w} {s : RoutingISA.Bank w} {mac : TeamOpcode.Macros w 8}
    {banks : CellBanks.Layout} {rl : ReportLayout} {reports : List (ReportCell rl)} {q : ReportCursor}

/-- A single returning public packet fixes the task metadata for every real
cell and its spare. The rank, original dense extent, descriptor address,
public count words, and literal post-report RAM are all for the same cell. -/
theorem Published.signed_prepared_placements {args : E → ℕ} (out : Published G p d (ctl+37) H ptr args base)
    (addresses : ∀ i, args (ptr i)=slot i) (alloc : ReportAllocation a.before a.after banks rl reports q)
    (seed : PreparedReportInput pub m reports q description) (r : Returns prepareCellReports pub mac s m)
    {fit : f.Fits w (readings r.val.2.2)} {cells : a.fragments.cells=f.cells} (e : SparseEmission a f r.val.2.2 fit cells)
    (place : a.SparsePlacement frame ctl) (gp : SparseGeometry a f offsets ctl)
    (fromControls : ∀ z, ctl+37≤z → z<a.cube.header.header → readings m z=base z)
    (physical : banks.bankStart=a.cube.cellBank) (frameEq : rl.frame=frame)
    (sorted : l.sorted=top) (padded : l.padded=2^d)
    (stops : l.stops=a.cube.cells+1+(Schema.coords (G.referenceRows ptr).length).length)
    (tableRoom : top+2*(2^d)≤a.cube.header.header)
    (ranks : ∀ i : Fin (2^d), base (top+(2^d+i.val))<2^d) :
    ∃ hf : pubRoom, ∃ hs : descRoom,
    let src := readings e.output
    let places := signedPlaces (ctl:=ctl) (H:=H) G ptr base slot fs l src hf hs
    TypedBatch.SourceShape places G ∧
    ∀ c : Fin a.cube.cells, let row := places c.castSucc
      let geom := row.publicBase+((prefixParts row).flatMap Part.publicBuffer).length
      let stop := top+base (top+(2^d+(Markers.stop hs c.castSucc).val))
      src (l.sorted+l.padded+(l.stops+c.val))-src (l.sorted+l.padded+c.val)-1=3*(row.parts.length+3) ∧
        src (l.offsets+2*l.cables+c.val)+src (l.tails+c.val)=row.external.length ∧
        l.sorted+src (l.sorted+l.padded+c.val)+1=row.descriptorBase ∧
        CellMemory row geom stop (readings r.val.2.2) ∧
        (ctl+37≤row.descriptorBase ∧ stop≤a.cube.header.header) ∧
        (ctl+37≤row.publicBase ∧ geom≤a.cube.header.header) ∧
        (ctl+37≤geom ∧ geom+(fieldList record row.rows++fieldList vector row.reports).length≤a.cube.header.header) := by
  let src := readings e.output
  let ext := fun c : Fin (a.cube.cells+1) => src (l.banks+2*c.val+1)
  let scratch := fun c : Fin (a.cube.cells+1) => l.scratch+l.scratchStride*c.val
  let burst := fun c : Fin (a.cube.cells+1) => l.bursts+l.burstStride*c.val
  let bytes := fun c : Fin (a.cube.cells+1) => denseReportBits l.toLayout src c.val
  obtain ⟨hf,hs,shape,original⟩ := out.places G ptr base slot fs ext scratch burst bytes addresses
  refine ⟨hf,hs,shape,?_⟩
  intro c row geom stop
  have loBank : ctl+37≤top := Nat.le_add_right ..
  have rankKept (i : Fin (2^d)) : src (top+(2^d+i.val))=base (top+(2^d+i.val)) :=
    signed_geometry_on_fragment alloc seed r e place gp base fromControls physical frameEq _ (by omega) (by have := i.isLt; omega)
  have spans := (atRanges_produced_memory (dest:=ctl+37) (hdr:=H) G ptr hf hs base slot fs ext scratch burst bytes
    l src sorted padded stops rankKept original).1 c.castSucc
  have marker : l.sorted+src (l.sorted+l.padded+c.val)+1=row.descriptorBase := by
    have load := rankKept (Markers.start hs c.castSucc)
    change l.sorted+src (l.sorted+l.padded+c.val)+1=top+base (top+(2^d+c.val))+1
    rw [sorted,padded,Nat.add_assoc top (2^d) c.val]
    exact congrArg (fun v => top+v+1) load
  have lower₁ : ctl+37≤row.descriptorBase := by
    change ctl+37≤top+base (top+(2^d+c.val))+1
    omega
  have upper₁ : stop≤a.cube.header.header := by
    have hi := ranks (Markers.stop hs c.castSucc)
    dsimp only [stop]
    omega
  have lower₂ : ctl+37≤row.publicBase := by
    change ctl+37≤(ctl+37)+base ((ctl+37)+(2^p+c.val))+1
    omega
  obtain ⟨_,_,_,ending,_⟩ := out.ordinary_region place.beforeControl c
  have total : row.publicBase+(row.parts.flatMap Part.publicBuffer).length≤top := ending
  have countWord : geom+(fieldList record row.rows++fieldList vector row.reports).length≤top := by
    change row.publicBase+((prefixParts row).flatMap Part.publicBuffer).length+_ ≤ _
    have parts : row.parts = prefixParts row ++ [.publicWords (fieldList record row.rows++fieldList vector row.reports)] := by
      simp [Placed.parts,plan,prefixParts]
    simpa only [parts,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,Part.publicBuffer,
      List.length_append,Nat.add_assoc] using total
  have lower₃ : ctl+37≤geom := lower₂.trans (Nat.le_add_right ..)
  have upper₃ : geom+(fieldList record row.rows++fieldList vector row.reports).length≤a.cube.header.header := by omega
  have wordHi : geom≤a.cube.header.header := by omega
  have startImage := (original c.castSucc).at_checkpoint (lo:=ctl+37) (hi:=a.cube.header.header)
    ⟨lower₁,upper₁⟩ ⟨lower₂,wordHi⟩ ⟨lower₃,upper₃⟩ fromControls
  have safe : rl.frame+35<ctl+37 := by rw [frameEq]; have := place.beforeControl; omega
  have keep := startImage.report_return alloc seed r (lo:=ctl+37) (hi:=a.cube.header.header)
    ⟨safe,physical ▸ a.open_table_order.1⟩ ⟨lower₁,upper₁⟩ ⟨lower₂,wordHi⟩ ⟨lower₃,upper₃⟩
  exact ⟨spans,(denseReportBits_length l.toLayout _ _).symm,marker,keep,⟨lower₁,upper₁⟩,⟨lower₂,wordHi⟩,lower₃,upper₃⟩

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
