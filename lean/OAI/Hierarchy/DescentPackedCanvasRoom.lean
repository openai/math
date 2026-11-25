import OAI.Hierarchy.DescentPackedCanvasPlacement

namespace OAI
/-! # Verify every pre-estimator lookup aperture in the relative address book -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Placement
open DescentPackedColony DescentPackedWalsh DescentPackedRectangle DescentPackedSingletonDepth
open DescentMeasuredHeader DescentBaseProfile DescentColonies ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (p : Placement) {w : ℕ}
local notation "H" => p.geo.hosts
local notation "D" => p.geo.ports
local notation "u" => p.geo.high
local notation "l" => p.geo.low
local notation "m" => u+l
local notation "N" => H*(m+1)+H*D
local notation "wordsPer" => N*2^u
local notation "M" => m-p.geo.f
local notation "Dbase" => p.scratch+(M+1)*pad H
local notation "measured" => @DescentPackedRectangle.metadata H u l D p.geo.meta
local notation "issued" => @DescentPackedRectangle.gather H u l D p.geo.meta (Bank.mk p.headerBase (Nat.clog 2 N))
  (Bank.mk p.first (rowBits H u)) p.peers

private theorem beginGuard : p.first+p.guardSize≤p.headerBase := by
  unfold headerBase scratch totals
  omega

private theorem span {B : Bank} (lower : B.base≤p.first) (length : B.size≤p.guardSize) :
    B.base+B.size≤p.headerBase := (Nat.add_le_add lower length).trans p.beginGuard

private theorem metaBefore (installed : p.geo.stop≤p.middle) :
    p.geo.meta+4*N+3*wordsPer≤p.first := by
  have lo:p.geo.meta+words H u l D≤p.geo.stop:=Nat.le_add_right ..
  have endBase:p.middle≤p.first:=Nat.le_add_right ..
  simpa only [words,Nat.add_assoc] using (lo.trans (installed.trans endBase))

private theorem depthBefore : Dbase+pad H≤p.headerBase := by
  have a:=Nat.mul_le_mul_right (pad H) (show M+2≤ m+2 by omega)
  rw [show M+2=(M+1)+1 by omega,Nat.succ_mul] at a
  unfold headerBase
  omega

theorem header_room (installed : p.geo.stop≤p.middle) (edges : ℕ) (edgeBase : edges≤p.first)
    (word : p.endAddress<2^w) :
    DescentMeasuredHeader.Fits (measured ⟨Dbase,Nat.clog 2 H⟩ ⟨edges,Nat.clog 2 (H*D)⟩)
      w H m D p.headerBase := by
  have static:=p.metaBefore installed
  have cut:=p.stops
  have hb:p.headerBase<2^w:=by omega
  have countLen:pad N≤p.guardSize:=by unfold guardSize;omega
  have peerLen:pad (H*D)≤p.guardSize:=by unfold guardSize;omega
  constructor
  · intro z hit
    simp only [Tape.banks,List.mem_cons,List.not_mem_nil,or_false] at hit
    rcases hit with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals refine fitsOf _ ?_ hb
    · exact p.span (B:=⟨p.geo.meta,Nat.clog 2 N⟩) (by change p.geo.meta≤p.first;omega) countLen
    · exact p.span (B:=⟨p.geo.meta+N,Nat.clog 2 N⟩) (by change p.geo.meta+N≤p.first;omega) countLen
    · exact p.span (B:=⟨p.geo.meta+2*N,Nat.clog 2 N⟩) (by change p.geo.meta+2*N≤p.first;omega) countLen
    · exact p.span (B:=⟨p.geo.meta+3*N,Nat.clog 2 N⟩) (by change p.geo.meta+3*N≤p.first;omega) countLen
    · exact p.depthBefore
    · exact p.span (B:=⟨edges,Nat.clog 2 (H*D)⟩) edgeBase peerLen
  · intro z hit
    simp only [Tape.fixed,List.mem_cons,List.not_mem_nil,or_false] at hit
    rcases hit with rfl|rfl|rfl|rfl <;> exact cover N
  · exact cover H
  · exact cover (H*D)

theorem predecessors (installed : p.geo.stop≤p.middle) :
    ∀B∈[(issued).kind,(issued).owner,(issued).pointer,(issued).sites,(issued).flows],B.base+B.size≤p.headerBase := by
  have st:=p.metaBefore installed
  have metadata : pad wordsPer≤p.guardSize:=by unfold guardSize;omega
  intro z h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact p.span (B:=⟨p.geo.meta+4*N+wordsPer,Nat.clog 2 wordsPer⟩) (by change p.geo.meta+4*N+wordsPer≤p.first;omega) metadata
  · exact p.span (B:=⟨p.geo.meta+4*N,Nat.clog 2 wordsPer⟩) (by change p.geo.meta+4*N≤p.first;omega) metadata
  · exact p.span (B:=⟨p.geo.meta+4*N+2*wordsPer,Nat.clog 2 wordsPer⟩) (by change p.geo.meta+4*N+2*wordsPer≤p.first;omega) metadata
  · exact p.span (B:=(issued).sites) le_rfl (by change page H u≤p.guardSize;unfold guardSize;omega)
  · exact p.span (B:=p.peers) (Nat.le_add_right ..) (by change pad (D*p.geo.pitch)≤p.guardSize;unfold guardSize;omega)

theorem gather_room (installed : p.geo.stop≤p.middle) (pitch : H*2^u≤p.geo.pitch)
    (out : ℕ) (after : p.endAddress≤out) (output : out+wordsPer<2^w) :
    DescentPackedRectangle.Room issued p.geo.pitch H u l D w out := by
  have cut:=p.stops
  have before:=p.predecessors installed
  have outWord:out<2^w:=by omega
  have base:p.headerBase≤out:=by omega
  have raw:p.headerBase+pad N≤out:=by unfold endAddress gainPage depthPage at after;omega
  constructor
  · intro z h
    simp only [Gather.banks,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals refine fitsOf _ ?_ outWord
    · exact (before (issued).owner (by simp)).trans base
    · exact (before (issued).kind (by simp)).trans base
    · exact (before (issued).pointer (by simp)).trans base
    · exact raw
    · exact (before (issued).sites (by simp)).trans base
    · exact (before (issued).flows (by simp)).trans base
  · exact cover wordsPer
  · exact cover wordsPer
  · exact cover wordsPer
  · exact cover N
  · exact rows_le H u
  · exact pitch
  · exact cover (D*p.geo.pitch)
  · exact output

theorem masks_room (installed : p.geo.stop≤p.middle) (count : Bank) (counted : count.base+count.size≤p.headerBase)
    (word : p.endAddress<2^w) (depth edges : Bank) :
    ∀B∈[(measured depth edges).owner,count,(⟨p.headerBase+N,Nat.clog 2 N⟩:Bank),
      (⟨p.headerBase+2*N,Nat.clog 2 N⟩:Bank)],B.Fits w p.depthPage := by
  have cutoff:=p.stops
  have d:p.depthPage<2^w:=by omega
  have pos:=p.metaBefore installed
  intro B h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl
  all_goals refine fitsOf _ ?_ d
  · have room : p.geo.meta+N+pad N≤p.headerBase :=
      p.span (B:=⟨p.geo.meta+N,Nat.clog 2 N⟩) (by change p.geo.meta+N≤p.first;omega)
        (by change pad N≤p.guardSize;unfold guardSize;omega)
    exact room.trans (by unfold depthPage;omega)
  · exact counted.trans (by unfold depthPage;omega)
  · change p.headerBase+N+pad N≤p.depthPage
    unfold depthPage;omega
  · change p.headerBase+2*N+pad N≤p.depthPage
    unfold depthPage;omega

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Placement

end OAI
