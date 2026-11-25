import OAI.Hierarchy.DescentTerminalPlacedHistogram
import OAI.Hierarchy.DescentTerminalPlacedChip
import OAI.Hierarchy.DescentTerminalBoot

namespace OAI
/-! # Admission from the original incoming history at its two physical address bands -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalRowArena DescentExteriorShelf DescentExterior DescentGL
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {blocks v B bw:ℕ} (V:Home.Format) (S:Shape) (I:Input) (R:MaskAllocation.Channels blocks)
variable (start header:ℕ) (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal:DescentTerminalEmitter.Compact.Literals I.sources)
local notation "C" => meter V R start
local notation "O" => registers V S R start header
local notation "b_" => afterMeter V S R start
local notation "orig" => takeOff S I b_
local notation "loaded" => input V S I R start header short literal
local notation "L" => layout S I b_ O
local notation "A" => rowArena S I b_
local notation "μ" => fun m:Memory bw=>Suffix.events S L (C).layout ((A).mount (loaded m))

theorem events_original (m:Memory bw) (early:Earlier S I b_ (C).layout bw) (room:last V S I R start<2^bw)
    {x:ℕ} (low:x< start) : μ m x=m x := by
  have floor:start≤b_:=by change start≤ start+_+_+_+_+3;omega
  have addr:x<b_:=low.trans_le floor
  have look:=before S I b_ O x (by change x<b_+2;omega)
  exact (Suffix.early S L (C).layout ((A).mount (loaded m)) (suffix_room S I b_ (C).layout O early room)
    look.original look.slot look.page).trans
    (((A).mount_before _ addr).trans (input_frame V S I R start header short literal m (.inl low)))

variable {K W q piece codes:ℕ} (front empty:ℕ) (z:DescentTerminalChipPins.Inputs K W q piece→Bool)
local notation "banks" => DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=q) (p:=piece) codes (L).emit front empty

/-- All ten startup views are authentic before the scalar emitter, and every read
through their full rounded allocation survives the later scalar and exterior passes. -/
theorem chip_started (m:Memory bw) (early:Earlier S I b_ (C).layout bw) (room:last V S I R start<2^bw)
    (before_:front+DescentTerminalBoot.total K W q piece codes≤ start)
    (kept:∀j<DescentTerminalBoot.total K W q piece codes,m (front+j)=DescentTerminalBoot.back z bw codes j) :
    DescentTerminalEmitter.Boot banks (μ m) z ∧
    (∀j:Fin (codes+1),(μ m) ((banks).scalar.pointer.base+j.val)=
      ((DescentTerminalScalarDispatch.pointers (fun a:Fin codes=>a.val*2^(q*(W*piece))))[j.val]'(by
        simpa [DescentTerminalScalarDispatch.pointers] using j.isLt):Word bw)) ∧
    ∀b∈[(banks).ySlices,(banks).scalar.payload,(banks).joinedX,(banks).xWords,(banks).highField,(banks).menuStart,(banks).denseROM,
        (banks).pointer,(banks).routeROM,(banks).scalar.pointer],∀j<b.size,
      DescentTerminalEmitter.BeforeKey S.terminal (L).emit (b.base+j) ∧
      DescentTerminalEmitter.AfterFlights S.terminal (L).emit (b.base+j) := by
  let lim:=DescentTerminalBoot.total K W q piece codes
  have prev:∀j<lim,(μ m) (front+j)=DescentTerminalBoot.back z bw codes j:=by
    intro j hj
    exact (events_original V S I R start header short literal m early room
      ((Nat.add_lt_add_left hj _).trans_le before_)).trans (kept j hj)
  have headers:=(DescentTerminalBoot.ranges z bw codes front (μ m) prev).1
  obtain ⟨boot,scalar⟩:=DescentTerminalChipBootWords.boot_of_suffix z bw codes (L).emit front empty (μ m) headers
  refine ⟨boot,scalar,?_⟩
  have len:DescentTerminalChipBootWords.total K W q piece codes≤lim:=Nat.le_add_right ..
  have floor:start≤b_:=by change start≤ start+_+_+_+_+3;omega
  have sub:b_≤orig:=((A).start_le 22).trans ((stages S I b_).1.trans (stages S I b_).2.1)
  let bnk:=DescentTerminalChipBootWords.bank K W q piece codes front
  have each (c:Fin 10) (i:ℕ) (ok:i<(bnk c).size):
      DescentTerminalEmitter.BeforeKey S.terminal (L).emit ((bnk c).base+i) ∧
      DescentTerminalEmitter.AfterFlights S.terminal (L).emit ((bnk c).base+i):=by
    have lower:(bnk c).base+i<orig:=calc
      _ < (bnk c).base+(bnk c).size := Nat.add_lt_add_left ok _
      _ ≤ front+DescentTerminalChipBootWords.total K W q piece codes := DescentTerminalChipBootWords.end_le _ _ _ _ _ _ c
      _ ≤ front+lim := Nat.add_le_add_left len _
      _ ≤ orig := before_.trans (floor.trans sub)
    constructor
    · constructor <;> change (bnk c).base+i<orig+_ <;> omega
    · apply after_start S I b_ O
      change (bnk c).base+i<orig+_;omega
  intro b hb i room_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact each 3 i room_
  · exact each 2 i room_
  · exact each 1 i room_
  · exact each 0 i room_
  · exact each 4 i room_
  · exact each 5 i room_
  · exact each 6 i room_
  · exact each 7 i room_
  · exact each 8 i room_
  · exact each 9 i room_

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
