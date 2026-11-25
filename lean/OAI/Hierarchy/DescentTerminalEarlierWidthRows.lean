import OAI.Hierarchy.DescentTerminalPlacedWidthReads

namespace OAI
/-! # Width-source retention from the original preflight into the row publishers -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalRowArena DescentTerminalHeaderDraft
open DescentTerminalDenseWindow DescentTerminalDenseHeader DescentTerminalDenseHeaderRAM
open DescentTerminalEmitter DescentTerminalVertexFields ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w q p n : ℕ} (A : Arena) (L : DescentTerminalHeaderSockets.Layout) (degree litBase paidRows : ℕ)
    (m : Memory w) (ok : DescentTerminalHeaderDraft.Room A L degree w)
    (boundary : litBase+4*DescentTerminalHeaderDraft.span paidRows≤A.start)
local notation "before_" => litMem litBase paidRows m
local notation "after_" => data A L degree before_

include ok boundary in
theorem preflight (positive : 0<w) :
    ((litProc w litBase paidRows).seq (machine A L degree w)).Exec m after_
        ((4+40*DescentTerminalHeaderDraft.span paidRows)+DescentTerminalHeaderDraft.clocks A L degree) ∧
      CheapCode ((litProc w litBase paidRows).seq (machine A L degree w)) ∧
      ∀x<litBase,after_ x=m x := by
  have fit := arenaFit A L degree ok
  have top := boundary.trans_lt ((A.start_le 22).trans_lt fit)
  obtain ⟨load_,one,_,frame⟩:=lit_install litBase paidRows m top
  obtain ⟨move,two⟩:=DescentTerminalHeaderDraft.any A L degree before_ ok positive
  refine ⟨@Procedure.Exec.then w _ _ m before_ after_ _ _ (@load_) (@move),
    @cheap_seq w _ _ (@one) (@two),?_⟩
  intro x hx
  have low : x<A.start := hx.trans_le ((Nat.le_add_right ..).trans boundary)
  exact (lowFrame A L degree before_ ok x low).trans (frame x (.inl hx))

include ok boundary in
theorem incoming_width {a : Fin n→Profile q p} (positive : 0<w) (layout : DescentTerminalDenseHeaderRAM.Layout)
    (below : ∀j,(inputBanks layout j).base+(inputBanks layout j).size≤litBase)
    (word : Reads layout a m) : Reads layout a after_ := by
  have kept := (preflight A L degree litBase paidRows m ok boundary positive).2.2
  apply five_reads word
  intro j z
  change after_ ((inputBanks layout j).base+z.val%(inputBanks layout j).size)=_
  exact kept _ ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le (below j))

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns

end OAI
