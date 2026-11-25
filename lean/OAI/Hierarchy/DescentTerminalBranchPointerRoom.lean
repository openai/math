import OAI.Hierarchy.DescentTerminalPlacedAdmission
import OAI.Hierarchy.DescentTerminalChipBootExtent
import OAI.Hierarchy.DescentTerminalBoot

namespace OAI
/-! # Scalar-pointer and gate read bounds for the placed terminal branch -/

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalChipBootWords DescentTerminalRowArena
noncomputable section
set_option quotPrecheck false


variable {K W q piece : ℕ} (S : Shape) (I : Input) (base : ℕ) (O : DescentPrivateExponentRAM.Banks)
    (codes front empty : ℕ)
local notation "E" => (layout S I base O).emit
local notation "G" => chipBanks (K:=K) (W:=W) (q:=q) (p:=piece) codes E front empty
local notation "origin" => takeOff S I base

/-- Each nonzero scalar code has a cell in original ROM column nine. -/
theorem branch_pointer_below (before_ : front+DescentTerminalBoot.total K W q piece codes≤base)
    (j : Fin codes) : (G).scalar.pointer.base+(j.val+1)<base := by
  let col:=bank K W q piece codes front (9 : Fin 10)
  have enough : codes+1≤col.size := by
    change codes+1≤2^(Nat.clog 2 (codes+1))
    exact Nat.le_pow_clog (by decide) _
  have cell : j.val+1<col.size := (Nat.succ_lt_succ j.isLt).trans_le enough
  have end_ : col.base+col.size≤front+total K W q piece codes := end_le _ _ _ _ _ _ 9
  have both : total K W q piece codes≤DescentTerminalBoot.total K W q piece codes := Nat.le_add_right ..
  exact (Nat.add_lt_add_left cell col.base).trans_le (end_.trans ((Nat.add_le_add_left both front).trans before_))

/-- Every pointer used by the sparse dispatch survives both native publication passes. -/
theorem branch_pointer_safe (before_ : front+DescentTerminalBoot.total K W q piece codes≤base)
    (j : Fin codes) :
    DescentTerminalEmitter.BeforeKey S.terminal E ((G).scalar.pointer.base+(j.val+1)) ∧
      DescentTerminalEmitter.AfterFlights S.terminal E ((G).scalar.pointer.base+(j.val+1)) := by
  have start : base≤origin := ((rowArena S I base).start_le 22).trans
    ((stages S I base).1.trans (stages S I base).2.1)
  have prev:= (branch_pointer_below S I base O codes front empty before_ j).trans_le start
  constructor
  · constructor <;> change (G).scalar.pointer.base+(j.val+1)<origin+_ <;> omega
  · apply after_start S I base O
    change (G).scalar.pointer.base+(j.val+1)<origin+_
    omega

/-- The same address is representable at the actual machine width. -/
theorem branch_pointer_room {w : ℕ} (before_ : front+DescentTerminalBoot.total K W q piece codes≤base)
    (endFit : endAddress S I base<2^w) (j : Fin codes) :
    (G).scalar.pointer.base+(j.val+1)<2^w := by
  obtain ⟨a,b,c,d,e⟩:=stages S I base
  have start : base≤endAddress S I base := ((rowArena S I base).start_le 22).trans
    (a.trans (b.trans (c.trans (d.trans e))))
  exact (branch_pointer_below S I base O codes front empty before_ j).trans (start.trans_lt endFit)

/-- Gate words occupy the sixth emitter region. The allocation reserves all
three words per row before the seventh region, where the leaf cells start. -/
theorem branch_gate_life (live : S.terminal.rows=K*W) (i : Fin (K*W)) :
    (G).gate.base+3*i.val<(E).leaf.cells.base ∧ (G).gate.base+3*i.val<(E).scalar := by
  let t:=DescentTerminalDataPlane.Arena.finish S.terminal.plane origin
  let n:=DescentTerminalEmitter.Allocation.slab S.terminal I.indexEvents I.formatEvents
  have sized:=DescentTerminalEmitter.Allocation.reserve_fit S.terminal I.indexEvents I.formatEvents
  change 3*(S.terminal.rows+S.terminal.pool+S.terminal.leaves+I.indexEvents+I.formatEvents+1)≤n at sized
  have lt : i.val<S.terminal.rows := by rw [live];exact i.isLt
  change t+6*n+3*i.val<t+7*n ∧ t+6*n+3*i.val<t+9*n
  omega

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
