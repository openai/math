import OAI.Hierarchy.DescentTerminalMaskCounter

namespace OAI
/-! # Literal seven-slot tariff of the final native mask and field multiplicity gate -/
namespace Hierarchy.DescentTerminalVertexFields.MaskAllocation
open DescentTerminalSiteShelves DescentTerminalRecipeRows ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentCompiler.TerminalScale ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {q t H N A p groups blocks sites V B bw : ℕ}
local notation "F₀" => Fin (channels blocks)
local notation "size" => channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
local notation "cap" => cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
variable (R : Channels blocks) (base header : ℕ)
local notation "cells" => marks size+cap
local notation "C" => counter (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) R base
local notation "O" => PrivateCounter.registers C header sites cap
local notation "clock" => privateMaskedClock cells cap sites blocks p
local notation "phase" => PrivateCounter.machine (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=sites) (bw:=bw) C O
local notation "fetch" proof => program (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p)
  (groups:=groups) (blocks:=blocks) (V:=V) (B:=B) proof bw base


theorem terminal_names (fit : V * span q t H N A p ≤ B) :
    DescentStaticWordColumn.names ((fetch fit).seq phase)≤privateMaskedNames cells cap blocks p := by
  have load : DescentStaticWordColumn.names (fetch fit)=15*(cells+1) :=
    names (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (blocks:=blocks) base fit
  have count : DescentStaticWordColumn.names phase≤privateHomeNames cap blocks p :=
    PrivateCounter.hardware (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups)
      (homes:=sites) (bw:=bw) C O
  rw [DescentStaticWordColumn.names_seq,load]
  exact Nat.add_le_add_left count _

theorem terminal_native_tariff (fit : V * span q t H N A p ≤ B) {T fund factor : ℕ}
    (paid : (clock+privateMaskedNames cells cap blocks p)*bw*T≤3213*factor*fund) :
    (clock+7*DescentStaticWordColumn.names ((fetch fit).seq phase))*bw*T≤22491*factor*fund := by
  have namesBound : DescentStaticWordColumn.names ((fetch fit).seq phase) ≤ privateMaskedNames cells cap blocks p :=
    terminal_names (sites:=sites) (bw:=bw) R base header fit
  calc
    _ ≤ (7*(clock+privateMaskedNames cells cap blocks p))*bw*T :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    _ = 7*((clock+privateMaskedNames cells cap blocks p)*bw*T) :=by ring
    _ ≤ 7*(3213*factor*fund) :=Nat.mul_le_mul_left 7 paid
    _ = _ :=by ring

end
end Hierarchy.DescentTerminalVertexFields.MaskAllocation

end OAI
