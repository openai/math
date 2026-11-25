import OAI.Hierarchy.DescentTerminalPlacedSocketMask
import OAI.Hierarchy.DescentTerminalNormalizedVenues

namespace OAI
/-! # Numeric occupancy of each raw terminal socket after the physical row pass -/
namespace Hierarchy.DescentSixParty.Reached
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentCompiler DescentTerminalGraphPositions
open DescentTerminalCompiledPrefix DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalVertexFields DescentSIMDLookup DescentTerminalEmitter.Compact
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
variable {G : PoweredGadget F} {price ε : ℝ} {S : AtomSchedule} {k age z degree wire hist p : ℕ}
    (live : Reached W G price ε S k age z degree wire hist) (order : Order W.graph (S.hostSize age) p)
    (same : order.home = live.home)
variable {q tags H N A verts B w : ℕ}
local notation "V" => (⟨q,tags,H,N,A,p,S.groupCount age⟩ : Home.Format)
variable (cfg : DescentTerminalCompiledPrefix.Shape) (I : Input) (R : MaskAllocation.Channels (2^k))
    (start header : ℕ) (short : verts*span q tags H N A p ≤ B) (lit : Literals I.sources)
local notation "cs" => meter V R start
local notation "ba" => afterMeter V cfg R start
local notation "abi" => layout cfg I ba (registers V cfg R start header)
local notation "area" => rowArena cfg I ba
local notation "after" => fun m : Memory w => Suffix.sockets cfg abi
    ((area).mount (input V cfg I R start header short lit m))
local notation "number" => S.groupCount age
local notation "hosts" => S.hostSize age
local notation "masks" => fun x h g => (if ∃ v : W.graph.Site,
  live.home v=h ∧ (live.placement.pos v).1=g ∧ live.placement.block v=x then 1 else 0 : Cell 1)

omit [Fintype P] in
/-- The incoming occupancy tape is the original physical census by group and block.
Only addresses below the next primitive writer are transported through its live prefix. -/
theorem sockets_occupation (census prim : Memory w)
    (old : Earlier cfg I ba (cs).layout w) (fits : last V cfg I R start < 2^w)
    (hostFit : hosts ≤ 2^w) (wide : number ≤ w) (rows : ∀ x,hosts ≤ (R.occupied x).size)
    (words : ∀ x (h : Fin hosts),census ((R.occupied x).base+h.val) =
      ((encode 1 number (masks x h)).val : Word w))
    (primStart : ℕ) (under : primStart ≤ start)
    (ends : ∀ x,(R.occupied x).base+(R.occupied x).size ≤ primStart)
    (kept : ∀ j < primStart, prim j = census j) (i : Fin hosts) (c : Fin (number*2^k)) :
    blankAt (measured (q:=q) (t:=tags) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=number)
      (cs).layout (after prim) i) c ≠ 0 ↔ ∃ u,live.chart order same i u=c := by
  apply measured_chart live order same R start census (after prim) hostFit wide rows words primStart ends
  intro x hx
  exact (AddressPlan.original_sockets V cfg I R start header short lit prim old fits
    (hx.trans_le under)).trans (kept x hx)

end
end Hierarchy.DescentSixParty.Reached

end OAI
