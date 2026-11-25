import OAI.Hierarchy.DescentTerminalChipTapes

namespace OAI
/-! # Literal pin views and shared tables of the terminal emitter -/
namespace Hierarchy.DescentTerminalEmitter
open DescentTerminalChipRuntime DescentTerminalChipPins DescentTerminalScalarTransposes
open DescentTerminalBinReaddress DescentTerminalDenseWindow DescentTerminalDenseWindowRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {K W q p w : ℕ}
local notation "n" => K*W
local notation "d" => q*(W*p)
local notation "c" => DescentTerminalBinFormat.controlBits W q
local notation "routes" => DescentTerminalBinFormat.address W q

/-- Only the four fixed literal pin views and the static shared arithmetic
ROMs; every graph-dependent field is produced by the native prefix. -/
structure Boot (B : Banks) (m : Memory w) (z : DescentTerminalChipPins.Inputs K W q p→Bool) : Prop where
  pins : ∀which slice : Bool,∀i : Fin n,
    m ((if which then (if slice then B.ySlices else B.scalar.payload) else (if slice then B.joinedX else B.xWords)).base+i.val)=
      DescentTerminalChipPins.column z which slice i.val
  high : ∀u : Word d,m (B.highField.base+u.val)=(offsets w (radix q (W*p)) (radix q (W*p)))[u.val]
  menu : ∀v : Fin (Menus q (W*p)),m (B.menuStart.base+v.val)=
    (offsets w (Menus q (W*p)) (radix q (W*p)*radix q (W*p)))[v.val]
  lookup : ∀(v : Fin (Menus q (W*p))) (lo hi : Word d),m (B.denseROM.base+
    (v.val*(radix q (W*p)*radix q (W*p))+(lo.val*radix q (W*p)+hi.val)))=
      DescentTerminalDenseWindow.entry w q (W*p) v lo hi
  ptr : ∀a : Fin (2^c),m (B.pointer.base+a.val)=(DescentTerminalBinSliceCheap.pointers w c (sliceWidth W q p))[a.val]'a.isLt
  route : ∀(a : Tagged.Row c) (b : Word (sliceWidth W q p)),
    m (B.routeROM.base+(a.val*2^(sliceWidth W q p)+b.val))=DescentTerminalBinReaddress.entry w p routes a b

end
end Hierarchy.DescentTerminalEmitter

end OAI
