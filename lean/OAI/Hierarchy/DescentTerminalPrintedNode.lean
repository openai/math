import OAI.Hierarchy.DescentTerminalSliceExecution
import OAI.Hierarchy.DescentTerminalSlicePanel
import OAI.Hierarchy.DescentTerminalRoleTableMount
import OAI.Hierarchy.DescentTerminalRoleNumerals

namespace OAI
/-! Reading the six native role fields at one acquired chronological node. -/
namespace Hierarchy.DescentTerminalSliceRuns
open DescentSixParty DescentKernelHistory DescentBundleHistory DescentPrimitivePalette
open DescentSIMDLookup DescentTerminalCombinedRole DescentTerminalPointerDigits
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] (G : PoweredGadget F) {s Z : ℕ} (op : RotorSpec) (a k p R : ℕ)
variable {N groups blocks hosts M d bw : ℕ} (start advice : ℕ) (cfg : RawWidths)
    (chart : Fin (Columns M) → Fin blocks → Gather.Address) (original acquired : Memory bw)
    (block : Fin blocks) (shop : Fin hosts) (group : Fin groups) (slot : Fin N)
local notation "colors_" => colors G s Z op
local notation "paletteCodec" => DescentPrimitivePalette.codec (G:=G) (s:=s) (Z:=Z) op
local notation "widths" => fun f : Fin 6 => width colors_ a k p R f * N * groups
local notation "L" => Columns M
local notation "rows" => blocks * hosts
local notation "rawBank" => fun f : Fin 6 => DescentTerminalSliceShelf.field start L d rows (Fin.val f)
local notation "shelf" => DescentTerminalRoleTables.role widths rawBank advice
local notation "write_" => writePanel (d:=d) (M:=M) (s:=s) (Z:=Z) (N:=N) (groups:=groups) G op a k p R cfg
local notation "before_" => DescentTerminalSliceShelf.memory start chart write_ hosts original
local notation "floor_" => DescentTerminalSliceShelf.fence start L d rows
local notation "row_" => finProdFinEquiv (block,shop)
local notation "inputs" => DescentTerminalSliceShelf.seen (d:=d) chart original block shop
local notation "raw_" => extract cfg inputs group slot
local notation "view_" => observed (n:=colors_) (A:=a) (G:=k) (p:=p) (R:=R)
  (N:=N) (M:=groups) shelf acquired (Fin.val row_ : Computability.VPVNP.BurstRAM.Word bw)

variable {T E : Type} {w : E → ℕ} {r : BitRecipe T E w}

/-- The six words read at this block, host, group and node describe the label and
its operand slices. The rotor case uses its acquired affine span words. -/
theorem printed_at_node (positive : 0 < p) (sh : Shape p r) (u : r.Node) (label : Label G s Z op)
    (kind : (classify G p s label).correct (sh.sliceFields u))
    (valid : DescentBundleTagKeys.Fits paletteCodec a k p R (label,sh.sliceFields u))
    (ok : ∀ j x, (chart j x).Fits start hosts bw) (off : 2^d < 2^bw) (room_ : floor_ < 2^bw)
    (fitsWord : ∀ f, widths f ≤ bw) (kept : ∀ j < floor_, acquired j = before_ j)
    (token : (raw_).token = ((paletteCodec).store label).val + 1)
    (live : (raw_).live = (repeatFields (sh.sliceFields u).flatten).length)
    (fits : (repeatFields (sh.sliceFields u).flatten).length ≤ M)
    (spans : classify G p s label = .rotor → ∀ j : Fin (repeatFields (sh.sliceFields u).flatten).length,
      (raw_).header (j.castLE fits) = (repeatFields (sh.sliceFields u).flatten)[j.val]) :
    Printed paletteCodec (fields (node view_ group slot)) label (sh.sliceFields u) := by
  have issued := (DescentTerminalSliceShelf.native (H:=hosts) start chart write_ original ok off room_).2.2.2
  have inPage (f : Fin 6) : (row_).val<(rawBank f).size :=
    (row_).isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) (blocks * hosts))
  have inFence (f : Fin 6) : (rawBank f).base+(row_).val<floor_ := by
    calc
      _ < (rawBank f).base+(rawBank f).size := Nat.add_lt_add_left (inPage f) _
      _ = DescentTerminalSliceShelf.stage start L d rows (f.val+1) :=
        DescentTerminalSliceShelf.output_end (base:=start) («L»:=L) (d:=d) (blocks:=blocks) (H:=hosts) f.val
      _ ≤ floor_ := DescentTerminalSliceShelf.monotone start L d rows f.isLt
  have rowFits : (row_).val<2^bw :=
    (Nat.le_add_left _ (rawBank 0).base).trans_lt ((inFence 0).trans room_)
  have payload (f : Fin 6) : (view_) f=write_ f inputs := by
    have pageRead : ((shelf).input f).read acquired ((row_).val:Computability.VPVNP.BurstRAM.Word bw) =
        ((write_ f inputs).val:Computability.VPVNP.BurstRAM.Word bw) := by
      change acquired ((rawBank f).base+(((row_).val:Computability.VPVNP.BurstRAM.Word bw).val%(rawBank f).size))=_
      rw [Fin.val_cast_of_lt rowFits,Nat.mod_eq_of_lt (inPage f),kept _ (inFence f)]
      exact issued f block shop
    have wordFits : (write_ f inputs).val<2^bw :=
      (write_ f inputs).isLt.trans_le (Nat.pow_le_pow_right (by decide) (fitsWord f))
    change ((((shelf).input f).read acquired ((row_).val:Computability.VPVNP.BurstRAM.Word bw)).val:Cell (widths f))=_
    rw [pageRead,Fin.val_cast_of_lt wordFits]
    exact Fin.cast_val_eq_self _
  have nodeWords : node view_ group slot = rawWords (n:=colors_) (p:=p) (R:=R)
      (birth (A:=a) (G:=k) paletteCodec label (sh.sliceFields u)) := by
    funext f
    unfold node
    rw [payload f]
    exact partial_digit G op a k p R cfg positive sh u label
      f inputs group slot kind
      token live fits spans
  rw [nodeWords]
  exact birth_printed _ _ _ valid

end
end Hierarchy.DescentTerminalSliceRuns

end OAI
