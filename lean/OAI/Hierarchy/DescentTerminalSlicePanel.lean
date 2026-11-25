import OAI.Hierarchy.DescentTerminalSliceRaw
import OAI.Hierarchy.DescentTerminalSliceDigits

namespace OAI
/-! # Issuing each of the six authentic printed fields in its little-endian node lane -/
namespace Hierarchy.DescentTerminalSliceRuns
open DescentKernelHistory DescentBundleHistory DescentSixParty
open DescentSIMDLookup DescentPrimitivePalette DescentTerminalCombinedRole
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {M N groups d:ℕ}
variable {F:Type} [Field F] (G:PoweredGadget F) {s Z:ℕ} (op:RotorSpec) (a k p R:ℕ)
    (cfg:RawWidths)
local notation "paletteSize" => colors G s Z op
local notation "dict" => DescentPrimitivePalette.codec (G:=G) (s:=s) (Z:=Z) op
local notation "width_" => width paletteSize a k p R
def writePanel (f:Fin 6) (x:Fin (Columns M)→Cell d) : Cell (width_ f*N*groups) :=
  collect (n:=paletteSize) (A:=a) (G:=k) (p:=p) (R:=R) (N:=N) (M:=groups)
    (fun (g:Fin groups) (u:Fin N)=>print (s:=s) (Z:=Z) G op a k p R (extract cfg x g u)) f

theorem panel_digit (f:Fin 6) (x:Fin (Columns M)→Cell d) (g:Fin groups) (u:Fin N) :
    (encode (width_ f) N).symm ((encode (width_ f*N) groups).symm (writePanel (s:=s) (Z:=Z) (N:=N) (groups:=groups) G op a k p R cfg f x) g) u=
      print (s:=s) (Z:=Z) G op a k p R (extract cfg x g u) f := by
  simp [writePanel,collect]

variable {T E:Type} {w:E→ℕ} {r:BitRecipe T E w} (hp:0<p) (sh:Shape p r) (v:r.Node)
    (label:Label G s Z op) (f:Fin 6) (x:Fin (Columns M)→Cell d) (g:Fin groups) (u:Fin N)
local notation "raw" => extract cfg x g u
local notation "xs" => sh.sliceFields v
local notation "words" => repeatFields (List.flatten xs)
include hp in
theorem authentic_digit
    (kind:(classify G p s label).correct xs) (token:(raw).token=((dict).store label).val+1)
    (live:(raw).live=(words).length) (fits:(words).length≤M)
    (spans:∀j:Fin (words).length,(raw).header (j.castLE fits)=words[j.val]) :
    (encode (width_ f) N).symm ((encode (width_ f*N) groups).symm (writePanel (s:=s) (Z:=Z) (N:=N) (groups:=groups) G op a k p R cfg f x) g) u=
      rawWords (n:=paletteSize) (p:=p) (R:=R) (birth (A:=a) (G:=k) dict label xs) f := by
  rw [panel_digit]
  exact congrFun (printed_arrays G op hp sh v label kind raw token live fits spans a k R) f

include hp in
theorem partial_digit (kind:(classify G p s label).correct xs) (token:(raw).token=((dict).store label).val+1)
    (live:(raw).live=(words).length) (fits:(words).length≤M)
    (spans:classify G p s label=.rotor→∀j:Fin (words).length,(raw).header (j.castLE fits)=words[j.val]) :
    (encode (width_ f) N).symm ((encode (width_ f*N) groups).symm (writePanel (s:=s) (Z:=Z) (N:=N) (groups:=groups) G op a k p R cfg f x) g) u=
      rawWords (n:=paletteSize) (p:=p) (R:=R) (birth (A:=a) (G:=k) dict label xs) f := by
  rw [panel_digit]
  exact congrFun (partial_arrays G op hp sh v label kind raw token live fits a k R spans) f

theorem empty_digit (f:Fin 6) (x:Fin (Columns M)→Cell d) (g:Fin groups) (u:Fin N)
    (vacant:(extract cfg x g u).token=0) :
    (encode (width_ f) N).symm ((encode (width_ f*N) groups).symm (writePanel (s:=s) (Z:=Z) (N:=N) (groups:=groups) G op a k p R cfg f x) g) u=0 := by
  rw [panel_digit]
  simp [print,recover,vacant]

end
end Hierarchy.DescentTerminalSliceRuns

end OAI
