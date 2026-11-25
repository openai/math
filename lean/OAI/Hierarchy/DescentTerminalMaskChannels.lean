import OAI.Hierarchy.DescentTerminalScanReads
import OAI.Hierarchy.DescentTerminalWholeRows
import OAI.Hierarchy.DescentTerminalMaskedRAM

namespace OAI
/-! # Original emitted SIMD words and their group digits at the masked terminal shelf -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentSIMDLookup ThreeFlat.Routing
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical Fin.CommRing
noncomputable section
variable {q t H N A w groups blocks shops wb a : ℕ}
local notation "sized" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)
local notation "dataAt" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups)

theorem whole_digit (v : Fin shops→Fin groups→Word a) (pos : 0<groups) (i : Fin shops) (g : Fin groups) :
    digit a g.val (data v (i,onlyBatch pos)).val=(v i g).val := by
  change digit a g.val (encode a groups _).val=_
  rw [digit_encode]
  simp [onlyBatch]

private theorem measured_payload (machine : MaskedShelf blocks) (m : Memory wb) (i : Fin shops)
    (c : Fin (channels blocks)) (payload : Word a)
    (width : channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) c=a)
    (fit : a≤wb) (read : (machine.channel c).read m (i.val:Word wb)=(payload.val:Word wb)) :
    (dataAt machine m i c).val=payload.val := by
  change ((machine.channel c).read m (i.val:Word wb)).val %
    2^(channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) c)=payload.val
  rw [width,read,Fin.val_cast_of_lt (payload.isLt.trans_le (Nat.pow_le_pow_right (by decide) fit)),
    Nat.mod_eq_of_lt payload.isLt]

/-- Real earlier data writes need only store their own finite SIMD payload. The terminal
reader can use those physical bank addresses directly, including on the final site. -/
theorem from_cell (machine : MaskedShelf blocks) (m : Memory wb) (pos : 0<groups) (b : Fin blocks)
    (f : Fin 8) (v : Fin shops→Fin groups→Word (sized f)) (fit : sized f*groups≤wb)
    (read : ∀i, (machine.channel (finProdFinEquiv (b,f.succ))).read m (i.val:Word wb)=((data v (i,onlyBatch pos)).val:Word wb))
    (i : Fin shops) (g : Fin groups) : cellAt (dataAt machine m i) (finProdFinEquiv (g,b)) f=v i g := by
  apply Fin.ext
  rw [cell_digit,measured_payload (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups)
    machine m i (finProdFinEquiv (b,f.succ)) (data v (i,onlyBatch pos))
    (by simp [channelSize,primitiveSize]) fit (read i)]
  exact whole_digit v pos i g

theorem from_mask (machine : MaskedShelf blocks) (m : Memory wb) (pos : 0<groups) (b : Fin blocks)
    (v : Fin shops→Fin groups→Word 1) (fit : groups≤wb)
    (read : ∀i,(machine.channel (finProdFinEquiv (b,(0:Fin 9)))).read m (i.val:Word wb)=((data v (i,onlyBatch pos)).val:Word wb))
    (i : Fin shops) (g : Fin groups) : blankAt (dataAt machine m i) (finProdFinEquiv (g,b))=v i g := by
  apply Fin.ext
  rw [presence_digit,measured_payload (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups)
    machine m i (finProdFinEquiv (b,(0:Fin 9))) (data v (i,onlyBatch pos))
    (by simp [channelSize,primitiveSize]) (by simpa only [Nat.one_mul] using fit) (read i)]
  exact whole_digit v pos i g

end
end Hierarchy.DescentTerminalVertexFields

end OAI
