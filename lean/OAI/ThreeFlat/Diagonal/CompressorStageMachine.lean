import OAI.ThreeFlat.Diagonal.CompressorNativeGraph
import OAI.ThreeFlat.Diagonal.CompressorNativeRefresh
import OAI.ThreeFlat.Diagonal.CompressorNativeSweep

namespace OAI
/-! # Actual private RAMs for the two chronological graph-update scans

All six columns occupy one public consecutive output interval. The first
three are outgoing neighbor, mate port, and displacement, followed by the
same three quantities in incoming-slot order. Each descriptor only reads
the old graph, the public radices and the current output pointer.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Native
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.Compression RAM.DescriptorExpr
open Placement
open scoped Fin.NatCast
variable {w k : ℕ}

def sixColumns (start length : Term w k 1) (row : Fin 6 → Term w k 1 → Term w k 1) : Term w k 1 :=
  let o := terms w k 1
  let field := o.bin .div (o.bin .sub (.result 0) start) length
  let addr := fun i : Fin 6 => o.bin .add start (o.bin .mul length (o.lit i.val))
  (List.finRange 6).foldr (fun i tail => o.choose field (o.lit i.val) (row i (addr i)) tail)
    (o.lit 0)

def shrinkColumns (g : ArcColumns (Term w k 1)) (r : Radices (Term w k 1))
    (S : Graph.Stage) (lay : Bool) (start length mask : Term w k 1) : Term w k 1 :=
  sixColumns start length fun i atRow => Graph.updateRow g r S lay (decide (3 ≤ i.val))
    (![Graph.Field.neighbor,.matePort,.delta,.neighbor,.matePort,.delta] i) atRow mask

def refreshColumns {m a : ℕ} (E : SlotGraph (Fin m) a) (pad : ℕ)
    (old : Bool → Refresh.OldColumns (Term w k 1)) (start length : Term w k 1) : Term w k 1 :=
  sixColumns start length fun i =>
    let reverse := decide (3 ≤ i.val)
    Refresh.row E reverse pad (![Refresh.Field.neighbor,.matePort,.delta,.neighbor,.matePort,.delta] i)
      (old reverse)

/-- Concrete fixed-width program. The driver reads its interval endpoints
from public words 0 and 1; all remaining words are graph-layout parameters. -/
def stageMachine (desc : Term w (2+k) 1) (start stop : Word w) (pub : Fin k → Word w) :=
  machine desc start stop pub

theorem finish_stage (desc : Term w (2+k) 1) (lo hi state : Word w) (pub : Fin k → Word w)
    (m : Memory w) (length : ℕ) (fit : lo.val+length=hi.val) :
    let M := stageMachine desc lo hi pub
    ∃ out, out.pc = RAM.DescriptorScan.tailPc desc.labels (0 : Fin 1) ∧
      RAM.advance M.program (4+length*(desc.steps+3)) (M.program.start state) m =
        some (out,sweep (fun z mem => desc.eval M.publicData mem (fun _ => z)) length lo m) :=
  machine_run desc lo hi state pub m length fit

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
