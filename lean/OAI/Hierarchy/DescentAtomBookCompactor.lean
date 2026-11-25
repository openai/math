import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentPackedActorMask
import OAI.Hierarchy.DescentPackedLocalAtoms
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Native compaction of packed actor fields and scalar count masks -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {D K cap nodes H G M w a n mBits : ℕ}

structure TablesAt where
  targets : Tables
  actors : Tables
  emitted : Tables

def masked (T : TablesAt) (want addr count : Expr) :=T.actors.read (T.targets.read want addr) count

def resultExpr (T : TablesAt) (G : Fin nodes→Tables) (field : Fin nodes→Expr) (want addr count : Expr) :=
  T.emitted.read (masked T want addr count) (Gather.assembly G field)

local notation "t" => DescentPackedActorMask.actors D cap
local notation "W" => DescentPackedActorMask.nodes D K cap

/-- A single rectangular scan tests old/party venues, reads old scalar
counts, and writes the compact atom book for all packed group lanes. -/
theorem run (T : TablesAt) (gates : Fin W→Tables) (src : Fin W→Expr) (want addr count : Expr) (out K' : ℕ) (mem : Memory w)
    (targets : DescentPackedZip.Fits T.targets want addr n (n*t) M out w)
    (actors : DescentPackedZip.Fits T.actors (T.targets.read want addr) count (1*t) (mBits*D) M out w)
    (fields : Gather.Bounds (w:=w) (d:=a) (M:=M) gates src out)
    (emit : DescentPackedZip.Fits T.emitted (masked T want addr count) (Gather.assembly gates src) (1*W) (a*W) M out w)
    (space : out+H*chunks G M<2^w)
    (fixedT : Static T.targets (DescentPackedActorMask.target n t) M mem)
    (fixedA : Static T.actors (DescentPackedActorMask.occupied D K cap mBits) M mem)
    (fixedF : ∀i,Static (gates i) (Gather.setField (d:=a) i) M mem)
    (fixedE : Static T.emitted (DescentPackedLocalAtoms.pack a W K') M mem)
    (wanted : Fin H→Fin G→Cell n) (venue : Fin H→Fin G→Fin t→Cell n)
    (num : Fin H→Fin G→Fin D→Cell mBits) (value : Fin H→Fin G→Fin W→Cell a)
    (query : Source want wanted M mem) (venues : Source addr (fun h g=>encode n t (venue h g)) M mem)
    (counts : Source count (fun h g=>encode mBits D (num h g)) M mem) (donors : ∀j,Source (src j) (fun h g=>value h g j) M mem) :
    let e:=resultExpr T gates src want addr count;let state:=image out (H*chunks G M) e mem
    let raster:=fun h g=>DescentPackedActorMask.occupied D K cap mBits (DescentPackedActorMask.target n t (wanted h g) (encode n t (venue h g))) (encode mBits D (num h g))
    (scan w out (H*chunks G M) e).Exec mem state (4+(H*chunks G M)*(2*e.work+4)) ∧
      (∀rowId : Row H G M,state (out+(row H G M rowId).val)=((data (fun h g=>DescentPackedLocalAtoms.pack a W K' (raster h g) (encode a W (value h g))) rowId).val:Word w)) ∧
      CheapCode (scan w out (H*chunks G M) e) := by
  let target:=fun h g=>DescentPackedActorMask.target n t (wanted h g) (encode n t (venue h g))
  have tv:=read_data T.targets want addr out targets _ (DescentPackedActorMask.target_zero ..) mem fixedT _ _ query venues
  have bits_:=read_data T.actors (T.targets.read want addr) count out actors _ (DescentPackedActorMask.occupied_zero ..) mem fixedA target _ tv counts
  have vf:Source (Gather.assembly gates src) (fun h g=>encode a W (value h g)) M mem:=by
    simpa only [Gather.assembly,List.mem_finRange,ite_true] using Gather.collected gates src out fields mem fixedF value donors (List.finRange W)
  have result:=read_data T.emitted (masked T want addr count) (Gather.assembly gates src) out emit _ (DescentPackedLocalAtoms.pack_zero ..) mem fixedE _ _ bits_ vf
  have bounded : (resultExpr T gates src want addr count).Fits w out := by simp [resultExpr,Tables.read,Expr.Fits,emit.left,emit.right,emit.shift,emit.apply]
  refine ⟨scan_exec _ _ _ _ bounded space,?_,@scan_cheap _ _ _ _⟩
  intro rowId;exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H G M rowId)).trans (result rowId)

end
end Hierarchy.DescentOrdinaryAtomFieldRAM

end OAI
