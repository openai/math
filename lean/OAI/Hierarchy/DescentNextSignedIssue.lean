import OAI.Hierarchy.DescentNextSignedRAM
import OAI.Hierarchy.DescentPackedFieldGather

namespace OAI
/-! # Compile actual eight short per-role columns into the next physical signed RAM -/
namespace Hierarchy.DescentNextSignedWindow.Native
open DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentPackedColony DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentPacking.PackedMatch.Local
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D cap b H G M w c : ℕ}
local notation "s" => DescentSignedCableCodec.width D cap

/-- All field inputs are the actual presence, direction, numeric successor
neighbor, core flag, signed first slot, parallel first slot, source first
slot and normalized-width count. The operand is composed inside the scan. -/
theorem run_fields (j:Fin (2*cap)) (join:Fin 8→Tables) (tables:Tables) (field:Fin c→Fin 8→Expr) (out:Bank) (m:Memory w)
    (rows:Fin H→Fin G→Fin c→Option (Record D cap)) (target:Fin H→Fin G→Option (Stage.Live D cap))
    (bounds:∀a,Gather.Bounds (d:=b) (M:=M) (w:=w) join (field a) out.base)
    (static:∀i,Static (join i) (Gather.setField (d:=b) i) M m)
    (actual:∀a i,Source (field a i) (fun h g=>(fields (rows h g a) i:Cell b)) M m)
    (fit:∀a,DescentPackedZip.Fits tables (Gather.assembly join (field a)) (.lit 0) (b*8) 0 M out.base w)
    (small:∀h g i t,fields (rows h g i) t<2^b)
    (rom:Static tables (fun x (_:Cell 0)=>table (D:=D) (b:=b) j x) M m)
    (empty:∀h g,target h g=none→∀i,(rows h g i).bind (fun r=>read r j)=none)
    (live:∀h g r,target h g=some r→∃i,(rows h g i).bind (fun u=>read u j)=some r ∧ ∀l,l≠i→(rows h g l).bind (fun u=>read u j)=none)
    (room:out.base+H*chunks G M<2^w):
    let op':=op tables (fun a=>Gather.assembly join (field a))
    let result:=image out.base (H*chunks G M) op' m
    (scan w out.base (H*chunks G M) op').Exec m result (4+H*chunks G M*(2*op'.work+4)) ∧
    DescentPackedColony.Reads out (fun h g=>DescentSignedCableCodec.encode (target h g)) M result ∧
    CheapCode (scan w out.base (H*chunks G M) op'):=by
  apply run j tables (fun a=>Gather.assembly join (field a)) out m rows target fit _ small rom empty live room
  intro a
  have proof:=Gather.collected join (field a) out.base (bounds a) m static
    (fun h g i=>(fields (rows h g a) i:Cell b)) (actual a) (List.finRange 8)
  simpa [Gather.assembly,word] using proof

end
end Hierarchy.DescentNextSignedWindow.Native

end OAI
