import OAI.Hierarchy.DescentMarkedNeighborToken
import OAI.Hierarchy.DescentPackedMaskedData
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentSignedCableCodec
import OAI.Hierarchy.DescentPackedMatchedGeometry

namespace OAI
/-! # Emitting the matcher’s marked-edge neighbor input from its signed predecessor -/
namespace Hierarchy.DescentPackedMatchSenderPins
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentSharedCableNames
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {D cap d : ℕ}

/-- Holds on each physical host/group instruction word used by the native
matching gather, including the true zero sentinel in unused final lanes. -/
theorem publish {H g M w : ℕ} (L : Banks) (out : ℕ) (fit : Fits L (DescentSignedCableCodec.width D cap) d M H g w out)
    (rows : Fin H→Fin g→Option (DescentSharedCableNames.Stage.Live D cap)) (m : Memory w)
    (pins : PinFrame (M:=M) L (table D cap d) (fun h j=>DescentSignedCableCodec.encode (rows h j)) m) (positive : 0<M) :
    let result:=image out (H*chunks g M) (DescentSIMDLookup.lookup L) m
    (DescentSIMDLookup.program L out H g M w).Exec m result (4+H*chunks g M*44) ∧
      (∀h j,digit d (lane j positive).val (result (out+(row H g M (position h j positive)).val)).val=(Stage.marked d (rows h j)).val) ∧
      (∀p : Row H g M,result (out+(row H g M p).val)=((masked (table D cap d) (fun h j=>DescentSignedCableCodec.encode (rows h j)) p : ℕ):Word w)) ∧
      CheapCode (DescentSIMDLookup.program L out H g M w) :=by
  intro result
  let x:=fun h j=>DescentSignedCableCodec.encode (rows h j)
  have ft : (DescentSIMDLookup.lookup L).Fits w out:=by simp [DescentSIMDLookup.lookup,Expr.Fits,fit.source,fit.mask,fit.dictionary]
  have read (p : Row H g M) : result (out+(row H g M p).val)=((masked (table D cap d) x p:ℕ):Word w):=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H g M p)).trans (lookup_read L out fit (table D cap d) x m pins p)
  refine ⟨scan_exec _ _ _ _ ft fit.output,?_,read,(spec L out fit (table D cap d) x).2⟩
  intro h j;exact (physical_read L out fit (table D cap d) x result read h j positive).trans (congrArg Fin.val (table_at (rows h j)))

/-- Exact `Gather.real_fields` premise for each published field bank. -/
theorem mounted {H g M w : ℕ} (L : Banks) (B : Bank) (fit : Fits L (DescentSignedCableCodec.width D cap) d M H g w B.base)
    (rows : Fin H→Fin g→Option (DescentSharedCableNames.Stage.Live D cap)) (m : Memory w)
    (pins : PinFrame (M:=M) L (table D cap d) (fun h j=>DescentSignedCableCodec.encode (rows h j)) m) (positive : 0<M) :
    let result:=image B.base (H*chunks g M) (DescentSIMDLookup.lookup L) m
    (DescentSIMDLookup.program L B.base H g M w).Exec m result (4+H*chunks g M*44) ∧
      DescentPackedColony.Reads B (fun h j=>Stage.marked d (rows h j)) M result ∧
      CheapCode (DescentSIMDLookup.program L B.base H g M w) :=by
  obtain ⟨ran,_,words,cheap⟩:=publish L B.base fit rows m pins positive
  refine ⟨ran,fun p=>?_,cheap⟩
  simpa only [masked_eq_data,table_at] using words p

end
end Hierarchy.DescentPackedMatchSenderPins

end OAI
