import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentPackedLookupHeader

namespace OAI
/-! # Applying a finite local law to the reached packed rows of actual hosts -/

namespace Hierarchy.DescentPackedLocalLookup
open DescentSIMDLookup ProtocolRAM DescentPackedFallbackTree.Image Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
theorem compile {a b hosts groups M w : ℕ} (g : DescentSIMDLookup.Banks) (out : ℕ)
    (fn : Cell a→Cell b) (x : Fin hosts→Fin groups→Cell a) (pos : 0<M) (safe : Fits g a b M hosts groups w out)
    (m : Memory w) (res : resident fn g hosts groups M m)
    (source : ∀q : Row hosts groups M,m (g.source.base+(row hosts groups M q).val)=(data x q).val) :
    let dst:=imageBank hosts groups M out g m
    (program g out hosts groups M w).Exec m dst (4+44*(hosts*chunks groups M)) ∧
    (∀v i,digit b (lane i pos).val (dst (out+(row hosts groups M (position v i pos)).val)).val=(fn (x v i)).val) ∧
    (∀a<out,dst a=m a) ∧ ∀a,out+hosts*chunks groups M≤a→dst a=m a := by
  let dst:=imageBank hosts groups M out g m
  have words : PinFrame (M:=M) g fn x m := by
    refine ⟨?_,source⟩
    intro key bit
    cases key with
    | inl t=>exact congrArg (fun n=>wordBits w n bit) (res.1 t)
    | inr t=>exact congrArg (fun n=>wordBits w n bit) (res.2 t)
  have valid : (DescentSIMDLookup.lookup g).Fits w out:=⟨⟨safe.dictionary,safe.source,trivial⟩,safe.mask,trivial⟩
  have read (q : Row hosts groups M) : dst (out+(row hosts groups M q).val)=(masked fn x q:Word w):=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans (lookup_read g out safe fn x m words q)
  refine ⟨?_,fun v i=>physical_read g out safe fn x dst read v i pos,fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ha),
    fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr ha)⟩
  change (scan w out (hosts*chunks groups M) (DescentSIMDLookup.lookup g)).Exec m
    (image out (hosts*chunks groups M) (DescentSIMDLookup.lookup g) m) (4+44*(hosts*chunks groups M))
  rw [Nat.mul_comm 44]
  exact scan_exec out (hosts*chunks groups M) _ m valid safe.output

end
end Hierarchy.DescentPackedLocalLookup

end OAI
