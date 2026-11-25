import OAI.Hierarchy.DescentResetCompactGeometry
import OAI.Hierarchy.DescentResetHaloBroadcast

namespace OAI
/-! # Scalar self-halo pull and its packed broadcast at compact new hosts -/
namespace Hierarchy.DescentResetCompactGeometry
open DescentPackedZip DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M b w : ℕ}
def selfExpr (total owner ranks : Bank) : Expr:=
  .branch .lt .row (.lookup total (.lit 0)) (.lookup ranks (.lookup owner .row)) (.lit 0)

theorem pull_self (total owner ranks : Bank) (out : ℕ) (m : Memory w) (N S : ℕ) (source : Fin N→Fin S)
    (value : Fin S→Cell b) (cnt : m total.base=(N:Word w)) (own : ∀i,m (owner.base+i.val)=((source i).val:Word w))
    (inputs : ∀i,m (ranks.base+i.val)=((value i).val:Word w))
    (ht : total.Fits w out) (ho : owner.Fits w out) (hr : ranks.Fits w out)
    (extent : N≤owner.size) (roots : S≤ranks.size) (capacity : N≤H) (room : out+H<2^w) :
    let e:=selfExpr total owner ranks
    let dst:=image out H e m
    (scan w out H e).Exec m dst (4+H*(2*e.work+4)) ∧
      (∀h:Fin H,dst (out+h.val)=((if v : h.val<N then (value (source ⟨h.val,v⟩)).val else 0):Word w)) ∧
      (∀a,a<out ∨ out+H≤a→dst a=m a) ∧ CheapCode (scan w out H e):=by
  intro e dst
  have safe : e.Fits w out:=⟨trivial,⟨ht,trivial⟩,⟨hr,ho,trivial⟩,trivial⟩
  refine ⟨scan_exec _ _ _ _ safe room,?_,ProtocolRAMGeneratedWrite.frame_image _ _ _ m,@scan_cheap _ _ _ _⟩
  intro h
  apply (ProtocolRAMGeneratedWrite.read_image out H e m h).trans
  have count : total.read m ((0 : ℕ) : Word w) = (N : Word w) := by
    rw [bank_read total m (i:=0) ht.1 ht, Nat.add_zero, cnt]
  have cal : H < 2^w := (Nat.le_add_left H out).trans_lt room
  have cmp : DescriptorExpr.Comparison.lt.test (h.val : Word w) (N : Word w) = decide (h.val < N) := by
    simp only [DescriptorExpr.Comparison.test, Fin.lt_def, Fin.val_cast_of_lt (h.isLt.trans cal),
      Fin.val_cast_of_lt (capacity.trans_lt cal)]
  simp only [e, selfExpr, Expr.eval, count, cmp]
  by_cases hi : h.val < N
  · let i : Fin N := ⟨h.val,hi⟩
    have ownerRead : owner.read m (h.val : Word w) = ((source i).val : Word w) :=
      (bank_read owner m (hi.trans_le extent) ho).trans (own i)
    have rankRead : ranks.read m ((source i).val : Word w) = ((value (source i)).val : Word w) :=
      (bank_read ranks m ((source i).isLt.trans_le roots) hr).trans (inputs (source i))
    simp [hi, ownerRead, rankRead, i]
  · simp [hi]

/-- A single broadcast dictionary serves shape and self: each arranged source word is
short and both public outputs are read by immutable expressions on the same post-state. -/
theorem broadcast (banks : Fin 2→Bank) (src : Fin 2→Fin H→Cell b) (base : ℕ) (m : Memory w)
    (fit : ∀s,(banks s).Fits w base) (extent : ∀s,H≤(banks s).size)
    (stored : ∀s i,m ((banks s).base+i.val)=((src s i).val:Word w))
    (room : DescentResetHaloBroadcast.endAt base H G M b<2^w) :
    let n:=DescentResetHaloBroadcast.count H G M b
    let f:=DescentResetHaloBroadcast.literal b G M (id : Fin H→Fin H)
    let dst:=DescentStaticWordColumn.image base f m n
    (DescentStaticWordColumn.program w base f n).Exec m dst (4+10*n) ∧
      (∀s,Source (DescentResetHaloBroadcast.expr (banks s) base H G M b) (fun h (_ : Fin G)=>src s h) M dst) ∧
      (∀a,a<base ∨ base+n≤a→dst a=m a) ∧ CheapCode (DescentStaticWordColumn.program w base f n):=by
  intro n f dst
  have both (s : Fin 2):=DescentResetHaloBroadcast.run (banks s) base (id : Fin H→Fin H) (src s) m
    (fit s) (extent s) (stored s) room
  exact ⟨(both 0).1,fun s=>(both s).2.1,(both 0).2.2.1,@DescentStaticWordColumn.cheap _ _ _ _⟩

end
end Hierarchy.DescentResetCompactGeometry

end OAI
