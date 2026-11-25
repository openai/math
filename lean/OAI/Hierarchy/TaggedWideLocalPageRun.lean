import OAI.Hierarchy.TaggedWideMountedControlFields
import OAI.Hierarchy.TaggedWideDatedLayout
import OAI.Hierarchy.TaggedWideSitePublisher

namespace OAI
/-! # Dense site control publication after the sparse ballot tables -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM Calendar.WideCPU ProbeStage.CoreBoard.HistoryRoles
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing Classical
variable {W sites n D cap : ℕ}
  (table : Bank) (old new ballot C rom base : ℕ) (lowStart : ℕ := C-(D+D))
local notation "cols" => fieldCount D
local notation "geometry" => (⟨sites,1,cols⟩ : Shape)
local notation "fields" => fixed sites n D cap table old new ballot C lowStart
local notation "phase" => (geometry).sheet sites rom base fields
local notation "strideROM" => RoleROM.bank (rom+3*(geometry).count) sites

theorem fixed_run (m : Memory W) (one : 1<2^W) (fieldRoom : cols≤2^W)
    (addressRoom : base+(geometry).span sites<2^W)
    (directory : ∀i : Fin 3,RoleROM.Mounted (rom+i.val*(geometry).count)
      (SiteScatter.directory sites 1 cols i) m)
    (strides : ∀s : Fin sites,(strideROM).read m (s.val:Word W)=((s.val*cols:ℕ):Word W))
    (reads : (phase).value.Fits W (base+1)) (dest : (phase).address.Fits W (base+1)) :
    ∃out,((phase).code W).Exec m out (phase).ticks ∧
      (∀s : Fin sites,∀f : Field D,out (base+1+(SiteScatter.pos s (fieldNumber D f)).val)=
        ((fields).value 0 (fieldNumber D f)).eval m (s.val:Word W)) ∧
      (∀a,a<base ∨ base+(geometry).span sites≤a → out a=m a) := by
  let pair : Fin sites ↪ Fin sites × Fin 1 := ⟨fun s=>(s,0),fun _ _ eq=>congrArg Prod.fst eq⟩
  let site:=Function.Embedding.refl (Fin sites)
  let word:=fun s : Fin sites=>fun f : Fin cols=>((fields).value 0 f).eval m (s.val:Word W)
  have qty : (geometry).count≤2^W := by
    change base+(1+sites*cols+2*(geometry).count)<2^W at addressRoom
    omega
  have bound : base+1+sites*cols+(geometry).count+(geometry).count<2^W := by
    change base+(1+sites*cols+2*(geometry).count)<2^W at addressRoom
    omega
  have whole := SiteScatter.replay pair site word rom (base+1) (base+1+sites*cols) base strideROM
    (fields).selected (fields).site (fields).value m directory qty one.le fieldRoom
    (fun ⟨s,j⟩ => by
      have uid:j=0:=Subsingleton.elim ..;subst j
      constructor
      · exact fun _=>⟨s,rfl⟩
      · intro _
        change (1:Word W)≠0
        intro eq
        have bad := congrArg Fin.val eq
        change 1 % (2^W) = 0 at bad
        rw [Nat.mod_eq_of_lt one] at bad
        omega)
    (fun _=>rfl) (fun _ _=>rfl) strides reads dest le_rfl bound (by omega)
  obtain ⟨out,run,read,frame⟩:=whole
  refine ⟨out,run,?_,?_⟩
  · intro s f
    exact (read s (fieldNumber D f)).trans (SiteScatter.active site word s (fieldNumber D f))
  · intro a outside
    change a < base ∨ base + (1 + sites*cols + 2*(sites*(1*cols))) ≤ a at outside
    apply frame a <;> omega

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
