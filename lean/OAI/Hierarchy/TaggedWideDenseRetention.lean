import OAI.Hierarchy.TaggedWidePageSweep
import OAI.Hierarchy.ProbeSparseParticipantROM

namespace OAI
/-! # Persistent output of a dated local control computation -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
variable {W n c : ℕ} (rom start : ℕ)
variable (x : Fields (⟨n,1,c⟩ : Shape)) (prior : Memory W→Prop)

def denseResult : PageResult W ((⟨n,1,c⟩ : Shape).sheet n rom start x) where
  holds out:=∃before,prior before ∧ ∀s : Fin n,∀f : Fin c,
    out (start+1+(SiteScatter.pos s f).val)=(x.value 0 f).eval before (s.val:Word W)
  localize:=by
    rintro early later frame ⟨before,prev,shown⟩
    refine ⟨before,prev,fun s f=>?_⟩
    rw [←shown s f]
    apply frame
    · simp [Shape.sheet,Scatter.floor]; omega
    · have h:=(SiteScatter.pos s f).isLt
      change start+1+(SiteScatter.pos s f).val<start+1+n*c+2*(⟨n,1,c⟩ : Shape).count
      omega

/-- The scatter is dense specifically because there is exactly one
candidate at its own physical site, even when its new width is zero. -/
theorem dense_run (m : Memory W) (origin : prior m) (pub : PublicSheet (⟨n,1,c⟩ : Shape) n rom start W x m)
    (one : 1<2^W) (sel : ∀i,x.selected i=.lit 1) (site : ∀i,x.site i=.row) :
    let z:=(⟨n,1,c⟩ : Shape).sheet n rom start x
    ∃out,(z.code W).Exec m out z.ticks ∧ (denseResult (n:=n) (c:=c) rom start x prior).holds out ∧
      ∀a,a<z.floor → out a=m a := by
  intro z
  let pair : Fin n↪Fin n×Fin 1:=⟨fun i=>(i,0),fun _ _ h=>congrArg Prod.fst h⟩
  let nm:=Function.Embedding.refl (Fin n)
  let word:=fun s : Fin n=>fun f : Fin c=>(x.value 0 f).eval m (s.val:Word W)
  obtain ⟨out,run,reads,frame⟩:=SiteScatter.replay pair nm word rom (start+1) (start+1+n*c) start
    (RoleROM.bank (rom+3*(⟨n,1,c⟩ : Shape).count) n) x.selected x.site x.value m pub.mounted pub.size one.le pub.columns
    (fun ⟨s,i⟩=>by
      have e:i=0:=Subsingleton.elim ..;subst i
      exact ⟨fun _=>⟨s,rfl⟩,fun _=>by
        rw [sel];change (1:Word W)≠0
        intro bad
        have raw := congrArg Fin.val bad
        change 1 % (2^W) = 0 at raw
        rw [Nat.mod_eq_of_lt one] at raw
        omega⟩)
    (fun s=>by rw [site];rfl) (fun _ _=>rfl) pub.stride pub.value pub.address le_rfl pub.space (by omega)
  refine ⟨out,run,⟨m,origin,fun s f=>(reads s f).trans (SiteScatter.active nm word s f)⟩,?_⟩
  intro a ha
  apply frame a <;> simp only [z,Shape.sheet,Scatter.floor,Nat.add_sub_cancel] at ha <;> omega

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
