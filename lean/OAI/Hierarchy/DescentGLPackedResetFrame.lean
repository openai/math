import OAI.Hierarchy.DescentGLPackedReset
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Incoming and outgoing memory frames of the measured change of basis -/
namespace Hierarchy.DescentGLPacked.BankImage
open DescentGLPacked DescentGL DescentColonies DescentGLNielsen DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H h l b w : ℕ}

private theorem steps_frame (C : Chart) (H P d x : ℕ) (m : Memory w) (small : H*P≤C.page)
    (start n : ℕ) (frame : x<C.heap d ∨ C.heap d+(start+n)*C.page≤x) :
    result (steps (C.chosen d) H P start n) m x=m x := by
  induction n generalizing start m with
  | zero=>rfl
  | succ n ih=>
    let p:=single (C.chosen d) H P start
    have tail : x<C.heap d ∨ C.heap d+(start+1+n)*C.page≤x := by
      rwa [show start+1+n=start+(n+1) by omega]
    apply (ih (p.apply m) (start+1) tail).trans
    apply ProtocolRAMGeneratedWrite.frame_image
    change x<C.heap d+start*C.page ∨ C.heap d+start*C.page+H*P≤x
    rcases frame with lo|hi
    · exact Or.inl (lo.trans_le (Nat.le_add_right ..))
    · right
      have larger:=Nat.mul_le_mul_right C.page (show start+1≤ start+(n+1) by omega)
      rw [Nat.succ_mul] at larger
      omega

theorem reset_frames (C : Chart) (s : Size C H h l b w) (e : Expr) (m : Memory w) (a : ℕ)
    (frame : a<C.flags ∨ C.heap (h+l)+(schedule (h+l)).length*C.page≤a) :
    let n:=(schedule (h+l)).length
    let filled:=image C.flags n e m
    result (steps (C.chosen (h+l)) H (2^h) 0 n) filled a=m a := by
  let n:=(schedule (h+l)).length
  have offset:C.start≤C.heap (h+l):=Nat.le_add_right ..
  have lower:=s.controls
  have ga : a<C.heap (h+l) ∨ C.heap (h+l)+(0+n)*C.page≤a := by
    rcases frame with before|after
    · left;omega
    · exact Or.inr (by simpa only [Nat.zero_add] using after)
  apply (steps_frame C H (2^h) _ _ _ s.rows 0 n ga).trans
  apply ProtocolRAMGeneratedWrite.frame_image
  rcases frame with lo|hi
  · exact .inl lo
  · right;omega

theorem reset_resident {N : ℕ} (C : Chart) (sizes : Size C H h l b w)
    (T : DescentGLControlCode.Tables) (name : DescentGL.Layout (h+l) ↪ Fin N) (key : Expr)
    (L : DescentGL.Layout (h+l)) (X : Fin H→Block (h+l)→Cell b) (m : Memory w)
    (ks : DescentGLControlCode.fits T key w C.flags)
    (off : DescentGLControlCode.Count (h+l)≤T.offsets.size)
    (area : DescentGLControlCode.Count (h+l)*N≤T.switches.size)
    (stat : DescentGLControlCode.installed T name m)
    (measured : ∀i : Fin (DescentGLControlCode.Count (h+l)),key.eval m (i.val:Word w)=((name L).val:Word w))
    (source : Dense C.input.base X m) (protectedInput : C.input.base+C.input.size≤C.flags)
    (resident : C.install H h l b m=m) :
    let n:=(schedule (h+l)).length
    let filled:=image C.flags n (T.expr key) m
    let ps:=steps (C.chosen (h+l)) H (2^h) 0 n
    let machine:=(scan w C.flags n (T.expr key)).seq (program w ps)
    let out:=result ps filled
    machine.Exec m out ((4+n*(2*(T.expr key).work+4))+clock ps) ∧ CheapCode machine ∧
    Dense (((C.chosen (h+l)).bank n).base) (fun v z=>X v ((rearrange L).symm z)) out ∧
    ∀a,a<C.flags ∨ C.heap (h+l)+n*C.page≤a→ out a=m a := by
  obtain ⟨run,cheap,reads⟩:=reset C sizes T name key L X m ks off area stat measured source protectedInput
  rw [resident] at run reads
  exact ⟨run,cheap,reads,reset_frames C sizes _ m⟩

end
end Hierarchy.DescentGLPacked.BankImage

end OAI
