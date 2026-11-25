import OAI.Hierarchy.DescentPackedFlowBatch
import OAI.Hierarchy.DescentGLPackedReset
import OAI.Hierarchy.DescentResetGLPanels

namespace OAI
/-! # Executing the selected basis once over all source fields -/
namespace Hierarchy.DescentGLPacked.BankImage
open DescentGLPacked DescentGL DescentColonies DescentGLNielsen DescentSIMDLookup
open DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D H h l c b w M : ℕ}

def slice (base cells width : ℕ) (i : Fin D) := base+i.val*cells*width

def stack (X : Fin D→Fin H→Block (h+l)→Cell b) (v : Fin (D*H)) :=
  X (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2

private theorem slice_row {G : ℕ} (d : Fin D) (r : DescentSIMDLookup.Row H G M) :
   (DescentSIMDLookup.row (D*H) G M (finProdFinEquiv (d,r.1),r.2)).val=
     d.val*H*chunks G M+(DescentSIMDLookup.row H G M r).val := by
  change r.2.val+chunks G M*(r.1.val+H*d.val)=d.val*H*chunks G M+(r.2.val+chunks G M*r.1.val)
  ring

theorem slice_dense (base : ℕ) (X : Fin D→Fin H→Block (h+l)→Cell b) (mem : Memory w)
    (issued : Dense (h:=h) (l:=l) base (stack X) mem) (d : Fin D) :
    Dense (h:=h) (l:=l) (slice base H (2^h) d) (X d) mem := by
  intro p
  have word:=issued (finProdFinEquiv (d,p.1),p.2)
  have stride := congrArg (fun cells => d.val * H * cells) (chunk_count h l)
  rw [slice_row d p, stride] at word
  simpa only [slice,Nat.add_assoc,data,stack,Equiv.symm_apply_apply] using word

/-- Copy the genuine old packed fields into the public channel order. Each row
reads the preceding tape and all rows share the same original measured basis. -/
theorem gather_channels (base : ℕ) (field : ℕ→Expr) (X : Fin D→Fin H→Block (h+l)→Cell b)
    (mem : Memory w) (fits : ∀j<D,(field j).Fits w base) (room : base+D*(H*2^h)<2^w)
    (input : ∀d,DescentPackedZip.Source (field d.val) (X d) (2^l) mem) :
    let n:=H*2^h
    let ps:=DescentPackedFlowBatch.passes base n n field 0 D
    (program w ps).Exec mem (result ps mem) (clock ps) ∧
    Dense (h:=h) (l:=l) base (stack X) (result ps mem) ∧ ∀a<base,result ps mem a=mem a := by
  obtain ⟨run,reads,low⟩:=DescentPackedFlowBatch.execute base (H*2^h) (H*2^h) D field mem fits room le_rfl
  refine ⟨run,?_,low⟩
  rintro ⟨combined,y⟩
  obtain ⟨⟨d,v⟩,rfl⟩:=finProdFinEquiv.surjective combined
  let p : Row H (2^(h+l)) (2^l):=(v,y)
  let i : Fin (H*2^h):=Fin.cast (congrArg (H*·) (chunk_count h l)) (row H _ _ p)
  have hword:=(reads d i).trans (input d p)
  have stride := congrArg (fun cells => d.val * H * cells) (chunk_count h l)
  rw [slice_row d p, stride]
  simpa only [i,Fin.val_cast,Nat.add_assoc,Nat.mul_assoc,stack,data,Equiv.symm_apply_apply] using hword

theorem all_fields {N : ℕ} (C : Chart) (sizes : Size C (D*H) h l b w)
    (T : DescentGLControlCode.Tables) (name : DescentGL.Layout (h+l)↪Fin N) (key : Expr)
    (L : DescentGL.Layout (h+l)) (X : Fin D→Fin H→Block (h+l)→Cell b) (mem : Memory w)
    (ks : DescentGLControlCode.fits T key w C.flags)
    (off : DescentGLControlCode.Count (h+l)≤T.offsets.size)
    (area : DescentGLControlCode.Count (h+l)*N≤T.switches.size)
    (stat : DescentGLControlCode.installed T name mem)
    (measured : ∀i : Fin (DescentGLControlCode.Count (h+l)),key.eval mem (i.val:Word w)=((name L).val:Word w))
    (source : Dense C.input.base (stack X) mem) (protectedInput : C.input.base+C.input.size≤C.flags)
    (short : c≤h+l) (pitch : M*2^(h+l-c)=2^l) (pos : 0<M) :
    let n:=(schedule (h+l)).length
    let original:=C.install (D*H) h l b mem
    let filled:=ProtocolRAM.image C.flags n (T.expr key) original
    let ps:=steps (C.chosen (h+l)) (D*H) (2^h) 0 n
    let machine:=(scan w C.flags n (T.expr key)).seq (program w ps)
    let dst:=result ps filled
    machine.Exec original dst ((4+n*(2*(T.expr key).work+4))+clock ps) ∧ CheapCode machine ∧
    ∀(d : Fin D) (p : Row H (2^c) M),
       dst (slice (((C.chosen (h+l)).bank n).base) H (2^h) d+(row H (2^c) M p).val)=
         ((data (fun v hi=>encode b (2^(h+l-c)) (fun x=>X d v ((rearrange L).symm
           (DescentIssuedFallbackPanel.join short hi x)))) p).val:Word w) := by
  obtain ⟨run,cheap,reads⟩:=reset C sizes T name key L (stack X) mem ks off area stat measured source protectedInput
  refine ⟨run,cheap,?_⟩
  intro d p
  apply DescentPlainTerminal.Suffix.grouped_remix short pitch pos _ (X d) L _ _ p
  exact slice_dense _ (fun d v z=>X d v ((rearrange L).symm z)) _ reads d

end
end Hierarchy.DescentGLPacked.BankImage

end OAI
