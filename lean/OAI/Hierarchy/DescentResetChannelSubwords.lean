import OAI.Hierarchy.DescentSubwordReturn
import OAI.Hierarchy.DescentResetChannelPanels

namespace OAI
/-! # Repack all selected GL channels into the smaller terminal stencil lanes in one scan -/
namespace Hierarchy.DescentSixParty.PackedFlow.Channels
open DescentGLPacked DescentGLPacked.BankImage DescentGL DescentSIMDLookup DescentColonies DescentPlainTerminal.Suffix
open DescentIssuedFallbackPanel ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {D H h l c b w M R K a G : ℕ}
local notation "m" => h+l
local notation "r" => m-c

def tableAt (X : Fin D→Fin H→Fin G→Cell a) (v : Fin (D*H)) := X (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2

private theorem offsetAt (d : Fin D) (v : Fin H) (i : Fin (chunks G M)) :
    (row (D*H) G M (finProdFinEquiv (d,v),i)).val=d.val*H*chunks G M+(row H G M (v,i)).val := by
  change i.val+chunks G M*(v.val+H*d.val)=d.val*H*chunks G M+(i.val+chunks G M*v.val)
  ring

private theorem dataAt (X : Fin D→Fin H→Fin G→Cell a) (d : Fin D) (v : Fin H) (i : Fin (chunks G M)) :
    data (tableAt X) (finProdFinEquiv (d,v),i)=data (X d) (v,i) := by
  simp only [data,tableAt,Equiv.symm_apply_apply]

theorem repack (small : c≤ m) (lanes : R*M*2^r=2^l) (oldCount : 2^c=K*(R*M))
    (ratio : 0<R) (pos : 0<M) (B : Bank) (base : ℕ) (L : DescentGL.Layout m)
    (X : Fin D→Fin H→Block m→Cell b) (mem : Memory w)
    (issued : ∀d,Dense (h:=h) (l:=l) (slice B.base H (2^h) d) (fun v x=>X d v ((rearrange L).symm x)) mem)
    (prior : B.Fits w base) (space : D*H*2^h≤B.size)
    (fit : Subwords.finish base (b*2^r) (D*H) (2^c) R M<2^w) :
    let a:=b*2^r
    let H':=D*H
    let G:=2^c
    let T:=Subwords.chart base a H' G R M
    let out:=Subwords.destination base a H' G R M
    let I:=Subwords.literals (w:=w) base H' a oldCount ratio pos
    let N:=H'*chunks G M
    let procedure:=I.program.seq (scan w out N (Subwords.term T B))
    ∃dst,procedure.Exec mem dst ((4+10*I.length)+(4+N*(2*(Subwords.term T B).work+4))) ∧
      CheapCode procedure ∧ (∀d (p : Row H G M),dst (slice out H (chunks G M) d+(row H G M p).val)=
        ((data (blockValues small (X d) L) p).val:Word w)) ∧
      ∀a,a<base ∨ Subwords.finish base (b*2^r) H' G R M≤a→dst a=mem a := by
  intro a HH G T out I rows proc
  let values:=fun d=>blockValues small (X d) L
  have product : 2^c*2^r=2^m:=by rw [←pow_add,Nat.add_sub_of_le small]
  have count : chunks G (R*M)=2^h := by
    have cut:=chunks_group G (R*M) (2^r) (Nat.mul_pos ratio pos) (Nat.two_pow_pos _)
    change chunks (2^c*2^r) (R*M*2^r)=chunks G (R*M) at cut
    rw [product,lanes,chunk_count] at cut
    exact cut.symm
  have old (p : Row HH G (R*M)) : mem (B.base+(row HH G (R*M) p).val)=((data (tableAt values) p).val:Word w) := by
    rcases p with ⟨v,i⟩
    obtain ⟨⟨d,v⟩,rfl⟩:=finProdFinEquiv.surjective v
    rw [offsetAt,dataAt]
    have got:=grouped_remix small lanes (Nat.mul_pos ratio pos) (slice B.base H (2^h) d) (X d) L mem (issued d) (v,i)
    refine (congrArg mem ?_).trans got
    change B.base + (d.val*H*chunks G (R*M) + _) = B.base + d.val*H*2^h + _
    rw [← Nat.add_assoc]
    exact congrArg (fun n => B.base + d.val*H*n + (row H G (R*M) (v,i)).val) count
  obtain ⟨dst,run,cheap,valid,outer⟩:=Subwords.saved base B oldCount ratio pos (tableAt values) mem prior
    (by change D*H*chunks G (R*M) ≤ B.size; rw [count]; exact space) old fit
  refine ⟨dst,run,cheap,?_,outer⟩
  rintro d ⟨v,i⟩
  have word:=valid (finProdFinEquiv (d,v),i)
  rw [offsetAt,dataAt] at word
  simpa only [slice,Nat.add_assoc] using word

end
end Hierarchy.DescentSixParty.PackedFlow.Channels

end OAI
