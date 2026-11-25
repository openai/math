import OAI.Hierarchy.DescentTerminalChronologicalIssue
import OAI.Hierarchy.DescentTerminalPositionGather
import OAI.Hierarchy.DescentTerminalVertexFields

namespace OAI
/-! # Reading chronological leaf codes from booked position rows -/
namespace Hierarchy.DescentTerminalSiteShelves
open DescentTerminalRowBooks DescentTerminalSpanBook DescentTerminalBinPack
open DescentTerminalRecipeRows DescentTerminalChronologicalBooks DescentTerminalDenseWindow
open DescentKernelHistory (Recipe)
open Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V W B pool S ℓ : ℕ}
variable (sites : Fin S→Site) (wp : 0<W) (qp : 0<q) (fit : ∀i,(sites i).rows q≤W)
    (recipes : ∀i,(v : Fin (sites i).nodes)→Recipe (Fin t) (Fin ((sites i).arity v))) (birth : ∀i,Birth (recipes i))
    (hH : ∀i v,Fintype.card (recipes i v).Hidden≤H) (hN : ∀i v,Fintype.card (recipes i v).Node≤N)
    (hA : ∀i v j,(recipes i v).arity j≤A) (hw : ∀i v j,(recipes i v).width j≤w)
    (hv : ∀i,(sites i).nodes≤V) (short : ∀i v,(sites i).arity v≤q)
    (space : purchased W (counts (q:=q) sites) ≤ pool)
local notation "books" => fun i=>actual (sites i) (recipes i) (birth i) (hH i) (hN i) (hA i) (hw i) (hv i) (short i)
local notation "tape" => DescentTerminalChronologicalIssue.leaf sites wp qp space recipes birth hH hN hA hw hv
local notation "atRow" => DescentTerminalRowBooks.rowAddress sites wp space

theorem decoded (bp : 0<B) (start : Fin S→ℕ) (stream : ℕ→Bool) (leg : rowRange q t H N A w≤2^ℓ)
    (small : ∀i,(sites i).nodes*ℓ≤B) (texture : ∀i,Texture (books i) (start i) ℓ stream) (i : Fin pool) :
    entry (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) qp ℓ (chosen sites fit books start stream bp i)=
      DescentTerminalLeafFold.code (tape i) := by
  cases hit:resolve sites fit i.val with
  | none=>
    have off (a : LocalRow (q:=q) sites) : atRow a≠i := by
      intro eqn
      have hm:=congrArg Fin.val eqn
      let u:=a.2.castLE (fit a.1)
      have existsRow:= (resolve_iff sites fit i.val a.1 u).mpr ⟨a.2,hm.symm,rfl⟩
      simp [hit] at existsRow
    rw [DescentTerminalChronologicalIssue.leaf_gap sites wp qp space recipes birth hH hN hA hw hv i off]
    let skip : Fin B:=⟨0,bp⟩
    simpa [chosen,hit,skip,DescentTerminalLeafFold.code] using (entry_blank (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (ℓ:=ℓ) qp (0:Fin (V+1)) skip (0:Word B) (0:Word B))
  | some pair=>
    rcases pair with ⟨v,u⟩
    obtain ⟨r,ordinal,localEq⟩:=(resolve_iff sites fit i.val v u).mp hit
    have numbered : atRow ⟨v,r⟩=i:=Fin.ext ordinal.symm
    have modeEq : modeAt ((sites v).portRows q) u=mode (sites v) r (fit v):=by
      apply Fin.ext
      by_cases p:r.val<(sites v).portRows q <;> simp [modeAt,mode,localEq,p]
    simp only [chosen,hit,Option.elim_some]
    rw [entry_read (books v) (start v) stream bp leg (small v) (texture v),modeEq,selected_mode,
      ←numbered,DescentTerminalChronologicalIssue.leaf_at]
    rfl

theorem decoded_fields (bp : 0<B) (start : Fin S→ℕ) (stream : ℕ→Bool)
    (small : ∀i,(sites i).nodes*DescentTerminalVertexFields.span q t H N A w≤B)
    (source : ∀i,DescentTerminalVertexFields.Source (books i) (start i) stream) (i : Fin pool) :
    entryBy (DescentTerminalVertexFields.decode (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)) qp (chosen sites fit books start stream bp i)=
      DescentTerminalLeafFold.code (tape i) := by
  cases hit:resolve sites fit i.val with
  | none=>
    have off (a : LocalRow (q:=q) sites) : atRow a≠i := by
      intro eqn
      have hm:=congrArg Fin.val eqn
      let u:=a.2.castLE (fit a.1)
      have existsRow:= (resolve_iff sites fit i.val a.1 u).mpr ⟨a.2,hm.symm,rfl⟩
      simp [hit] at existsRow
    rw [DescentTerminalChronologicalIssue.leaf_gap sites wp qp space recipes birth hH hN hA hw hv i off]
    let skip : Fin B:=⟨0,bp⟩
    simpa [chosen,hit,skip,DescentTerminalLeafFold.code] using (entryBy_blank (DescentTerminalVertexFields.decode (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)) qp (0:Fin (V+1)) skip (0:Word B) (0:Word B))
  | some pair=>
    rcases pair with ⟨v,u⟩
    obtain ⟨r,ordinal,localEq⟩:=(resolve_iff sites fit i.val v u).mp hit
    have numbered : atRow ⟨v,r⟩=i:=Fin.ext ordinal.symm
    have modeEq : modeAt ((sites v).portRows q) u=mode (sites v) r (fit v):=by
      apply Fin.ext
      by_cases p:r.val<(sites v).portRows q <;> simp [modeAt,mode,localEq,p]
    simp only [chosen,hit,Option.elim_some]
    rw [entryBy_read _ (books v) (start v) stream bp (DescentTerminalVertexFields.vertex_read (books v) (start v) stream bp (small v) (source v)),modeEq,selected_mode,
      ←numbered,DescentTerminalChronologicalIssue.leaf_at]
    rfl

end
end Hierarchy.DescentTerminalSiteShelves

end OAI
