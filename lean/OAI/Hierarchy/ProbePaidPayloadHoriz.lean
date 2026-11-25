import OAI.Hierarchy.ProbeCoreCode
import OAI.Hierarchy.ProbePaidStripRoles
import OAI.Hierarchy.ProbePayloadFixedJoins

namespace OAI
/-! # The measured edge and both true sockets of each payload-strip horizontal -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open scoped Fin.CommRing Classical

variable {h d k R w : ℕ} {S : PurchaseSampler}

def HorizontalFaces {C V : Type*} (col : C→V) (ends : DistinctPair C) (layer : ColumnLayer k)
    (sites : ColumnSite V k × ColumnSite V k) : Prop :=
  sites=((col ends.left,layer),(col ends.right,layer)) ∨ sites=((col ends.right,layer),(col ends.left,layer))

/-- Each payload horizontal instruction is looked up in the true core ROM
and its endpoints are those of that very record's advised stage or fixed join. -/
theorem payload_faces_price (M : ℕ) (base : ℕ) (col : PayloadStrip.Columns (Stages h d)→Expr)
    (order : Fin R≃Edges S h d k) (m : Memory w) (loaded : CoreLookup.Loaded base order m)
    (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (wide : 2^h≤2^w)
    (column : ∀c,((col c).eval m (p.val:Word w)).val=((Fintype.equivFin _) (payloadPlace π p c)).val)
    (e : Fin (PayloadStrip.edgeCount (Stages h d))) (l : ColumnLayer k) :
    ∃f : Edges S h d k,
      (payloadHorizontal S h d k base col e l).eval m (p.val:Word w)=((order.symm f).val:Word w) ∧
      (coreCode S M f:ℝ)=PayloadStrip.length (Stages h d) e ∧
      HorizontalFaces (payloadPlace π p) (Strip.horizontal _ e) l (CoreBoard.ends π f) := by
  let N:=Stages h d
  have room := e.isLt
  change e.val<2*N+1 at room
  by_cases even : e.val%2=0
  · let j : Fin (N+1):=⟨e.val/2,by omega⟩
    have pos : e.val=2*j.val := by dsimp [j];omega
    have same : (⟨2*j.val,by have:=j.isLt;change 2*j.val<2*N+1;omega⟩ : Fin (PayloadStrip.edgeCount N))=e := Fin.ext pos.symm
    have pair:=payloadPlace_free π p j
    dsimp only at pair
    rw [same] at pair
    let x:=(payloadPlace π p) (Strip.horizontal _ e).left
    let y:=(payloadPlace π p) (Strip.horizontal _ e).right
    have adj : (permutationFabric h d).fixedAll (fabricBoard h d x) (fabricBoard h d y) := by
      simpa only [x,y,pair.1,pair.2.1] using payloadFree_fixed π p j
    have apart : x≠y := (payloadPlace π p).injective.ne (Strip.horizontal _ e).apart
    refine ⟨.inl (.inr (.inr (.inl (fixedLink x y adj apart,l)))),?_,by simp [coreCode,PayloadStrip.length,even],?_⟩
    · exact payload_fixed base col order m loaded (p.val:Word w) e even l x y adj apart (column _)
    · change (((fixedLink x y adj apart).val.1,l),((fixedLink x y adj apart).val.2,l))=((x,l),(y,l)) ∨
        (((fixedLink x y adj apart).val.1,l),((fixedLink x y adj apart).val.2,l))=((y,l),(x,l))
      unfold fixedLink
      split <;> first | exact Or.inl rfl | exact Or.inr rfl
  · let t : StageAt h d:=⟨e.val/2,by change e.val/2<N;omega⟩
    have pos : e.val=2*t.val+1 := by dsimp [t];omega
    have same : (⟨2*t.val+1,by have:=t.isLt;change 2*t.val+1<2*N+1;omega⟩ : Fin (PayloadStrip.edgeCount N))=e := Fin.ext pos.symm
    have pair:=payloadPlace_tile π p t
    dsimp only at pair
    rw [same] at pair
    refine ⟨.inr ((p,t),l),payload_tile base col order m loaded p e t l pos wide,by simp [coreCode,PayloadStrip.length,even],Or.inl ?_⟩
    exact Prod.ext (Prod.ext pair.1.symm rfl) (Prod.ext pair.2.1.symm rfl)

theorem payload_faces (base : ℕ) (col : PayloadStrip.Columns (Stages h d)→Expr)
    (order : Fin R≃Edges S h d k) (m : Memory w) (loaded : CoreLookup.Loaded base order m)
    (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (wide : 2^h≤2^w)
    (column : ∀c,((col c).eval m (p.val:Word w)).val=((Fintype.equivFin _) (payloadPlace π p c)).val)
    (e : Fin (PayloadStrip.edgeCount (Stages h d))) (l : ColumnLayer k) :
    ∃f : Edges S h d k,
      (payloadHorizontal S h d k base col e l).eval m (p.val:Word w)=((order.symm f).val:Word w) ∧
      HorizontalFaces (payloadPlace π p) (Strip.horizontal _ e) l (CoreBoard.ends π f) := by
  obtain ⟨f,read,_,faces⟩:=payload_faces_price 0 base col order m loaded π p wide column e l
  exact ⟨f,read,faces⟩

theorem Board.core_resolve_faces {C V : Type} (b : Board) (wide : b.rows<2^w) (col : C→V)
    (horizontal : DistinctPair C) (l : ColumnLayer k) (expr : Expr) (m : Memory w) (r : Word w)
    (v : Fin b.rows) (read : ((b.coreOnly expr).eval m r).val=v.val)
    (order : Fin b.coreRows≃Edges S h d k) (π : Equiv.Perm (Fin (2^h)))
    (mapSite : Site h d k → ColumnSite V k) (endRow : Fin b.rows → ColumnSite V k×ColumnSite V k)
    (core : ∀f,endRow (b.coreIndex (order.symm f))=Prod.map mapSite mapSite (CoreBoard.ends π f))
    (raw : ∃f,expr.eval m r=((order.symm f).val:Word w) ∧
      HorizontalFaces col horizontal l (Prod.map mapSite mapSite (CoreBoard.ends π f))) :
    HorizontalFaces col horizontal l (endRow v) := by
  obtain ⟨f,word,pair⟩:=raw
  have resolved:=b.coreOnly_read expr m r (order.symm f) wide word
  have fit : (order.symm f).val<2^w := (b.coreIndex (order.symm f)).isLt.trans wide
  have index : v=b.coreIndex (order.symm f) := Fin.ext <|
    read.symm.trans ((congrArg Fin.val resolved).trans (Fin.val_cast_of_lt fit))
  rw [index,core]
  exact pair

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
