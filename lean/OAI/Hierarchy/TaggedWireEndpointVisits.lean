import OAI.Hierarchy.TaggedWireCoreVisits
import OAI.Hierarchy.TaggedWireCoreLayout
import OAI.Hierarchy.TaggedWireSpineVisits

namespace OAI
/-! # Per-site visit ordinals of the real settled-matrix word spines -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor VisitOrder
open scoped Classical

variable {K : ℕ} {E : Type} {G : PortGraph (Fin K) E} {xs : List E} {a b : Fin K}

def forwardBoundary (a b : Fin K) (n j : ℕ) := if a<b then j else n-j

theorem Spine.visit_ordered (diff : a≠b) (v : ℕ→Fin K) (start : v 0=a) (last : v xs.length=b)
    (walk : Steps (fun e=>(G.tail e,G.head e)) v 0 xs)
    (sp : Spine G (orderedChord a b diff).1.1 (oriented a b xs) (orderedChord a b diff).1.2)
    (j : Fin ((oriented a b xs).length+1)) :
    sp.visit j = v (forwardBoundary a b xs.length j.val) := by
  let holds (c : Fin K × Fin K) (es : List E) (index : ℕ → ℕ) : Prop :=
    ∀ (w : Spine G c.1 es c.2) (q : Fin (es.length+1)), w.visit q = v (index q.val)
  suffices h : holds (orderedChord a b diff).val (oriented a b xs) (forwardBoundary a b xs.length) from h sp j
  by_cases ord : a<b
  · have pair : (orderedChord a b diff).val = (a,b) := by simp [orderedChord,ord]
    have path : oriented a b xs = xs := by simp [oriented,ord]
    have index : forwardBoundary a b xs.length = fun n => n := by funext n;simp [forwardBoundary,ord]
    rw [pair,path,index]
    intro sp j
    exact congrFun (sp.visit_eq (fun n=>v n.val) start (fun i=>by
      simpa only [Between,Prod.fst,Prod.snd,Nat.zero_add,List.get_eq_getElem,Fin.val_castSucc,Fin.val_succ] using walk i.val i.isLt)) j
  · have pair : (orderedChord a b diff).val = (b,a) := by simp [orderedChord,ord]
    have path : oriented a b xs = xs.reverse := by simp [oriented,ord]
    have index : forwardBoundary a b xs.length = fun n => xs.length-n := by funext n;simp [forwardBoundary,ord]
    rw [pair,path,index]
    intro sp j
    have links := walk.reverse
    exact congrFun (sp.visit_eq (fun n=>v (xs.length-n.val)) (by simpa using last) (fun i=>by
      simpa only [Between,Prod.fst,Prod.snd,Nat.zero_add,List.get_eq_getElem,Fin.val_castSucc,Fin.val_succ] using links i.val i.isLt)) j

end Hierarchy.WireTelescope

namespace Hierarchy.ProbeStage.CoreBoard.WordSeats
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor WireTelescope VisitOrder AdaptiveProbe
open scoped Classical

variable {S : PurchaseSampler} {h d k K edges : ℕ} {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
variable (B : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord K)

local notation "L" => B.matrixLayout inj pad

private theorem core_between (e : Edges S h d k) :
    Between (((rowGraph (L).edge).tail (B.row e)),((rowGraph (L).edge).head (B.row e)))
      (place (ends π e).1) (place (ends π e).2) := by
  rcases B.core_order inj pad e with ⟨x,y⟩|⟨x,y⟩
  · exact Or.inl ⟨x,y⟩
  · exact Or.inr ⟨y,x⟩

theorem visit_commodity (i : Commodity (Fin (2^h)) (Stages h d) k)
    (sp : Spine (rowGraph (L).edge) ((L).original (.inr (.inl i))).1.1 ((L).steps (.inr (.inl i)))
      ((L).original (.inr (.inl i))).1.2) (j : Fin (((L).steps (.inr (.inl i))).length+1)) :
    sp.visit j = place (site π (commodityTurn i
      (forwardBoundary ((L).goods.tail i) ((L).goods.head i) (B.ordinary i).length j.val))) := by
  apply Spine.visit_ordered ((L).goodsDistinct i) (fun n=>place (site π (commodityTurn i n)))
  · exact congrArg place (commodity_start π i)
  · change place (site π (commodityTurn i (B.ordinary i).length))=place (commodityEnds π i).2
    simpa only [Mount.ordinary,List.length_map] using congrArg place (commodity_end (S:=S) π i)
  · exact (commodity_steps (S:=S) π i).map place B.row (core_between B inj pad)

theorem visit_reserve (c : Columns h d × Fin k)
    (sp : Spine (rowGraph (L).edge) ((L).original (.inr (.inr c))).1.1 ((L).steps (.inr (.inr c)))
      ((L).original (.inr (.inr c))).1.2) (j : Fin (((L).steps (.inr (.inr c))).length+1)) :
    sp.visit j = place (site π (reserveTurn c
      (forwardBoundary ((L).reserve.tail c) ((L).reserve.head c) (B.centers c).length j.val))) := by
  apply Spine.visit_ordered ((L).reserveDistinct c) (fun n=>place (site π (reserveTurn c n)))
  · rfl
  · rfl
  · exact (reserve_steps (S:=S) π c).map place B.row (core_between B inj pad)

theorem visit_fixed (e : Fin edges)
    (sp : Spine (rowGraph (L).edge) ((L).original (.inl e)).1.1 ((L).steps (.inl e)) ((L).original (.inl e)).1.2)
    (j : Fin (((L).steps (.inl e)).length+1)) :
    sp.visit j = if j.val=0 then ((L).edge e).1.1 else ((L).edge e).1.2 := by
  have size : ((L).steps (.inl e)).length=1 := rfl
  by_cases z : j.val=0
  · have eq : j=0 := Fin.ext z
    rw [ite_eq_left z,eq,Spine.visit_zero]; rfl
  · have bound : j.val<2 := by simpa only [size] using j.isLt
    have one : j.val=1 := by omega
    have eq : j=Fin.last (((L).steps (.inl e)).length) := Fin.ext (one.trans size.symm)
    rw [ite_eq_right z,eq,Spine.visit_last]; rfl

end Hierarchy.ProbeStage.CoreBoard.WordSeats

end
end OAI
