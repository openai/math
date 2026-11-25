import OAI.Computability.IntegerMultiplication.Hook.Swap

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Hook
open Code Strip Dims Strip.Optic Adic Packed Net Net.Tensor Net.Walsh Phase Haze Staff Loom Axon Earth
open Dusk
open Matrix Finset
noncomputable section
variable {A Z R:Type} {p t:Tape} {s:Series A} {L f k : ℕ}
variable [CommRing R]
abbrev member (i:Fin k) := spray (P:=p) (V:=t) i f
-- update Deck implementation common position
def freeze (i:Fin k) (x:Deck f k) (v:Fin f→B) : Deck f k :=
  fun j=> (layBit k).symm (Function.update (layBit k (x j)) i (v j))
theorem spray_reads (i:Fin k) (x : Base p t (Deck f k)) (u:Fin f) :
    (member (p:=p) (t:=t) (f:=f) i x).1 u=layBit _ (x.2.1 u) i := by
  let H := connector p t f i
  obtain ⟨x,rfl⟩ := H.cast.surjective x
  change (target p t _ _ (Fin f) (H.cast.symm (H.cast x))).1 u=_
  rw [Equiv.symm_apply_apply,show H.cast x = _ from contract i x]
  exact (step_q i (x.2.1 u)).symm

theorem spray_fills (i:Fin k) (x : Base p t (Deck f k)) (y : Walsh.Addr (Fin f)) :
    let H := member (p:=p) (t:=t) (f:=f) (k:=k) i
    H.symm (y,(H x).2)= (x.1,freeze i x.2.1 y,x.2.2) := by
  dsimp only
  let l := connector p t f i
  obtain ⟨x,rfl⟩ := l.cast.surjective x
  change l.cast ((target p t _ _ (Fin f)).symm
    (y,(target p t _ _ _ (l.cast.symm (l.cast x))).2))=_
  rw [Equiv.symm_apply_apply,show ∀ x,l.cast x = _ from fun x=>contract i x]
  refine Prod.ext rfl (Prod.ext (funext fun j=> ?_) rfl)
  apply (layBit _).injective
  let a := x.2.1 j
  let q := pulse.symm (y j,(pulse a).2)
  change layBit _ ((letter i).cast q)= layBit _ ((layBit _).symm _)
  rw [Equiv.apply_symm_apply]
  funext t
  by_cases h:t=i
  · subst t; change layBit _ ((letter i).cast q) i=Function.update (α:=Fin k) (β:=fun _=> B) _ i (y j) i
    rw [step_q i,Function.update_self]; rfl
  change layBit _ ((letter i).cast q) t=Function.update (α:=Fin k) (β:=fun _=> B) _ i _ t
  rw [Function.update_of_ne h]
  rw [show l.cast x = _ from contract i x]
  exact step_right i t (Ne.symm h) q a rfl

-- logical vs physical. r_i spectator decomposed separately using lens onto complete universe.
variable {e : A ≃ Z × Scr (Fin f) L} {b : Fin L} {v : Fin k}
structure Stream (M : Slot s p (useD f k) t) (e : A ≃ Z×Scr (Fin f) L) (b : Fin L) (v : Fin k) : Prop where
  can (a j) : layBit k (M.read a j) v=(e a).2 j b
  report (a) (y:Walsh.Addr (Fin f)) :
    e (M.alter a (freeze v (M.read a) y))=((e a).1,replaceAt b (e a).2 y)

def logic (M : Tensor.Mat B R) (x:Z×Scr (Fin f) L→R) : Z × Scr (Fin f) L→R :=
  fun i=> (zoom b M *ᵥ (fun a=>x (i.1,a))) i.2
theorem verify (s' : Slot s p (useD f k) t) (M : Tensor.Mat B R)
    (h : Stream s' e b v) (x : Z × Scr (Fin f) L → R) (a : A) :
    logic (b:=b) M x (e a)=
      operate (member v (f:=f)) (mat (fun (_:Fin f)=>M))
        (x ∘ e ∘ s'.view.cast.symm) (s'.view.cast a) := by
  rw [logic,retinal b M]
  let d := s'.view.cast
  let D := member (p:=p) (t:=t) (f:=f) v
  change ∑ z,mat _ (who b (e a).2) z*x _ =
    ∑ z : Walsh.Addr (Fin f),mat _ (D (d a)).1 z * x (e (d.symm (D.symm (z,(D (d a)).2))))
  apply sum_congr rfl
  intro m _
  rw [show D.symm (m,(D (d a)).2) = _ from spray_fills v _ m]
  have z : who b (e a).2=(D (d a)).1 := by
    funext j; rw [spray_reads]; exact (h.can a j).symm
  rw [z]
  congr 2
  exact (h.report a _).symm
-- theorem giving stage. effort
section
variable {I J W N : Type} [Fintype J] [DecidableEq J] [Fintype W] (d : Guild J W N Motif.sigma)
    (R₁ : Series W)
variable {U A Z : I→Type} {K F L w B₁ : I→ℕ} {r : Regime I}
variable (P T : I→Tape) (card : ArrayCards r P T w)
    (K' : Realizes r K) (F' : Realizes r F)
    (safe' : ∀ i,Phase.safe (F i) (K i)) (small : ∀ i,F i≤w i+1)
    (pos : ∀ i,1≤F i)
variable (s : (i:I)→Series (U i)) (h : ∀ i,(s i).count*(w i+1)≤B₁ i)
variable (z:(i:I)→Series (A i)) (j : ∀ i, Slot (z i) (P i) (useD (F i) (K i)) (T i))
variable (e : (i:I)→A i≃Z i × Scr (Fin (F i)) (L i))
variable (b:(i:I)→Fin (L i)) (v:(i:I)→Fin (K i))
variable (hv:Realizes r (fun i=> (v i).val)) (u : ∀ i, Stream (j i) (e i) (b i) (v i))
include d R₁ card K' F' safe' small pos h j hv u
theorem dawn
    (x : (i:I)→Z i × Scr (Fin (F i)) (L i)→U i→ Grain (w i)) :
    Breeze (expense K F) r (fun i=>(z i).count) B₁
      (together r.header (orchid z s w fun i=> x i ∘ e i))
      (orchid z s w fun i=> (runOn (logic (b:=b i) Walsh.F) (x i)) ∘ e i) := by
  let g (i:I) := connector (P i) (T i) (F i) (v i)
  let k (i:I) := (v i).val
  let M (i:I) := K i-k i-1
  let a i := (j i).view
  let δ (i:I) := x i ∘ (e i) ∘ (a i).cast.symm ∘ (g i).cast
  have HM : Realizes r M :=
    (K'.minused hv).minused (Realizes.fix 1)
  have S (i:I) : width (k i) (M i)=K i := by unfold width k M; dsimp only [k]; have := (v i).isLt; omega
  have hs : ∀ i,Phase.safe (F i) (width (k i) (M i)) := by intro i; rw [S]; exact safe' i -- safe ambiguous
  have C :=
    Earth.hyper P T k M F w card.prefix_ card.trail hv HM F' card.digits s h d R₁ δ small card.below hs pos
  have t0 : (fun i=> width (k i) (M i))= K := funext S
  let H i := (a i).thenDo (g i).back
  change Breeze _ _ (fun i=> (plain (P i) (T i) _ _ _).count) _ _ _ at C
  have U₁ (i:I) := (H i).cost.symm
  change ∀ i,(plain (P i) (T i) (k i) (M i) (F i)).count = (z i).count at U₁
  simp_rw [U₁] at C
  rw [t0] at C
  unfold lake orchid cloth stackRun at C
  change Breeze _ _ _ _
    (together _ (fun i:I=> stripe (plain ..) (fun a=>stripe (s i) (fun y=> Code.send (Dusk.mark (δ i a y))))))
    (fun i:I=> stripe (plain (P i) (T i) _ _ _) _) at C
  have Pz (i:I) (f) := (H i).packet f
  change ∀ i f,stripe (plain (P i) (T i) (k i) (M i) (F i)) f=stripe (z i) (f ∘ (H i).cast) at Pz
  simp_rw [Pz] at C
  let D (i:I) := target (P i) (T i) (k i) (M i) (Fin (F i))
  have q (i:I) : δ i ∘ (H i).cast=x i ∘ (e i) := by
    funext t
    change x i (e i ((a i).cast.symm ((g i).cast ((g i).cast.symm ((a i).cast t)))))=_
    rw [Equiv.apply_symm_apply,Equiv.symm_apply_apply]; rfl
  have B (i:I) : runOn (operate (D i) (mat (fun _=> Walsh.F))) (δ i) ∘ (H i).cast =
                 runOn (logic (b:=b i) Walsh.F) (x i) ∘ (e i) := by
    funext v₁ z₁
    exact (verify (j i) (R:=Grain (w i)) Net.Walsh.F (u i) (fun a=> x i a z₁) v₁).symm -- RHS corresponds operate spray includes f∘cast.symm includes g? D trans, spray; defeq forward inverse understands
  convert C using 1
  · unfold orchid cloth stackRun
    congr 1
    funext i; try rw [(H i).packet]; apply congrArg (stripe _)
    funext v; apply congrArg (stripe _); funext t
    exact congrArg (Code.send ∘ Dusk.mark) (congrFun (congrFun (q i) v) t).symm
  unfold orchid cloth stackRun
  funext i; apply congrArg (stripe _)
  funext v; apply congrArg (stripe _); funext t
  exact congrArg (Code.send ∘ Dusk.mark) (congrFun (congrFun (B i) v) t).symm
end
end
end Hook

end IntegerMultiplication
end Computability
end OAI
