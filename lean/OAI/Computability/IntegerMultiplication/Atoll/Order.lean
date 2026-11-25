import OAI.Computability.IntegerMultiplication.Cap.Mix
import OAI.Computability.IntegerMultiplication.Loom.Tracks

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Strip Loom Cap
variable {A B C D:Type}
def Lex (ia : A→A→Prop) (ib:B→B→Prop) (x y:A×B) :=
  ia x.1 y.1 ∨ x.1=y.1 ∧ ib x.2 y.2

abbrev Runs (s:Series A) (L:A→A→Prop):=s.explore.Pairwise L

theorem prodRuns (s:Series A) (t:Series B) (la:A→A→Prop) (lb:B→B→Prop)
    (h:Runs s la)(f:Runs t lb):
    Runs (s.cart t) (Lex la lb) := by
  rw [Runs,←Series.tab_id,Series.grouped]
  change ((s.explore.map (fun a=> t.explore.map (fun b=>(a,b)))).flatten).Pairwise _
  rw [List.pairwise_flatten]
  simp only [List.mem_map,List.pairwise_map]
  constructor
  · rintro _ ⟨x,_,rfl⟩
    apply List.pairwise_map.mpr
    exact f.imp (fun h=> Or.inr ⟨rfl,h⟩)
  refine h.imp (fun {a b} h x z y u=>?_ )
  obtain ⟨x,_,rfl⟩:=z
  obtain ⟨y,_,rfl⟩:=u
  exact Or.inl h

variable (s:Series A) (e:A≃B)
theorem transfer {la:A→A→Prop}{lb:B→B→Prop}(g:Runs s la)
    (p:∀ a b,la a b→lb (e a) (e b)):
    Runs (s.via e) lb :=
  List.pairwise_map.mpr (g.imp (fun h=> p _ _ h)) -- implicit binders?
theorem sameness {u:Series A}{l:A→A→Prop} [Std.Antisymm l] [Std.Irrefl l]
    (q:Runs s l)(h:Runs u l):s=u := by
  have p:s.explore=u.explore:= q.eq_of_mem_iff h (fun i=> ⟨fun _=>u.complete i,fun _=>s.complete i⟩)
  cases s; cases u; congr -- simp?

abbrev Digit (n:ℕ):Fin n→Fin n→Prop:=fun i j=>i.val<j.val
theorem clock (n:ℕ):Runs (Series.natural n) (Digit n):= by
  apply List.pairwise_iff_getElem.mpr
  change ∀ i j (_:i<(List.finRange _).length)(_:j<(List.finRange _).length)(_:i<j),Digit _ _ _
  simp [Digit,Series.natural,Series.fixed]
variable {d:ℕ} {r : Bounds d}
def Rise (a b:Vector_ r):Prop:=∃i : Fin d, Digit (r i) (a i) (b i) ∧ ∀j,j< i → a j=b j
def Fall (a b:Vector_ r):Prop:=∃i : Fin d, Digit (r i) (a i) (b i) ∧ ∀j,i<j→a j=b j
private theorem rising (a b:Vector_ r) (h:Rise a b)(e:Rise b a):False:=by
  obtain ⟨i,t,f⟩:=h; obtain ⟨j,v,g⟩:=e
  rcases lt_trichotomy i j with p|p|p
  · unfold Digit at t; rw [g i p] at t; exact lt_irrefl _ t
  · subst j; exact Nat.not_lt_of_ge t.le v
  unfold Digit at v; rw [f j p] at v; exact lt_irrefl _ v
private theorem falling (a b:Vector_ r) (h:Fall a b)(e:Fall b a):False:=by
  obtain ⟨i,t,f⟩:=h; obtain ⟨j,v,g⟩:=e
  rcases lt_trichotomy j i with p|p|p
  · unfold Digit at t; rw [g i p] at t; exact lt_irrefl _ t
  · subst i; exact Nat.not_lt_of_ge t.le v
  unfold Digit at v; rw [f j p] at v; exact lt_irrefl _ v
instance : Std.Antisymm (Rise (r:=r)):= ⟨fun a b p v=>False.elim (rising a b p v)⟩
instance : Std.Irrefl (Rise (r:=r)):=⟨fun a p=>rising a a p p⟩
instance : Std.Antisymm (Fall (r:=r)):= ⟨fun a b p v=>False.elim (falling a b p v)⟩
instance : Std.Irrefl (Fall (r:=r)):=⟨fun a p=>falling a a p p⟩

abbrev Vacant (r : Bounds 0) : Unit≃Vector_ r where
  toFun _:=fun i=>Fin.elim0 i; invFun _:=()
  left_inv _:=rfl;right_inv _x:=funext fun v=>v.elim0
abbrev Expand (r:Bounds (d+1)):= (Fin.consEquiv (fun i:Fin (d+1)=>Fin (r i)))
abbrev Contract (r:Bounds (d+1)):= (Equiv.prodComm _ _).trans (Expand r)

def top : {d:ℕ}→(r:Bounds d)→ Series (Vector_ r)
| 0,r => Series.one.via (Vacant r)
| _d+1,r=> ((Series.natural (r 0)).cart (top (body r))).via (Expand r)
def bot : {d:ℕ}→(r:Bounds d)→ Series (Vector_ r)
| 0,r => top r
| _d+1,r=> ((bot (body r)).cart (Series.natural (r 0))).via (Contract r)

variable (r)
theorem best : Runs (top r) Rise := by
  induction d with
  | zero=>exact List.pairwise_singleton _ _
  | succ d ih=>
    change Runs (((Series.natural (r 0)).cart (top (body r))).via _) _
    apply transfer _ _ (prodRuns _ _ (Digit _) Rise (clock _) (ih _))
    rintro ⟨a,x⟩ ⟨b,y⟩ (e|⟨t,h⟩)
    · exact ⟨0,e,fun j e=>False.elim (Nat.not_lt_zero _ e)⟩
    obtain ⟨i,f,u⟩:=h
    refine ⟨i.succ,f, ?_⟩
    intro j
    refine Fin.cases (fun _=>t) (fun k h=> ?_) j
    simp only [Expand]
    exact u _ (Fin.succ_lt_succ_iff.mp h)
theorem worst : Runs (bot r) Fall := by
  induction d with
  | zero=>exact List.pairwise_singleton _ _
  | succ d ih=>
    change Runs (((bot (body r)).cart _).via _) _
    apply transfer _ _ (prodRuns _ _ Fall (Digit _) (ih _) (clock _))
    rintro ⟨x,a⟩ ⟨y,b⟩ (h|⟨t,e⟩)
    · obtain ⟨i,f,u⟩:=h
      refine ⟨i.succ,f, ?_⟩
      intro j
      refine Fin.cases (fun e=>False.elim (Nat.not_lt_zero _ e)) (fun k h=>?_) j
      change (Expand r) (a,x) k.succ=(Expand r) (b,y) k.succ
      simp only [Expand,Fin.consEquiv_apply]
      exact u _ (Fin.succ_lt_succ_iff.mp h)
    refine ⟨0,e,?_⟩
    intro j
    refine Fin.cases (fun h=>False.elim (lt_irrefl _ h)) (fun k _=> ?_) j
    change (Expand r) (a,x) k.succ=(Expand r) (b,y) k.succ
    simp only [Expand,Fin.consEquiv_apply]
    exact congrFun t k

end Atoll

end IntegerMultiplication
end Computability
end OAI
