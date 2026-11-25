import OAI.Computability.IntegerMultiplication.Brief.Mantissa

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Brief
open Code Carry Bits Grid Staff Strip

variable {I:Type} (r:Regime I)
def Signed (z:I→ℤ) := ∃ x:I→S, r.Has x ∧ ∀ i,whole (x i)=z i

namespace Signed
variable {r}
theorem up {x:I→ℕ} (t:Figure r x) :
    Signed r (fun i=> (x i:ℤ)) := by
  obtain ⟨f,p,u⟩ := t
  exact ⟨_,p.thenDo positivist,fun i=> (regV _).trans (by rw [u])⟩

variable {x y:I→ℤ} (p:Signed r x) (q:Signed r y)
include p
theorem negative : Signed r (fun i=> -x i) := by
  obtain ⟨f,t,e⟩:=p
  exact ⟨_,t.ez easy_neg,fun i=> (Grid.neg_r _).trans (by dsimp only; rw [e])⟩
theorem down :
    Figure r (fun i=>(x i).natAbs) := by
  obtain ⟨f,t,e⟩:= p
  exact ⟨_,t.ez Easy.snd,fun i=> by dsimp only; rw [← e,Grid.normal]⟩
omit p in
theorem fixed (a:ℤ) : Signed r (fun _=>a) := by
  have h : |a.sign| ≤ 1 := by
    rcases lt_trichotomy (0:ℤ) a with h|h|h <;>
      first|rw [Int.sign_eq_one_of_pos h];norm_num|rw [← h];decide|rw [Int.sign_eq_neg_one_of_neg h]; norm_num
  by_cases v : 0≤a
  · have e : (a.toNat:ℤ)=a := by simp [v]
    have H := up (Figure.natural (r:=r) a.toNat); simp only [e] at H; exact H
  have w : 0≤ -a := by omega
  have e : - ((-a).toNat:ℤ)=a := by omega
  have H := (up (Figure.natural (r:=r) (-a).toNat)).negative
  simpa only [e] using H

include q
theorem operator2 {a:ℤ→ℤ→ℤ} {b:S×S→S}
    (t: Poly b) (h:∀ x y,whole (b (x,y))=a (whole x) (whole y)) :
    Signed r (fun i=>a (x i) (y i)) := by
  obtain ⟨f,T,e⟩:=p
  obtain ⟨g,u,l⟩:=q
  exact ⟨_,(T.pair u).thenDo t,fun i=> by simp only [h,e,l]⟩
theorem adding :
    Signed r (fun i=>x i+y i) := operator2 p q easy_plus.poly Grid.plus_v
theorem multiplying :
    Signed r (fun i=> x i*y i) := operator2 p q timeP timeV
theorem subtraction :
    Signed r (fun i=>x i-y i) := by simp only [sub_eq_add_neg]; exact p.adding q.negative
theorem ordered :
    Classified r (fun i=>x i<y i) := by
  obtain ⟨f,T,e⟩:=p; obtain ⟨g,Q,v⟩:=q
  exact ⟨_,(T.pair Q).thenDo beforeP,fun i=> by simp [beforeV,e,v]⟩
theorem choose {z:I→Prop} [DecidablePred z] (h:Classified r z) :
    Signed r (fun i=> if z i then x i else y i) := by
  obtain ⟨f,t,e⟩:=p; obtain ⟨g,Q,v⟩:=q; obtain ⟨a,u,H⟩:=h
  have V := (u.pair (t.pair Q)).ez (condition (X:=Bool × S × S) Prod.fst (fun i=>i.2.1) (fun i=>i.2.2) (by fun_prop) (by fun_prop) (by fun_prop))
  refine ⟨_,V,?_⟩
  intro i; specialize H i; cases w:a i <;> simp [v,e,w ▸ H]
omit q
theorem power {a} (u:Realizes r a) :
    Signed r (fun i=>x i^a i) := by
  obtain ⟨f,t,e⟩:=p
  exact ⟨_,(t.pair (f:=fun i=> tally (a i)) u).thenDo stepP,fun _=> by simp only [steps_v,e,tally_length]⟩
theorem toNat :
    Figure r (fun i=>(x i).toNat) := by
  have e := (Figure.variant (Figure.natural 0) p.down (p.ordered (.fixed 0)))
  suffices H : ∀ i, (x i).toNat=(if x i<0 then 0 else (x i).natAbs) from by simp only [H];exact e
  intro i; cases x i <;> simp

omit p
-- finite sum
variable {A:Type*} (n:ℕ)
theorem summing [AddCommMonoid A] (q:Fin n→A) :
    (List.ofFn q).sum=∑ j:Fin n,q j := by
  induction n with
  | zero=>simp
  | succ n ih=> rw [List.ofFn_succ,List.sum_cons,ih,Fin.sum_univ_succ]
theorem forming [CommMonoid A] (q:Fin n→A) :
    (List.ofFn q).prod=∏ j:Fin n,q j := by
  induction n with
  | zero=>simp
  | succ n ih=> rw [List.ofFn_succ,List.prod_cons,ih,Fin.prod_univ_succ]
variable (m:I→ℕ) (t:Realizes r m) (v:(i:I)→Fin (m i)→ℤ)
variable (s:Signed (signal m t) (fun i:Across m=> v i.1 i.2))
include s
theorem sums :
    Signed r (fun i=>∑ a,v i a) ∧ Signed r (fun i=>∏ a,v i a) := by
  obtain ⟨x,h,e⟩:=s
  let V i:=List.ofFn (fun a=>x ⟨i,a⟩)
  have H : r.Has V := harvest m t _ h
  have p i : (V i).map Grid.whole=List.ofFn (v i) := by simp [V,List.map_ofFn,Function.comp_def,e]
  exact ⟨⟨_,H.thenDo waveP,fun i=> by rw [waveV,p,summing]⟩,
    ⟨_,H.thenDo chainsP,fun i=> by rw [chainsV,p,forming]⟩⟩
end Signed
end Brief

end IntegerMultiplication
end Computability
end OAI
