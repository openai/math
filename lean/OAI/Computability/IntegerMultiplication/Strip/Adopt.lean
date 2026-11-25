import OAI.Computability.IntegerMultiplication.Strip.Fleet

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
/-! Lexicographic compatibility. -/
variable {I J K C O : Type}
structure Adopt (s : Series I) (d : Series J) where
  cast : I ≃ J
  route {O : Type} (f : J→O) : d.tab f = s.tab (f ∘ cast)
namespace Adopt
variable {s : Series I} {t : Series J} {u : Series K} {v : Series C}

def same (s : Series I) : Adopt s s where
  cast := Equiv.refl I
  route _ := rfl

def thenDo (e : Adopt s t) (f : Adopt t u) : Adopt s u where
  cast := e.cast.trans f.cast
  route _ := by rw [f.route,e.route]; rfl

theorem cost (e : Adopt s t) : s.count=t.count := by
  have eq := congrArg List.length (e.route (fun _ => Code.Tree.atom false))
  simpa [Series.card] using eq.symm -- simp to Fintype no instance, s t

theorem packet (e : Adopt s t) (f : J → Code.Tree) :
    stripe t f = stripe s (f ∘ e.cast) := by rw [stripe_eq,e.route,stripe_eq]

def turn (s : Series I) (e : I ≃ J) : Adopt s (s.via e) where
  cast := e
  route f := Series.tab_via s e f
def back (e : Adopt s t) : Adopt t s :=
  ⟨e.cast.symm,fun {_} f => by
    rw [e.route]
    have h : (f ∘ ⇑e.cast.symm) ∘ ⇑e.cast=f := by ext x; simp
    rw [h]⟩

def split (e : Adopt s t) (h : Adopt u v) : Adopt (s.cart u) (t.cart v) where
  cast := e.cast.prodCongr h.cast
  route f := by
    -- need e.route on t.tab List(Tree) => can't; use general route polymorphism, change definition!
    rw [Series.grouped, Series.grouped,e.route]
    simp only [Function.comp_def,h.route, Equiv.prodCongr_apply]
    rfl

def rotate (s : Series I) (t : Series J) (u : Series K) :
    Adopt ((s.cart t).cart u) (s.cart (t.cart u)) :=
  ⟨Equiv.prodAssoc _ _ _,fun {_} f => by
    simp only [Series.grouped,Equiv.prodAssoc_apply,Function.comp_def]
    unfold Series.tab
    induction s.explore with
    | nil => rfl
    | cons x s ih =>
      simp only [List.map_cons,List.flatten_cons,List.flatten_append]
      rw [ih]⟩

@[simp] theorem tab_one (s : Unit → O) : Series.one.tab s = [s ()] := rfl

def skip (s : Series I) :
    Adopt (s.cart Series.one) s := ⟨Equiv.prodPUnit _,fun {_} v => by
      rw [Series.grouped]
      simp_rw [tab_one]
      unfold Series.tab
      induction s.explore with
      | nil => rfl
      | cons x l ih => simp only [List.map_cons,List.flatten_cons,ih,List.singleton_append]; rfl⟩
def omitL (s : Series I) :
    Adopt (Series.one.cart s) s := ⟨Equiv.punitProd _,fun {_} v => by
      rw [Series.grouped,tab_one]
      rw [List.flatten_cons,List.flatten_nil,List.append_nil]
      rfl⟩

end Adopt
open Code
namespace Fleet
variable {A B M N : I→Type} {s : (i:I)→Series (A i)} {d : (i:I)→Series (B i)}
variable {t : (i:I)→Series (M i)} {u : (i:I)→Series (N i)}
variable {l : I → ℕ} {r : Regime I}
theorem align (f : (i:I)→A i→Tree) (g : (i:I)→B i→Tree)
    (hs : ∀ i,Adopt (s i) (t i)) (hd : ∀ i,Adopt (d i) (u i))
    (h : Fleet r l t u (fun i => f i ∘ (hs i).cast.symm)
        (fun i => g i ∘ (hd i).cast.symm)) :
    Fleet r l s d f g := by
  have a : stackRun t (fun i => f i ∘ (hs i).cast.symm)=stackRun s f := by
    funext i; simp [stackRun,(hs i).route,Function.comp_def] -- stripe eq simpl
  have b : stackRun u (fun i => g i ∘ (hd i).cast.symm)=stackRun d g := by
    funext i; simp [stackRun,(hd i).route,Function.comp_def]
  unfold Fleet at *
  rw [a,b] at h
  simpa only [(hs _).cost] using h

-- version convenient for specializing data=payload original on logical target via hs
theorem access (f : (i:I)→M i→Tree) (g : (i:I)→N i→Tree)
    (hs : ∀ i,Adopt (s i) (t i)) (hd : ∀ i,Adopt (d i) (u i))
    (h : Fleet r l s d (fun i => f i ∘ (hs i).cast)
        (fun i => g i ∘ (hd i).cast)) :
    Fleet r l t u f g :=
  align _ _ (fun i => (hs i).back) (fun i => (hd i).back) h
end Fleet
end Strip

end IntegerMultiplication
end Computability
end OAI
