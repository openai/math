import OAI.Computability.NearSquareRoot.InterchangeROMLeafCommand

/-! # Local time for the shared interchange front end -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFront

open IntegerMultiplication IntegerMultiplication.Code

/-- A template bounds the size of either endpoint field. The runtime
descriptor can change at every recursive call. -/
structure Scale (I : Type) where
  endpoint : I → ℕ
  header : I → ℕ
  payload : I → ℕ

namespace Scale
variable {I : Type} (s : Scale I)

/-- A polynomial in the endpoint cardinality may multiply the data scan.
Polynomial descriptor work is additive. -/
def Cost (t : I → ℕ) : Prop :=
  ∃ a h : I → ℕ, Dom s.endpoint a ∧ Dom s.header h ∧ ∀ i, t i ≤ a i*(s.payload i+1)+h i

def Run (q r : I → Tree) := ∃ t, s.Cost t ∧ Task t q r

variable {s}

theorem Cost.mono {t u : I → ℕ} (h : s.Cost t) (le : ∀ i, u i ≤ t i) : s.Cost u := by
  obtain ⟨a,z,ha,hz,h⟩ := h
  exact ⟨a,z,ha,hz,fun i => (le i).trans (h i)⟩

theorem Cost.add {t u : I → ℕ} (h : s.Cost t) (g : s.Cost u) :
    s.Cost (fun i => t i + u i) := by
  obtain ⟨a,z,ha,hz,h⟩ := h; obtain ⟨a',z',ha',hz',g⟩ := g
  refine ⟨_,_,ha.add ha',hz.add hz',fun i => ?_⟩
  dsimp
  rw [Nat.add_mul]
  have ht := h i; have hu := g i
  omega

theorem Cost.compact {t : I → ℕ} (h : Dom s.header t) : s.Cost t :=
  ⟨fun _ => 0,t,Dom.const _ 0,h,by simp⟩

theorem Cost.scan : s.Cost s.payload :=
  ⟨fun _ => 1,fun _ => 0,Dom.const _ 1,Dom.const _ 0,by simp⟩

theorem Cost.extract {t : I → ℕ} (h : s.Cost t) :
    ∃ d C : ℕ, ∀ i, t i ≤ C * ((s.endpoint i+1)^d*(s.payload i+1)+(s.header i+1)^d) := by
  obtain ⟨a,z,⟨u,A,ua⟩,⟨v,Z,vz⟩,cost⟩ := h
  refine ⟨u+v,A+Z,fun i => (cost i).trans ?_⟩
  have h₁ := (ua i).trans (Dom.upper (by omega : u ≤ u+v) A (s.endpoint i))
  have h₂ := (vz i).trans (Dom.upper (by omega : v ≤ u+v) Z (s.header i))
  calc
    _ ≤ A*(s.endpoint i+1)^(u+v)*(s.payload i+1) + Z*(s.header i+1)^(u+v) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ h₁) h₂
    _ ≤ _ := by simp only [Nat.add_mul,Nat.mul_add]; ring_nf; omega

theorem Run.compose {p q r : I → Tree} (a : s.Run p q) (b : s.Run q r) : s.Run p r := by
  obtain ⟨t,ht,f⟩ := a; obtain ⟨u,hu,g⟩ := b
  exact ⟨_,ht.add hu,f.compose g⟩

theorem Run.left {p q : I → Tree} (a : s.Run p q) (r : I → Tree) :
    s.Run (fun i => Tree.fork (p i) (r i)) (fun i => Tree.fork (q i) (r i)) := by
  obtain ⟨t,ht,f⟩ := a
  exact ⟨t,ht,f.left r⟩

theorem Run.right {p q : I → Tree} (a : s.Run p q) (r : I → Tree)
    (size : s.Cost (fun i => (r i).count)) :
    s.Run (fun i => Tree.fork (r i) (p i)) (fun i => Tree.fork (r i) (q i)) := by
  obtain ⟨t,ht,f⟩ := a
  exact ⟨_,size.add ht,f.right r⟩

theorem Run.easy {A B : Type} [Codec A] [Codec B] {f : A → B} (p : I → A)
    (code : Easy f) (size : s.Cost (fun i => size (p i))) :
    s.Run (fun i => send (p i)) (fun i => send (f (p i))) :=
  ⟨_,size,code.on p⟩

theorem Run.poly {A B : Type} [Codec A] [Codec B] {f : A → B} (p : I → A)
    (code : Poly f) (size : Dom s.header (fun i => size (p i))) :
    s.Run (fun i => send (p i)) (fun i => send (f (p i))) := by
  obtain ⟨t,ht,run⟩ := code
  exact ⟨_,Cost.compact ((ht.map p).sub size),run.on p⟩

theorem Run.extract {p q : I → Tree} (a : s.Run p q) :
    ∃ d, Task (fun i => (s.endpoint i+1)^d*(s.payload i+1)+(s.header i+1)^d) p q := by
  obtain ⟨t,ht,run⟩ := a
  obtain ⟨d,C,hh⟩ := ht.extract
  refine ⟨d,run.bound (C+1) (fun i => ?_)⟩
  let W := (s.endpoint i+1)^d*(s.payload i+1)+(s.header i+1)^d
  change t i+1 ≤ (C+1)*(W+1)
  have le : t i ≤ C*W := hh i
  nlinarith

end Scale
end InterchangeROMFront

end NearSquareRoot
end Computability
end OAI
