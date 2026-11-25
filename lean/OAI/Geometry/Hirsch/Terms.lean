import OAI.Geometry.Hirsch.Interpolation

noncomputable section

namespace OAI.Geometry.Hirsch.Layer

structure World (X : Type) (n : ℕ) where
  layer : X → ℕ
  bound : ∀ x, layer x < n
  live : X → Prop
  step : X → Bool → X
  west : ∀ x, live x → layer (step x false) + 1 = layer x
  east : ∀ x, live x → layer (step x true) = layer x + 1
  rank : X → ℕ
  decrease : ∀ x, live x → ∀ d, rank (step x d) < rank x

namespace World

variable {X : Type} {n : ℕ} (w : World X n)

def Full : Prop :=
  (∀ j < n, ∃ x, w.layer x = j) ∧
  ∀ x y, w.layer x + 2 = w.layer y →
    ∃ z, w.live z ∧ w.step z false = x ∧ w.step z true = y

inductive Shape where
  | tip
  | fork (west east : Shape)

def Shape.depth : Shape → ℕ
  | .tip => 0
  | .fork a b => max a.depth b.depth + 1

abbrev Term (n : ℕ) := Fin n × Shape

def freeStep : Term n → Bool → Term n
  | (i,.tip),_ => (i,.tip)
  | (i,.fork a _),false => (⟨i.val-1,by omega⟩,a)
  | (i,.fork _ b),true => (⟨min (i.val+1) (n-1),by have := i.isLt; omega⟩,b)

def free (n : ℕ) : World (Term n) n where
  layer x := x.1.val
  bound x := x.1.isLt
  live x := x.2 ≠ .tip ∧ 0 < x.1.val ∧ x.1.val+1 < n
  step := freeStep
  west := by rintro ⟨i,_ | ⟨a,b⟩⟩ hh <;> simp_all [freeStep]; omega
  east := by rintro ⟨i,_ | ⟨a,b⟩⟩ hh <;> simp_all [freeStep]; omega
  rank x := x.2.depth
  decrease := by rintro ⟨i,_ | ⟨a,b⟩⟩ hh (_ | _) <;> simp_all [freeStep,Shape.depth]

theorem full_free (n : ℕ) : (free n).Full := by
  refine ⟨fun j hj => ⟨(⟨j,hj⟩,.tip),rfl⟩,?_⟩
  rintro ⟨i,a⟩ ⟨j,b⟩ hh
  change i.val+2 = j.val at hh
  refine ⟨(⟨i.val+1,by omega⟩,.fork a b),?_,?_,?_⟩
  · simp [free]; omega
  · simp [free,freeStep]
  · simp [free,freeStep,Fin.ext_iff]; omega

def turn (d e : Bool) : ℕ := if d = e then 0 else 1

inductive Walk (ok stop : X → Prop) : X → Bool → ℕ → Prop
  | done {x d k} (good : ok x) (last : stop x) : Walk ok stop x d k
  | go {x d e k m} (good : ok x) (live : w.live x) (budget : m + turn d e ≤ k)
      (tail : Walk ok stop (w.step x e) e m) : Walk ok stop x d k

abbrev Escape (ok : X → Prop) := w.Walk ok (fun x => ¬w.live x)

variable {w} {ok stop ok' stop' : X → Prop} {x : X} {d : Bool} {k : ℕ}

theorem Walk.good (hw : w.Walk ok stop x d k) : ok x := by cases hw <;> assumption

theorem Walk.mono (hw : w.Walk ok stop x d k) (ho : ∀ x, ok x → ok' x)
    (hs : ∀ x, stop x → stop' x) : w.Walk ok' stop' x d k := by
  induction hw with
  | done hg hl => exact .done (ho _ hg) (hs _ hl)
  | go hg hl hb _ ih => exact .go (ho _ hg) hl hb ih

theorem Walk.more (hw : w.Walk ok stop x d k) {m : ℕ} (hm : k ≤ m) : w.Walk ok stop x d m := by
  cases hw with
  | done hg hl => exact .done hg hl
  | go hg hl hb ht => exact .go hg hl (hb.trans hm) ht

theorem Walk.redirect (hw : w.Walk ok stop x d k) (e : Bool) : w.Walk ok stop x e (k+1) := by
  cases hw with
  | done hg hl => exact .done hg hl
  | go hg hl hb ht =>
    refine .go hg hl ?_ ht
    unfold turn at *
    split <;> omega

theorem Walk.append (hw : w.Walk ok stop x d k) {m : ℕ}
    (hs : ∀ x, stop x → ∀ d, w.Walk ok stop' x d m) : w.Walk ok stop' x d (k+m) := by
  induction hw with
  | done _ hl => exact (hs _ hl _).more (by omega)
  | go hg hl hb _ ih => exact .go hg hl (by omega) ih

theorem induct (w : World X n) (p : X → Prop)
    (step : ∀ x, (w.live x → ∀ d, p (w.step x d)) → p x) : ∀ x, p x := by
  intro x
  induction x using (measure w.rank).wf.induction with
  | h x ih => exact step x (fun hl d => ih _ (w.decrease x hl d))

def distance (n j : ℕ) (d : Bool) := if d then n-1-j else j

def cost (n j : ℕ) (d : Bool) (k : ℕ) := k*n + distance n j d

theorem distance_lt (w : World X n) (x : X) (d : Bool) : distance n (w.layer x) d < n := by
  have := w.bound x
  unfold distance
  split <;> omega

theorem cost_step (hl : w.live x) {e : Bool} {m : ℕ} (hb : m + turn d e ≤ k) :
    cost n (w.layer (w.step x e)) e m < cost n (w.layer x) d k := by
  unfold cost
  by_cases he : d = e
  · subst e
    have hm := Nat.mul_le_mul_right n (show m ≤ k by simpa [turn] using hb)
    have h₁ := w.west x hl
    have h₂ := w.east x hl
    have h₃ := w.bound (w.step x true)
    cases d <;> simp only [distance,Bool.false_eq_true,↓reduceIte] <;> omega
  · have hm := Nat.mul_le_mul_right n (show m+1 ≤ k by simpa [turn,he] using hb)
    rw [add_mul,one_mul] at hm
    have := w.distance_lt (w.step x e) e
    omega

end World
end OAI.Geometry.Hirsch.Layer
