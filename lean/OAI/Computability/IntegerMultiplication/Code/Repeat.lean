import OAI.Computability.IntegerMultiplication.Code.Product

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code.Task
variable {X : Type*}

/-- Suspension protocol for recursion tasks on `X`:
* Stop with the answer,
* loop on a new query of the same task,
* or push a parked tree z, compute the answer on a child, then pair
(answer, z) and loop on that as a fresh query.
Parking a tree for this protocol (and combining with or stripping the resulting
pairs) uses the tail below the active value and costs a *constant*, independent of
the parked or active sizes. It is the *producer* of z and the rest of the arguments
that must usually charge linear time for the parts it computes/traverses.
-/
inductive Event (X : Type*)
  | done
  | jump (next : X)
  | ask (child : X) (z : Tree) (next : X)

namespace Event

def signal (p f : X → Tree) (x : X) : Event X → Tree
  | done => .fork (.atom false) (f x)
  | jump y => .fork (.atom true) (.fork (.atom false) (p y))
  | ask y z _ => .fork (.atom true) (.fork (.atom true) (.fork (p y) z))

/-- Consistency of responses. -/
def sound (p f : X → Tree) (x : X) : Event X → Prop
  | done => True
  | jump k => f k=f x
  | ask y z k => f k=f x ∧ p k=.fork (f y) z

def more (b : X → ℕ) : Event X → ℕ
  | done => 0
  | jump k => b k
  | ask y _ k => b y+b k

end Event

private def askCode : Cmd :=
  splitRoot 0 (fun _ => .pass) (.join (.again 0) (.join (pack 0) (.again 0)))

private def decodeBit (c d : Cmd) : Cmd :=
  splitRoot 0 (fun _ => .pass) (splitRoot 0 (fun i => bif i then d else c) .pass)

private theorem fits_decodeBit {b : Bool} {x y : Tree} {r env n} {c d : Cmd}
    (h : Fits env (bif b then d else c) (pile 0 x r) (pile 0 y r) n) :
    Fits env (decodeBit c d) (pile 0 (.fork (.atom b) x) r) (pile 0 y r) (n+4+4) :=
  fits_pair (fits_bit h)

private def stackBody (step : Cmd) : Cmd :=
  .join step <| decodeBit .pass <| decodeBit (.again 0) askCode

private theorem bc {C D a b m : ℕ} (h : a+1+m ≤ b) (e : C+29 ≤ D) :
    C*(a+1)+D*m+29 ≤ D*b := by
  have h₁ : D * (a+1+m) ≤ D*b := Nat.mul_le_mul_left _ h
  have h₂ : (C+29)*(a+1) ≤ D*(a+1) := Nat.mul_le_mul_right _ e
  rw [Nat.add_mul] at h₂
  rw [Nat.mul_add] at h₁
  omega

theorem loop {a b : X → ℕ} {p f : X → Tree} (g : X → Event X)
    (h : Task a p fun x => Event.signal p f x (g x)) (hg : ∀ x, Event.sound p f x (g x))
    (ht : ∀ x, a x+1+Event.more b (g x) ≤ b x) : Task b p f := by
  obtain ⟨c,C,h⟩ := h
  let D := C+29
  let m := stackBody c
  refine ⟨.tie m,D+1,fun x E r => ?_⟩
  suffices hh : ∀ (x : X), Fits.value (m::E) m 0 (p x) (f x) (D*b x) from
    (Fits.tie (hh x r)).mono (by simp only [D,Nat.add_mul,Nat.one_mul,Nat.mul_add]; omega)
  intro i
  -- strong induction on budget
  suffices h' : ∀ n : ℕ, ∀ x, b x=n → Fits.value (m::E) m 0 (p x) (f x) (D*b x) by
    exact h' (b i) i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y ey w
    subst n
    have ha := h y (m::E) w
    -- reduce signal, sound and more together
    dsimp only at ha
    cases he : g y with
    | done =>
      have ht := ht y
      rw [he] at ha ht
      dsimp [Event.signal,Event.more] at ha ht
      exact (ha.join (fits_decodeBit (b := false) (c := Prog.pass) (Fits.pass _))).mono
        (Nat.le_trans (by omega : C*(a y+1)+ (1+4+4)+2 ≤ C*(a y+1)+D*0+29) (bc ht (Nat.le_refl _)))
    | jump k =>
      have eg := hg y
      have et := ht y
      rw [he] at ha eg et
      dsimp [Event.signal,Event.sound,Event.more] at ha eg et
      have hk := ih (b k) (by omega) k rfl w
      rw [eg] at hk
      refine (ha.join (fits_decodeBit (b := true) (d := _)
        (fits_decodeBit (b := false) (c := Prog.again 0) (Fits.again0 hk)))).mono
          (Nat.le_trans (by omega) (bc (D := D) et (Nat.le_refl _)))
    | ask k z j =>
      have eg := hg y
      have et := ht y
      rw [he] at ha eg et
      dsimp [Event.signal,Event.sound,Event.more] at ha eg et
      have hk := ih (b k) (by omega) k rfl (pile 0 z w)
      have hj := ih (b j) (by omega) j rfl w
      rw [eg.2, eg.1] at hj
      have he := (Fits.again0 hk).join ((fits_pack _ _ _ _ _).join (Fits.again0 hj))
      refine (ha.join (fits_decodeBit (b := true) (fits_decodeBit (b := true)
        (d := askCode) (fits_pair he)))).mono ?_
      have hp := bc (D := D) et (Nat.le_refl _)
      simp only [Nat.mul_add] at hp ⊢
      omega

-- Simpler iterator (no parking takes a single boolean constructor tag).
theorem iterate {a b : X → ℕ} {p f : X → Tree} (g : X → Option X)
    (h : Task a p fun x => match g x with
      | none => .fork (.atom false) (f x)
      | some y => .fork (.atom true) (p y))
    (hg : ∀ x y, g x=some y → f y=f x)
    (ht : ∀ x, a x + 1 + (g x).elim 0 b ≤ b x) : Task b p f := by
  apply loop (a := a) (fun x => match g x with
    | none => Event.done
    | some y => .jump y)
  · refine (h.compose (b' := fun _ => 0) ?_).mono ?_
    ·
      let d (x : X) := (g x).isSome
      let w (x : X) := match g x with
        | none => f x
        | some y => p y
      let v (x : X) := match g x with
        | none => Tree.fork (.atom false) (f x)
        | some y => (.fork (.atom true) (.fork (.atom false) (p y)):Tree)
      have hu : Task (fun _ => 0) (fun x => .fork (.atom (d x)) (w x)) v := by
        apply Task.control d
        · have e := Task.tag false (fun x : {x // d x=false} => w x)
          refine e.conform (by simp) (by simp) fun ⟨x,a⟩ => ?_
          cases y : g x <;> simp [d,w,v,y] at a ⊢
        · have e₁ := Task.tag false (fun x : {x // d x=true} => w x)
          have e₂ := Task.tag true (fun x : {x // d x=true} => Tree.fork (.atom false) (w x))
          refine (e₁.compose e₂).conform (by simp) (by simp) fun ⟨x,a⟩ => ?_
          cases y : g x <;> simp [d,w,v,y] at a ⊢
      refine hu.conform (by simp) (fun x => ?_) (fun x => ?_) <;> cases he : g x <;> simp [Event.signal,d,w,v,he]
    simp
  · intro x; cases e : g x <;> simp_all [Event.sound]; exact hg _ _ e
  · intro x; specialize ht x; cases e : g x <;> simp_all [Event.more]

end Code.Task

end IntegerMultiplication
end Computability
end OAI
