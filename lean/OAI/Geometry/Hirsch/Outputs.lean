import OAI.Geometry.Hirsch.Propagation

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

open Forest

variable {I : Type} {B V h : ℕ}

abbrev Space (I : Type) (B V : ℕ) := Vec (Port I B V)
abbrev Form (I : Type) (B V : ℕ) := Space I B V →ₗ[ℝ] ℝ

def W (i : I) (l : Fin V) : Form I B V := LinearMap.proj (i,none,false,l)
def P (i : I) (l : Fin V) : Form I B V := W i l + LinearMap.proj (i,none,true,l)
def terminal (i : I) (b : Fin B) (pos : Position V) : Form I B V := LinearMap.proj (i,some b,pos)

def base (i : I) (pos : Position V) : Form I B V :=
  if pos.1 then P i pos.2 else W i pos.2

variable (tree : Forest I (Fin V) h)

def quick (i : I) (pos : Position V) (b : Fin B) : Form I B V :=
  (if tree.depth i < h then base i pos else 0) + terminal i b pos

def output (eps : I → ℝ) (i : I) (pos : Position V) (b : Fin B) : ℕ → Form I B V
  | 0 => quick tree i pos b
  | k+1 => if hk : k < tree.depth i then
      P (tree.node i (k+1)) (tree.path i)[k].2 + eps (tree.node i (k+1)) • output eps i pos b k
    else output eps i pos b k

theorem output_next (eps : I → ℝ) (i : I) (pos : Position V) (b : Fin B) {k : ℕ}
    (hk : k < tree.depth i) (x : Space I B V) :
    output tree eps i pos b (k+1) x =
      P (tree.node i (k+1)) (tree.path i)[k].2 x + eps (tree.node i (k+1)) * output tree eps i pos b k x := by
  simp [output,hk]

def impulse (i : I) (b : Fin B) (w v f g : Values V) : Space I B V := by
  classical
  exact fun (j,role,kind,l) => if j = i then
    match role with
    | none => if kind then v l - w l else w l
    | some d => if d = b then (if kind then g l else f l) else 0
    else 0

namespace impulse

variable (i : I) (b : Fin B) (w v f g : Values V)

theorem supported {usable : Set (Port I B V)} (hr : Ready usable b i) :
    impulse i b w v f g ∈ OAI.Geometry.Hirsch.supported usable := by
  rintro ⟨j,role,kind,l⟩ hn
  by_cases he : j = i
  · subst j
    cases role with
    | none => exact (hn (hr _).1).elim
    | some d =>
      have hh : d ≠ b := by rintro rfl; exact hn (hr _).2
      simp [impulse,hh]
  · simp [impulse,he]

@[simp] theorem width (l : Fin V) : W i l (impulse i b w v f g) = w l := by simp [W,impulse]

@[simp] theorem price (l : Fin V) : P i l (impulse i b w v f g) = v l := by simp [P,W,impulse]

@[simp] theorem endpt (d : Fin B) (pos : Position V) :
    terminal i d pos (impulse i b w v f g) =
      if d = b then (if pos.1 then g pos.2 else f pos.2) else 0 := by
  cases pos; simp [terminal,impulse]

theorem other {j : I} (hn : j ≠ i) (role : Option (Fin B)) (pos : Position V) :
    impulse i b w v f g (j,role,pos) = 0 := by cases pos; simp [impulse,hn]

theorem zero (he : impulse i b w v f g = 0) : w = 0 ∧ v = 0 ∧ f = 0 ∧ g = 0 := by
  refine ⟨funext fun l => ?_,funext fun l => ?_,funext fun l => ?_,funext fun l => ?_⟩
  · simpa using congrArg (W i l) he
  · simpa using congrArg (P i l) he
  · simpa using congrArg (terminal i b (false,l)) he
  · simpa using congrArg (terminal i b (true,l)) he

end impulse

def Silent (x : Space I B V) (i : I) : Prop := ∀ role pos, x (i,role,pos) = 0

theorem Silent.price {x : Space I B V} {i : I} (hs : Silent x i) (l : Fin V) : P i l x = 0 := by
  simp [P,W,hs none]

theorem Silent.quick {x : Space I B V} {i : I} (hs : Silent x i) (pos : Position V) (b : Fin B) :
    Layer.quick tree i pos b x = 0 := by
  unfold Layer.quick base
  split <;> simp [terminal,hs (some b)]
  split <;> simp [hs.price,W,hs none]

end OAI.Geometry.Hirsch.Layer
