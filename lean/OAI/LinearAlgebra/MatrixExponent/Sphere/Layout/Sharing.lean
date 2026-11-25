import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Encode
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Pull
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Install
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Trie
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Attaching insertion tables to sphere forms

The ordinary network contains exterior bits and any private selectors.
The closed network contains the seams. A link joins one station of each
network. All three kinds of internal states are summed independently.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Classical Finset

structure Alphabet (I : Type) where
  state : I → Type
  [fs : ∀ i, Fintype (state i)]
  width : I → ℕ
  code : ∀ i, state i ↪ (Fin (width i) → Bool)

attribute [instance] Alphabet.fs

abbrev Alphabet.State {I : Type} (A : Alphabet I) := ∀ i, A.state i

variable {F I : Type} [Fintype I] {a b : Wire} (A : Alphabet I)

structure Attach (L : Bundled (A.State → F) a b) (R : Bundled (A.State → F) .unit .unit) where
  left : I → L.V
  right : I → R.V
  left_local : ∀ v x y z s t, (∀ i, left i = v → s i = t i) →
    L.station v x y z s = L.station v x y z t
  right_local : ∀ v z s t, (∀ i, right i = v → s i = t i) →
    R.station v () () z s = R.station v () () z t

theorem Bundled.eval_equiv [Field F] {Y : Type} [Fintype Y] (G : Bundled F a b)
    (x : Val a) (y : Val b) (e : G.State ≃ Y) (f : Y → F)
    (h : ∀ s, ∏ v, G.station v x y s = f (e s)) : G.eval x y = ∑ t, f t :=
  Fintype.sum_equiv e _ _ h

namespace Attach

variable {A} {L : Bundled (A.State → F) a b} {R : Bundled (A.State → F) .unit .unit}
  (H : Attach A L R)

abbrev net : Bundled F a b where
  V := L.V ⊕ R.V
  E := L.E ⊕ (R.E ⊕ I)
  src := Sum.elim (.inl ∘ L.src) (Sum.elim (.inr ∘ R.src) (.inl ∘ H.left))
  dst := Sum.elim (.inl ∘ L.dst) (Sum.elim (.inr ∘ R.dst) (.inr ∘ H.right))
  left := .inl ∘ L.left
  right := .inl ∘ L.right
  state := Sum.elim L.state (Sum.elim R.state A.state)
  fs := Sum.rec L.fs (Sum.rec R.fs A.fs)
  width := Sum.elim L.width (Sum.elim R.width A.width)
  code := Sum.rec L.code (Sum.rec R.code A.code)
  station v x y z := Sum.elim
    (fun u => L.station u x y (fun i => z (.inl i)) (fun i => z (.inr (.inr i))))
    (fun u => R.station u () () (fun i => z (.inr (.inl i))) (fun i => z (.inr (.inr i)))) v
  locality := by
    intro v x y z x' y' z' hx hy hz
    cases v with
    | inl v =>
      have h := L.locality v x y (fun i => z (.inl i)) x' y' (fun i => z' (.inl i))
        (fun i hi => hx i (congrArg Sum.inl hi)) (fun i hi => hy i (congrArg Sum.inl hi))
        (fun i hi => hz (.inl i) (hi.imp (congrArg Sum.inl) (congrArg Sum.inl)))
      exact (congrFun h _).trans (H.left_local _ _ _ _ _ _ fun i hi =>
        hz (.inr (.inr i)) (.inl (congrArg Sum.inl hi)))
    | inr v =>
      have h := R.locality v () () (fun i => z (.inr (.inl i))) () () (fun i => z' (.inr (.inl i)))
        (fun _ _ => rfl) (fun _ _ => rfl)
        (fun i hi => hz (.inr (.inl i)) (hi.imp (congrArg Sum.inr) (congrArg Sum.inr)))
      exact (congrFun h _).trans (H.right_local _ _ _ _ fun i hi =>
        hz (.inr (.inr i)) (.inr (congrArg Sum.inr hi)))

def split : H.net.State ≃ L.State × R.State × A.State :=
  (Equiv.sumPiEquivProdPi _).trans ((Equiv.refl _).prodCongr (Equiv.sumPiEquivProdPi _))

theorem eval_net [Field F] (x : Val a) (y : Val b) :
    H.net.eval x y = ∑ s : L.State, ∑ t : R.State, ∑ u : A.State,
      (∏ v, L.station v x y s u) * ∏ v, R.station v () () t u := by
  let f (w : L.State × R.State × A.State) :=
    (∏ v, L.station v x y w.1 w.2.2) * ∏ v, R.station v () () w.2.1 w.2.2
  calc
    _ = ∑ w, f w := by
      apply H.net.eval_equiv x y H.split f
      intro s
      exact Fintype.prod_sum_type _
    _ = _ := by simp only [Fintype.sum_prod_type, f]

theorem left_arity (v : L.V) :
    H.net.arity (.inl v) = L.arity v + ∑ i, if H.left i = v then A.width i else 0 := by
  simp [Bundled.arity, net, Fintype.card_subtype, Fintype.sum_sum_type, add_assoc, add_comm,
    add_left_comm]

theorem right_arity (v : R.V) :
    H.net.arity (.inr v) = R.arity v + ∑ i, if H.right i = v then A.width i else 0 := by
  simp [Bundled.arity, net, Fintype.sum_sum_type, add_assoc]

end Attach
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-! Assignment spaces for the two forms at every cell and chunk. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Finset Classical

variable {F T X E V : Type} [Field F] [Fintype E] [Fintype V] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) T E X} {d : E → ℕ}

/-- The parameters may include ordinary selector bits. A table must read
only the ordinary ports at its assigned station. -/
structure Backdrop (C : V → Surface.Cell F (M * r) (M * t) T E X) (a b : Wire) where
  base : Bundled F a b
  owner : Place C → base.V
  param : Val a → Val b → base.State → X
  paramAt : Place C → Val a → Val b → base.State → X
  compatible : ∀ x y z, (∏ v, base.station v x y z) ≠ 0 → ∀ i,
    (item C i).table (paramAt i x y z) = (item C i).table (param x y z)
  local_param : ∀ i x y z x' y' z',
    (∀ j, base.left j = owner i → bits a x j = bits a x' j) →
    (∀ j, base.right j = owner i → bits b y j = bits b y' j) →
    (∀ e, base.src e = owner i ∨ base.dst e = owner i → z e = z' e) →
    (item C i).table (paramAt i x y z) = (item C i).table (paramAt i x' y' z')
  src : E → V
  dst : E → V
  meets : ∀ v j, j ∈ (C v).ports → src j.1 = v ∨ dst j.1 = v

abbrev Grid (M : ℕ) (I : Type) := (I × Fin M) ⊕ (I × Fin M)

def Grid.point {I : Type} : Grid M I → I := Sum.elim Prod.fst Prod.fst

def Grid.map {I J : Type} (f : I → J) : Grid M I → Grid M J :=
  Sum.map (Prod.map f id) (Prod.map f id)

namespace Profile
variable (p : Profile C d)

abbrev seam (i : E × Fin M) := Level r ((p.1 (.inl i.1)).val i.2).val

abbrev leg : Grid M (Place C) → Type :=
  Sum.elim (fun i => Level r ((p.1 (.inr i.1)).val i.2).val)
    (fun i => Level t ((p.2 i.1).val i.2).val)

instance (i : Grid M (Place C)) : Fintype (p.leg i) :=
  match i with
  | .inl _ => inferInstanceAs (Fintype (Level r _))
  | .inr _ => inferInstanceAs (Fintype (Level t _))

abbrev Seams := ∀ i, p.seam i
abbrev Legs := ∀ i, p.leg i

def first (y : p.Seams) (z : p.Legs) : p.AState
  | .inl i, j => y (i, j)
  | .inr i, j => z (.inl (i, j))

def second (z : p.Legs) : p.BState := fun i j => z (.inr (i, j))

def assignments : p.Seams × p.Legs ≃ p.AState × p.BState where
  toFun s := (p.first s.1 s.2, p.second s.2)
  invFun s := (fun i => s.1 (.inl i.1) i.2,
    Sum.rec (fun i => s.1 (.inr i.1) i.2) (fun i => s.2 i.1 i.2))
  left_inv s := by
    apply Prod.ext
    · rfl
    · funext i; cases i <;> rfl
  right_inv s := by
    apply Prod.ext
    · funext i j; cases i <;> rfl
    · rfl

structure Widths where
  seam : E × Fin M → ℕ
  leg : Grid M (Place C) → ℕ
  seam_bound : ∀ i, Fintype.card (p.seam i) ≤ 2 ^ (seam i)
  leg_bound : ∀ i, Fintype.card (p.leg i) ≤ 2 ^ (leg i)

def widths : p.Widths where
  seam i := Chunk.width r ((p.1 (.inl i.1)).val i.2).val
  leg := Sum.elim (fun i => Chunk.width r ((p.1 (.inr i.1)).val i.2).val)
    (fun i => Chunk.width t ((p.2 i.1).val i.2).val)
  seam_bound _ := Chunk.card_le _ _
  leg_bound := by rintro (i | i) <;> exact Chunk.card_le _ _

abbrev Widths.alphabet {p : Profile C d} (w : p.Widths) : Alphabet (Grid M (Place C)) where
  state := p.leg
  width := w.leg
  code i := binaryCode _ _ (w.leg_bound i)

def insertion (z : p.Legs) (x : X) (i : Place C) :=
  (item C i).table x (Chunk.states M r _ ⟨p.1 (.inr i), fun j => z (.inl (i, j))⟩)
    (p.joinB (p.second z) i)

def form (P : ℕ) (y : p.Seams) (z : p.Legs) : Grid M V → F
  | .inl (v, j) => read (firstPoint C P) (fun i => (p.first y z (source C i) j).val) (firstList C v)
  | .inr (v, j) => read (secondPoint C) (fun i => (p.second z i j).val) (secondList C v)

end Profile
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-! The scalar from reordering generators is fixed by the energy profile. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Profile
open Finset Classical

variable {F T X E V : Type} [Field F] [Fintype E] [Fintype V] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) T E X} {d : E → ℕ} (p : Profile C d)

private def signA (v : V) : F :=
  (-1) ^ Plant.shuffle (fun i j => ((p.1 (source C i)).val j).val)
    (List.finRange M) (firstList C v)

private def signB (v : V) : F :=
  (-1) ^ Plant.shuffle (fun i j => ((p.2 i).val j).val)
    (List.finRange M) (secondList C v)

def sign : F := (∏ v, p.signA v) * ∏ v, p.signB v

omit [Fintype E] in
theorem factors_split (P : ℕ) (x : X) (y : p.Seams) (z : p.Legs) :
    factors C P d x (p.joinA (p.first y z)) (p.joinB (p.second z)) =
      p.sign * ((∏ i, p.insertion z x i) * ∏ v, p.form P y z v) := by
  have ha (v : V) :
      read (firstPoint C P) (fun i => (p.joinA (p.first y z) (source C i)).val) (firstList C v) =
        p.signA v * ∏ j, p.form P y z (.inl (v, j)) :=
    Chunk.wick_chunks (firstPoint C P) (fun i => firstEnergy C d (source C i))
      (fun i => p.1 (source C i)) (fun i => p.first y z (source C i)) (firstList C v)
  have hb (v : V) :
      read (secondPoint C) (fun i => (p.joinB (p.second z) i).val) (secondList C v) =
        p.signB v * ∏ j, p.form P y z (.inr (v, j)) :=
    Chunk.wick_chunks (secondPoint C) (secondEnergy C) p.2 (p.second z) (secondList C v)
  have he (i : Place C) : (item C i).table x (p.joinA (p.first y z) (.inr i)) (p.joinB (p.second z) i) =
      p.insertion z x i := rfl
  rw [Fintype.prod_sum_type (p.form P y z), Fintype.prod_prod_type, Fintype.prod_prod_type]
  simp only [factors, he, ha, hb, prod_mul_distrib, sign]
  ring

theorem value_split (P : ℕ) (x : X) :
    p.value P x = p.sign * ∑ y : p.Seams, ∑ z : p.Legs,
      (∏ i, p.insertion z x i) * ∏ v, p.form P y z v := by
  let f (s : p.AState × p.BState) := factors C P d x (p.joinA s.1) (p.joinB s.2)
  calc
    _ = ∑ s, f s := (Fintype.sum_prod_type f).symm
    _ = ∑ s, f (p.assignments s) := (p.assignments.sum_comp _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      change ∑ y, ∑ z, factors C P d x (p.joinA (p.first y z)) (p.joinB (p.second z)) = _
      simp only [factors_split, mul_sum]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Profile
end

/-!
# Emitting a network at fixed chunk energies

A form has its own station in each cell and chunk on each sphere.
Insertion vertices retain the original exterior bits and selector wires.
Each seam state is shared by its two ends.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Finset Classical

variable {F T X E V : Type} [Field F] [Fintype E] [Fintype V] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) T E X} {d : E → ℕ} {a b : Wire}

private theorem read_ext {I : Type} {q : ℕ} {f g : I → Wedge q} (l : List I) (z : I → F)
    (h : ∀ i ∈ l, f i = g i) : read z f l = read z g l := by
  unfold read
  congr 1
  exact List.flatMap_congr fun i hi => congrArg (Surface.modes (z i)) (h i hi)

namespace Backdrop

variable (B : Backdrop C a b) (p : Profile C d)

def arm (i : Grid M (Place C)) := B.owner (Grid.point i)

def socket (i : Grid M (Place C)) : Grid M V := Grid.map Sigma.fst i

def seamEnd (s : E → V) (i : E × Fin M) : Grid M V := .inl (s i.1, i.2)

omit [Fintype E] [Fintype V] in
private theorem form_eq (P : ℕ) (v : Grid M V) (s s' : p.Seams) (z z' : p.Legs)
    (hs : ∀ e, seamEnd B.src e = v ∨ seamEnd B.dst e = v → s e = s' e)
    (hz : ∀ i, socket i = v → z i = z' i) :
    p.form P s z v = p.form P s' z' v := by
  rcases v with ⟨v, j⟩ | ⟨v, j⟩
  · apply read_ext
    simp only [firstList, secondList, List.forall_mem_append, List.forall_mem_map]
    constructor
    · intro k _
      exact congrArg Subtype.val (hz (.inl (⟨v, k⟩, j)) rfl)
    · intro k hk
      apply congrArg Subtype.val
      apply hs (k.1, j)
      simpa [seamEnd] using B.meets v k hk
  · apply read_ext
    simp only [secondList, List.forall_mem_map]
    intro k _
    exact congrArg Subtype.val (hz (.inr (⟨v, k⟩, j)) rfl)

abbrev ordinary : Bundled (p.Legs → F) a b where
  V := B.base.V
  E := B.base.E
  state := B.base.state
  width := B.base.width
  code := B.base.code
  left := B.base.left
  right := B.base.right
  src := B.base.src
  dst := B.base.dst
  station v x y s z := B.base.station v x y s *
    ∏ i, if B.owner i = v then p.insertion z (B.paramAt i x y s) i else 1
  locality := by
    intro v x y s x' y' s' hx hy hs
    funext z
    rw [B.base.locality _ _ _ _ _ _ _ hx hy hs]
    congr 1
    apply prod_congr rfl
    intro i _
    split_ifs with h
    · unfold Profile.insertion
      subst v
      rw [B.local_param _ _ _ _ _ _ _ hx hy hs]
    · rfl

abbrev chambers (P : ℕ) (w : p.Widths) : Bundled (p.Legs → F) .unit .unit where
  V := Grid M V
  E := E × Fin M
  state := p.seam
  width := w.seam
  code i := binaryCode _ _ (w.seam_bound i)
  left := Empty.elim
  right := Empty.elim
  src := seamEnd B.src
  dst := seamEnd B.dst
  station v _ _ s z := p.form P s z v
  locality := by
    intro v _ _ s _ _ s' _ _ hs
    funext z
    exact B.form_eq p P v s s' z z hs (fun _ _ => rfl)

abbrev emit (P : ℕ) (w : p.Widths) : Attach w.alphabet (B.ordinary p) (B.chambers p P w) where
  left := B.arm
  right := socket
  left_local := by
    intro v x y s z z' h
    change _ * ∏ i, (if B.owner i = v then p.insertion z (B.paramAt i x y s) i else 1) =
      _ * ∏ i, (if B.owner i = v then p.insertion z' (B.paramAt i x y s) i else 1)
    congr 1
    apply prod_congr rfl
    intro i _
    split_ifs with hi
    · have ha : (fun j => z (.inl (i, j))) = fun j => z' (.inl (i, j)) :=
        funext fun j => h (.inl (i, j)) hi
      have hb : (fun j => z (.inr (i, j))) = fun j => z' (.inr (i, j)) :=
        funext fun j => h (.inr (i, j)) hi
      unfold Profile.insertion
      change _ = (item C i).table _ _ (Chunk.states M t _ ⟨p.2 i, fun j => z' (.inr (i, j))⟩)
      rw [← ha, ← hb]
      rfl
    · rfl
  right_local v s z z' h := B.form_eq p P v s s z z' (fun _ _ => rfl) h

omit [Fintype E] in
private theorem ordinary_prod (x : Val a) (y : Val b) (s : B.base.State) (z : p.Legs) :
    (∏ v, (B.ordinary p).station v x y s z) =
      (∏ v, B.base.station v x y s) * ∏ i, p.insertion z (B.param x y s) i := by
  unfold ordinary
  rw [prod_mul_distrib, prod_comm]
  by_cases h : (∏ v, B.base.station v x y s) = 0
  · simp [h]
  · have eq (i : Place C) : p.insertion z (B.paramAt i x y s) i = p.insertion z (B.param x y s) i := by
      unfold Profile.insertion
      rw [B.compatible x y s h i]
    simp [eq]

theorem profile_eval (P : ℕ) (w : p.Widths) (x : Val a) (y : Val b) :
    p.sign * (B.emit p P w).net.eval x y =
      ∑ s : B.base.State, (∏ v, B.base.station v x y s) * p.value P (B.param x y s) := by
  rw [Attach.eval_net, mul_sum]
  apply sum_congr rfl
  intro s _
  rw [Profile.value_split]
  simp only [mul_sum]
  refine sum_congr (by ext; simp) ?_
  intro t _
  refine sum_congr (by ext; simp) ?_
  intro u _
  change p.sign * ((∏ v, (B.ordinary p).station v x y s u) * ∏ v, p.form P t u v) = _
  rw [B.ordinary_prod]
  ring

/-- Expand over public energy profiles, keeping all ordinary selectors
inside each contraction. Each profile has one scalar sign. -/
theorem expansion (P : ℕ) (w : ∀ p : Profile C d, p.Widths) (x : Val a) (y : Val b) :
    (∑ p : Profile C d, p.sign * (B.emit p P (w p)).net.diagram.eval x y) =
      ∑ s : B.base.State, (∏ v, B.base.station v x y s) * Surface.eval P C d (B.param x y s) := by
  simp only [Bundled.eval_diagram, profile_eval, eval_shapes, mul_sum]
  rw [sum_comm]

end Backdrop
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-!
# Routing whole bundles through relay stations

Every old bundle follows its own path. A relay table is the product
of the equality constraints for paths passing through it. Each old
assignment consequently has exactly one consistent extension.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Finset Classical

variable {F Y : Type} {a b : Wire} (G : Bundled F a b)

/-- The internal vertices of a directed path for each bundle. -/
structure Routes (Y : Type) where
  length : G.E → ℕ
  via : ∀ e, Fin (length e) → Y

namespace Routes
variable {G} (R : Routes G Y)

abbrev Hop := Σ e, Fin (R.length e + 1)
abbrev Data := ∀ i : R.Hop, G.state i.1

def src (i : R.Hop) : G.V ⊕ Y :=
  Fin.cases (.inl (G.src i.1)) (fun j => .inr (R.via i.1 j)) i.2

def dst (i : R.Hop) : G.V ⊕ Y :=
  Fin.lastCases (.inl (G.dst i.1)) (fun j => .inr (R.via i.1 j)) i.2

def read (v : G.V) (z : R.Data) : G.State := fun e =>
  if G.src e = v then z ⟨e, 0⟩ else z ⟨e, Fin.last _⟩

def Valid (v : Y) (z : R.Data) : Prop :=
  ∀ e j, R.via e j = v → z ⟨e, j.castSucc⟩ = z ⟨e, j.succ⟩

def copy (z : G.State) : R.Data := fun i => z i.1

theorem copy_injective : Function.Injective R.copy := by
  intro x y h
  exact funext fun i => congrFun h ⟨i, 0⟩

private theorem copy_of_valid {z : R.Data} (h : ∀ v, R.Valid v z) :
    ∃ s, R.copy s = z := by
  refine ⟨fun e => z ⟨e, 0⟩, ?_⟩
  funext i
  obtain ⟨e, j⟩ := i
  change z ⟨e, 0⟩ = z ⟨e, j⟩
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih => exact ih.trans (h _ e j rfl)

variable [Fintype Y] [Field F]

abbrev net : Bundled F a b where
  V := G.V ⊕ Y
  E := R.Hop
  src := R.src
  dst := R.dst
  state i := G.state i.1
  width i := G.width i.1
  code i := G.code i.1
  left := .inl ∘ G.left
  right := .inl ∘ G.right
  station v x y z := Sum.elim (fun u => G.station u x y (R.read u z))
    (fun u => if R.Valid u z then 1 else 0) v
  locality := by
    intro v x y z x' y' z' hx hy hz
    cases v with
    | inl v =>
      apply G.locality _ _ _ _ _ _ _ (fun i hi => hx i (congrArg Sum.inl hi))
        (fun i hi => hy i (congrArg Sum.inl hi))
      intro e he
      unfold read
      split_ifs with hs
      · exact hz ⟨e, 0⟩ (.inl (by simp [src, hs]))
      · exact hz ⟨e, Fin.last _⟩ (.inr (by simp [dst, he.resolve_left hs]))
    | inr v =>
      have hh : R.Valid v z ↔ R.Valid v z' := by
        unfold Valid
        apply forall_congr'
        intro e
        apply forall_congr'
        intro j
        apply imp_congr_right
        intro hj
        rw [hz ⟨e, j.castSucc⟩ (.inr (by simp [dst, hj])), hz ⟨e, j.succ⟩ (.inl (by simp [src, hj]))]
      simp only [Sum.elim_inr, hh]

theorem copy_prod (x : Val a) (y : Val b) (s : G.State) :
    ∏ v, R.net.station v x y (R.copy s) = ∏ v, G.station v x y s := by
  rw [Fintype.prod_sum_type]
  have hv (v : Y) : R.Valid v (R.copy s) := fun _ _ _ => rfl
  have he (v : G.V) : R.read v (R.copy s) = s := by funext e; simp [read, copy]
  simp [he, hv]

theorem eval_net : R.net.eval = G.eval := by
  funext x y
  symm
  unfold Bundled.eval
  calc
    _ = ∑ z ∈ univ.image R.copy, ∏ v, R.net.station v x y z := by
      rw [sum_image R.copy_injective.injOn]
      exact sum_congr rfl fun s _ => (R.copy_prod x y s).symm
    _ = ∑ z : R.Data, ∏ v, R.net.station v x y z := by
      apply sum_subset (subset_univ _)
      intro z _ hz
      have : ¬∀ v, R.Valid v z := fun h => hz (by
        obtain ⟨s, rfl⟩ := R.copy_of_valid h
        exact mem_image_of_mem _ (mem_univ _))
      obtain ⟨v, hv⟩ := not_forall.mp this
      exact prod_eq_zero (mem_univ (Sum.inr v : G.V ⊕ Y)) (ite_eq_right hv)
    _ = _ := by congr!

def hits (v : G.V ⊕ Y) := ∑ e, ∑ j : Fin (R.length e), if .inr (R.via e j) = v then G.width e else 0

omit [Field F] [Fintype Y] in
private theorem count_src (v : G.V ⊕ Y) :
    (∑ s, if R.src s = v then G.width s.1 else 0) =
      (∑ e, if .inl (G.src e) = v then G.width e else 0) + R.hits v := by
  unfold hits
  rw [Fintype.sum_sigma, ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  rw [Fin.sum_univ_succ]
  simp only [src, Fin.cases_zero, Fin.cases_succ]
  congr!

omit [Field F] [Fintype Y] in
private theorem count_dst (v : G.V ⊕ Y) :
    (∑ s, if R.dst s = v then G.width s.1 else 0) =
      (∑ e, if .inl (G.dst e) = v then G.width e else 0) + R.hits v := by
  unfold hits
  rw [Fintype.sum_sigma, ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  rw [Fin.sum_univ_castSucc, add_comm]
  simp only [dst, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem old_arity (v : G.V) : R.net.arity (.inl v) = G.arity v := by
  simp only [Bundled.arity, net]
  rw [count_src, count_dst]
  simp [hits, Fintype.card_subtype]

theorem relay_arity (v : Y) : R.net.arity (.inr v) = 2 * R.hits (.inr v) := by
  simp only [Bundled.arity, net]
  rw [count_src, count_dst]
  simp [two_mul]

theorem total_relay : ∑ v : Y, R.net.arity (.inr v) = 2 * ∑ e, R.length e * G.width e := by
  simp_rw [relay_arity]
  rw [← mul_sum]
  unfold hits
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro e _
  rw [sum_comm]
  simp

end Routes
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-!
# Ordinary values shared across cells

A key has a connected footprint in the seam graph. Link its storage
at each visited cell to the local readers and to the neighboring hubs.
The local factors enforce equality at each hub, even on cycles.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open scoped Classical
open Finset

variable {F T X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}

structure Sharing (C : V → Surface.Cell F (M * r) (M * t) T E X) (a b : Wire) (Y : Alphabet K) where
  src : E → V
  dst : E → V
  meets : ∀ v j, j ∈ (C v).ports → src j.1 = v ∨ dst j.1 = v
  seen : V → Finset K
  reads : Place C → Finset K
  within : ∀ i, reads i ⊆ seen i.1
  present : ∀ k, ∃ v, k ∈ seen v
  connected : ∀ k v w, k ∈ seen v → k ∈ seen w →
    Relation.EqvGen (fun p q => k ∈ seen p ∧ k ∈ seen q ∧ ∃ e, src e = p ∧ dst e = q) v w
  left : slots a → Place C
  right : slots b → Place C
  param : Val a → Val b → Y.State → X
  locality : ∀ i x y z x' y' z',
    (∀ j, left j = i → bits a x j = bits a x' j) →
    (∀ j, right j = i → bits b y j = bits b y' j) →
    (∀ k ∈ reads i, z k = z' k) →
    (item C i).table (param x y z) = (item C i).table (param x' y' z')

namespace Sharing
variable {C : V → Surface.Cell F (M * r) (M * t) T E X} {a b : Wire} {Y : Alphabet K}
  (S : Sharing C a b Y)

abbrev Vertex (_ : Sharing C a b Y) := Place C ⊕ V ⊕ V
abbrev Stores (k : K) := {v // k ∈ S.seen v}
abbrev Links (k : K) := {e // k ∈ S.seen (S.src e) ∧ k ∈ S.seen (S.dst e)}
abbrev Readers (k : K) := {i // k ∈ S.reads i}
abbrev Line (k : K) := S.Stores k ⊕ S.Links k ⊕ S.Readers k
abbrev Edge := Σ k, S.Line k
abbrev State := ∀ e : S.Edge, Y.state e.1

instance : Fintype S.State :=
  @Pi.instFintype S.Edge (fun e => Y.state e.1) (Classical.typeDecidableEq _) _ (fun e => Y.fs e.1)

def start {k : K} : S.Line k → S.Stores k
  | .inl v => v
  | .inr (.inl e) => ⟨S.src e.val, e.property.1⟩
  | .inr (.inr i) => ⟨i.val.1, S.within i.val i.property⟩

def source (e : S.Edge) : S.Vertex := .inr (.inl (S.start e.2).val)

def target : S.Edge → S.Vertex
  | ⟨_, .inl v⟩ => .inr (.inr v.val)
  | ⟨_, .inr (.inl e)⟩ => .inr (.inl (S.dst e.val))
  | ⟨_, .inr (.inr i)⟩ => .inl i.val

def checks (p : S.Vertex) (z : S.State) : Prop :=
  ∀ k (v : S.Stores k), p = .inr (.inl v.val) → ∀ e : S.Line k,
    S.source ⟨k, e⟩ = p ∨ S.target ⟨k, e⟩ = p → z ⟨k, e⟩ = z ⟨k, .inl v⟩

abbrev base : Bundled F a b where
  V := S.Vertex
  E := S.Edge
  state e := Y.state e.1
  width e := Y.width e.1
  code e := Y.code e.1
  src := S.source
  dst := S.target
  left j := .inl (S.left j)
  right j := .inl (S.right j)
  station p _ _ z := if S.checks p z then 1 else 0
  locality p _ _ z _ _ z' _ _ hz := by
    have same : S.checks p z ↔ S.checks p z' := by
      unfold checks
      refine forall_congr' fun k => forall_congr' fun v => imp_congr_right fun hp =>
        forall_congr' fun e => imp_congr_right fun he => ?_
      rw [hz _ he, hz ⟨k, .inl v⟩ (.inl hp.symm)]
    simp only [same]

def store (k : K) : S.Stores k := ⟨(S.present k).choose, (S.present k).choose_spec⟩

def decode (z : S.State) : Y.State := fun k => z ⟨k, .inl (S.store k)⟩

def encode (x : Y.State) : S.State := fun e => x e.1

omit [Field F] [Fintype K] [Fintype V] [Fintype E] in
private theorem consistent (z : S.State) (ok : ∀ p, S.checks p z) :
    S.encode (S.decode z) = z := by
  have same (k : K) (p q : S.Stores k) : z ⟨k, .inl p⟩ = z ⟨k, .inl q⟩ := by
    let value (v : V) := if h : k ∈ S.seen v then z ⟨k, .inl ⟨v, h⟩⟩ else S.decode z k
    have link (v w : V) (h : Relation.EqvGen
        (fun i j => k ∈ S.seen i ∧ k ∈ S.seen j ∧ ∃ e, S.src e = i ∧ S.dst e = j) v w) :
        value v = value w := by
      induction h with
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ i j => exact i.trans j
      | rel v w he =>
        obtain ⟨hv, hw, e, rfl, rfl⟩ := he
        let l : S.Line k := .inr (.inl ⟨e, hv, hw⟩)
        simp only [value, dite_eq_left hv, dite_eq_left hw]
        exact (ok _ k ⟨_, hv⟩ rfl l (.inl rfl)).symm.trans (ok _ k ⟨_, hw⟩ rfl l (.inr rfl))
    simpa only [value, dite_eq_left p.property, dite_eq_left q.property] using
      link _ _ (S.connected k _ _ p.property q.property)
  funext ⟨k, e⟩
  exact (same k (S.store k) (S.start e)).trans (ok _ k (S.start e) rfl e (.inl rfl)).symm

def localState (i : Place C) (z : S.State) : Y.State :=
  fun k => if h : k ∈ S.reads i then z ⟨k, .inr (.inr ⟨i, h⟩)⟩ else S.decode z k

private theorem valid (x : Val a) (y : Val b) (z : S.State)
    (hp : (∏ v, S.base.station v x y z) ≠ 0) : S.encode (S.decode z) = z := by
  apply S.consistent
  intro v
  by_contra h
  exact hp (prod_eq_zero (mem_univ v) (ite_eq_right h))

abbrev backdrop : Backdrop C a b where
  base := S.base
  owner := .inl
  param x y z := S.param x y (S.decode z)
  paramAt i x y z := S.param x y (S.localState i z)
  compatible x y z hp i := by
    refine S.locality i x y _ x y _ (fun _ _ => rfl) (fun _ _ => rfl) ?_
    intro k hk
    rw [localState, dite_eq_left hk]
    exact (congrFun (S.valid x y z hp) ⟨k, .inr (.inr ⟨i, hk⟩)⟩).symm
  local_param i x y z x' y' z' hx hy hz := by
    apply S.locality _ _ _ _ _ _ _ (fun j hj => hx j (congrArg Sum.inl hj))
      (fun j hj => hy j (congrArg Sum.inl hj))
    intro k hk
    simp only [localState, dite_eq_left hk]
    exact hz _ (.inr rfl)
  src := S.src
  dst := S.dst
  meets := S.meets

/-- Each shared assignment contributes once. Inconsistent assignments
contribute zero. -/
theorem eval (x : Val a) (y : Val b) (f : X → F) :
    ∑ z : S.State, (∏ v, S.backdrop.base.station v x y z) * f (S.backdrop.param x y z) =
      ∑ a, f (S.param x y a) := by
  let g (z : S.State) := (∏ v, S.base.station v x y z) * f (S.param x y (S.decode z))
  have hinj : Function.Injective S.encode := Function.LeftInverse.injective (g := S.decode) (fun _ => rfl)
  have hgood (a : Y.State) : g (S.encode a) = f (S.param x y a) := by
    have h (v : S.Vertex) : S.checks v (S.encode a) := fun _ _ _ _ _ => rfl
    change (∏ v, if S.checks v (S.encode a) then (1 : F) else 0) * f (S.param x y a) = _
    simp [h]
  trans ∑ z ∈ univ.image S.encode, g z
  · symm
    refine sum_subset (subset_univ _) fun z _ hz => ?_
    have he : (∏ v, S.base.station v x y z) = 0 := by
      by_contra hp
      exact hz (mem_image.mpr ⟨S.decode z, mem_univ _, S.valid x y z hp⟩)
    exact mul_eq_zero_of_left he _
  · rw [sum_image hinj.injOn]
    exact sum_congr rfl (fun z _ => hgood z)

end Sharing
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end

/-!
# Routing on the common host

Independent blocks have distinct physical vertices but use the same
host slots. Every subbundle follows a source branch, crosses to the
peer's leaf, and follows the target branch backwards.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open Finset Classical

variable {F V I : Type} {a b : Wire} {d : ℕ} {G : Bundled F a b}

private theorem Routes.connect {Y : Type} (R : Routes G Y) (rel : G.V ⊕ Y → G.V ⊕ Y → Prop)
    (pos : ∀ e, 0 < R.length e)
    (first : ∀ e j, j.val = 0 → rel (.inl (G.src e)) (.inr (R.via e j)))
    (last : ∀ e j, j.val + 1 = R.length e → rel (.inr (R.via e j)) (.inl (G.dst e)))
    (mid : ∀ e j k, j.val + 1 = k.val → rel (.inr (R.via e j)) (.inr (R.via e k))) :
    ∀ h, rel (R.src h) (R.dst h) := by
  rintro ⟨e, i⟩
  have h := pos e
  have hs (j : Fin (R.length e + 1)) :
      (j.val = 0 ∧ R.src ⟨e, j⟩ = .inl (G.src e)) ∨
      ∃ k, k.val + 1 = j.val ∧ R.src ⟨e, j⟩ = .inr (R.via e k) := by
    induction j using Fin.cases with
    | zero => exact .inl ⟨rfl, rfl⟩
    | succ k => exact .inr ⟨k, rfl, rfl⟩
  have ht (j : Fin (R.length e + 1)) :
      (j.val = R.length e ∧ R.dst ⟨e, j⟩ = .inl (G.dst e)) ∨
      ∃ k, k.val = j.val ∧ R.dst ⟨e, j⟩ = .inr (R.via e k) := by
    induction j using Fin.lastCases with
    | last => exact .inl ⟨rfl, by simp [dst]⟩
    | cast k => exact .inr ⟨k, rfl, by simp [dst]⟩
  rcases hs i with ⟨hs, es⟩ | ⟨j, hs, es⟩ <;> rcases ht i with ⟨ht, et⟩ | ⟨k, ht, et⟩
  · omega
  · rw [es, et]; exact first e k (by omega)
  · rw [es, et]; exact last e j (by omega)
  · rw [es, et]; exact mid e j k (by omega)

/-- One station per host slot per independent block. -/
structure Fanout (G : Bundled F a b) (T : Trie V d) (I : Type) where
  site : G.V → V × I
  one : Function.Injective site
  near : ∀ e, (site (G.dst e)).1 ∈ T.near (site (G.src e)).1
  group : ∀ e, (site (G.src e)).2 = (site (G.dst e)).2

namespace Fanout
variable {T : Trie V d} (H : Fanout G T I)

def place : Node G.V d → Node V d × I
  | .inl v => (.inl (H.site v).1, (H.site v).2)
  | .inr u => (.inr ((H.site u.1).1, u.2), (H.site u.1).2)

theorem injective : Function.Injective H.place := by
  rintro (v|⟨v, i⟩) (w|⟨w, j⟩) h
  all_goals simp only [place, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
    false_and] at h
  · rw [H.one (Prod.ext h.1 h.2)]
  · rw [H.one (Prod.ext h.1.1 h.2), h.1.2]

def side (v w : G.V) (i : Fin (d + 1)) : Relay G.V d :=
  (v, i, T.address (H.site v).1 (H.site w).1 i)

abbrev route : Routes G (Relay G.V d) where
  length _ := (d + 1) + (d + 1)
  via e := Fin.append (H.side (G.src e) (G.dst e))
    (fun j => H.side (G.dst e) (G.src e) j.rev)

def linked (x y : Node G.V d) : Prop :=
  (H.place x).2 = (H.place y).2 ∧ (H.place y).1 ∈ T.adj (H.place x).1

private theorem reverse {x y} (h : H.linked x y) : H.linked y x :=
  ⟨h.1.symm, T.adj_symm h.2⟩

private theorem arm (v w : G.V) : H.linked (.inl v) (.inr (H.side v w 0)) :=
  ⟨rfl, T.root _ _⟩

private theorem next (v w : G.V) (j k : Fin (d + 1)) (hj : j.val + 1 = k.val) :
    H.linked (.inr (H.side v w j)) (.inr (H.side v w k)) := by
  let s : Fin d := ⟨j.val, by have := k.isLt; omega⟩
  have h₁ : j = s.castSucc := Fin.ext rfl
  have h₂ : k = s.succ := Fin.ext hj.symm
  rw [h₁, h₂]
  exact ⟨rfl, T.edge _ _ _⟩

private theorem bridge (e : G.E) :
    H.linked (.inr (H.side (G.src e) (G.dst e) (Fin.last d)))
      (.inr (H.side (G.dst e) (G.src e) (Fin.last d))) :=
  ⟨H.group e, T.join (H.near e)⟩

theorem edges (i : H.route.Hop) : H.linked (H.route.src i) (H.route.dst i) := by
  apply Routes.connect H.route H.linked (fun _ => by change 0 < (d + 1) + (d + 1); omega)
  · intro e j hj
    have he : j = Fin.castAdd (d + 1) (0 : Fin (d + 1)) := Fin.ext hj
    simp only [he, Fin.append_left]
    exact H.arm _ _
  · intro e j hj
    have he : j = Fin.natAdd (d + 1) (Fin.last d) := Fin.ext (by
      change j.val + 1 = (d + 1) + (d + 1) at hj
      change j.val = d + 1 + d
      omega)
    simp only [he, Fin.append_right, Fin.rev_last]
    exact H.reverse (H.arm _ _)
  · intro e j k hjk
    change Fin ((d + 1) + (d + 1)) at j k
    induction j using Fin.addCases <;> induction k using Fin.addCases
    all_goals simp only [Fin.append_left, Fin.append_right]
    · exact H.next _ _ _ _ hjk
    · rename_i j k
      change j.val + 1 = d + 1 + k.val at hjk
      have hj : j = Fin.last d := Fin.ext (by have := j.isLt; simp; omega)
      have hk : k = 0 := Fin.ext (by change k.val = 0; have := j.isLt; omega)
      rw [hj, hk, Fin.rev_zero]
      exact H.bridge e
    · rename_i j k
      change d + 1 + j.val + 1 = k.val at hjk
      have := k.isLt
      omega
    · rename_i j k
      apply H.reverse
      apply H.next
      change d + 1 + j.val + 1 = d + 1 + k.val at hjk
      change (d + 1 - (k.val + 1)) + 1 = d + 1 - (j.val + 1)
      have := k.isLt
      omega

end Fanout
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
end
