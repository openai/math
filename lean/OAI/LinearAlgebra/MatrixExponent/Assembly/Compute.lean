import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import Mathlib.Data.Fintype.EquivFin
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import Mathlib.Data.Fintype.Option
import OAI.LinearAlgebra.MatrixExponent.Control.BucketNet
import OAI.LinearAlgebra.MatrixExponent.Radix.WideTag
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array

/-! # Navigation on a symmetric host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

/-- Unused entries point to their own host. Flags distinguish padding
from actual self contacts. -/
structure Directory {V : Type} (N : V → Finset V) (m : ℕ) (d : ℕ := 3) where
  host : V ↪ B m
  nav : B m → B d → B m
  index : V → V → B d
  nav_link : ∀ v u, u ∈ N v → nav (host v) (index v u) = host u
  reciprocal : ∀ i j, nav i j ≠ i → ∃! k, nav (nav i j) k = i
  closed : ∀ v j, nav (host v) j ∈ Set.range host
  flags : B m → B d → Bool
  marks : ∀ v u, u ∈ N v ↔ ∃ k, nav (host v) k = host u ∧ flags (host v) k = true

def Directory.numbered {V : Type} (N : V → Finset V) {m d : ℕ}
    (hs : ∀ v u, u ∈ N v → v ∈ N u) (host : V ↪ B m)
    (link : ∀ v, ↥(N v) ↪ B d) : Directory N m d := by
  let index (v u : V) := if h : u ∈ N v then link v ⟨u, h⟩ else 0
  let edge i j u := ∃ v, host v = i ∧ u ∈ N v ∧ index v u = j
  let nav i j := if h : ∃ u, edge i j u then host h.choose else i
  have found {i j} (h : ∃ u, edge i j u) : ∃ u, edge i j u ∧ nav i j = host u :=
    ⟨h.choose, h.choose_spec, dite_eq_left h⟩
  have moving {i j} (h : nav i j ≠ i) : ∃ u, edge i j u ∧ nav i j = host u :=
    found (by by_contra hn; exact h (dite_eq_right hn))
  have follow v u (h : u ∈ N v) : nav (host v) (index v u) = host u := by
    obtain ⟨w, ⟨v', hv, hw, he⟩, hn⟩ := found (i := host v) (j := index v u) ⟨u, v, rfl, h, rfl⟩
    have := host.injective hv
    subst v'
    simp only [index, dite_eq_left hw, dite_eq_left h] at he
    have : w = u := congrArg Subtype.val ((link v).injective he)
    rwa [this] at hn
  refine ⟨host, nav, index, follow, ?_, ?_, fun i j => decide (∃ u, edge i j u), ?_⟩
  · intro i j h
    obtain ⟨u, ⟨v, hv, hu, _⟩, hn⟩ := moving h
    refine ⟨index u v, by rw [hn]; exact (follow _ _ (hs _ _ hu)).trans hv, ?_⟩
    intro k hk
    obtain ⟨w, ⟨z, hz, _, he⟩, hw⟩ := moving (show nav (nav i j) k ≠ nav i j by rw [hk]; exact h.symm)
    rw [host.injective (hz.trans hn), host.injective (hw.symm.trans (hk.trans hv.symm))] at he
    exact he.symm
  · intro v j
    by_cases h : nav (host v) j = host v
    · exact ⟨v, h.symm⟩
    obtain ⟨u, _, hu⟩ := moving h
    exact ⟨u, hu.symm⟩
  · intro v u
    constructor
    · intro h
      exact ⟨index v u, follow _ _ h, decide_eq_true ⟨u, v, rfl, h, rfl⟩⟩
    · rintro ⟨j, hn, hf⟩
      obtain ⟨w, ⟨z, hz, hw, _⟩, he⟩ := found (of_decide_eq_true hf)
      rwa [host.injective hz, host.injective (he.symm.trans hn)] at hw

theorem Directory.numbered_moving {V : Type} (N : V → Finset V) {m d : ℕ}
    (hs : ∀ v u, u ∈ N v → v ∈ N u) (host : V ↪ B m) (link : ∀ v, ↥(N v) ↪ B d) :
    let A := Directory.numbered N hs host link
    ∀ i j, A.nav i j ≠ i → A.flags i j = true := by
  intro A i j h
  dsimp only [A, Directory.numbered] at h ⊢
  apply decide_eq_true
  exact Classical.byContradiction (fun hn => h (dite_eq_right hn))

theorem directory {V : Type} [Fintype V] (N : V → Finset V) (m : ℕ)
    (hs : ∀ v u, u ∈ N v → v ∈ N u) (hd : ∀ v, (N v).card ≤ 8)
    (hm : Fintype.card V ≤ 2 ^ m) : Nonempty (Directory N m) := by
  obtain ⟨host⟩ : Nonempty (V ↪ B m) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hm)
  let link (v : V) : ↥(N v) ↪ B 3 :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hd v))
  exact ⟨Directory.numbered N hs host link⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Parallel networks on dependent families

Inputs and outputs carry disjoint named bit sets for each component.
Parallel realization uses the sum of the component budgets.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring
open scoped Classical

variable {I : Type} [Fintype I]

abbrev Fmt.pi (A : I → Format) : Format :=
  ⟨∀ i, (A i).obj, Σ i, (A i).pins,
    (Equiv.piCongrRight (fun i => (A i).code)).trans
      (Equiv.piCurry (fun i (_ : (A i).pins) => Bool)).symm⟩

@[simp] theorem Fmt.width_pi (A : I → Format) :
    (Fmt.pi A).width = ∑ i, (A i).width := Fintype.card_sigma

variable {F : Type} [Field F] {u : ℕ} {L : Set (Table F)}

theorem Kernel.renamePins {A B C D : Format} {f : A.obj → B.obj → F}
    {g : C.obj → D.obj → F} {n : ℕ} (h : Kernel F u L A B f n)
    (e : A.pins ≃ C.pins) (d : B.pins ≃ D.pins)
    (hg : ∀ x y, f (A.code.symm (x ∘ e)) (B.code.symm (y ∘ d)) =
      g (C.code.symm x) (D.code.symm y)) : Kernel F u L C D g n := by
  intro a b i j
  have k := h a b (e.trans i) (d.trans j)
  simp only [view_apply, Equiv.coe_trans, ← Function.comp_assoc, hg] at k
  exact k

private def optionPins (A : Option I → Format) :
    (A none).pins ⊕ (Σ i, (A (some i)).pins) ≃ Σ i, (A i).pins where
  toFun
    | .inl x => ⟨none, x⟩
    | .inr ⟨i, x⟩ => ⟨some i, x⟩
  invFun
    | ⟨none, x⟩ => .inl x
    | ⟨some i, x⟩ => .inr ⟨i, x⟩
  left_inv := by rintro (x | ⟨i, x⟩) <;> rfl
  right_inv := by rintro ⟨_ | i, x⟩ <;> rfl

theorem Kernel.family {A B : I → Format} {f : (i : I) → (A i).obj → (B i).obj → F}
    {m : I → ℕ} (h : ∀ i, Kernel F u L (A i) (B i) (f i) (m i)) :
    Kernel F u L (Fmt.pi A) (Fmt.pi B) (fun x y => ∏ i, f i (x i) (y i)) (∑ i, m i) := by
  refine Fintype.induction_empty_option (P := fun I => ∀ (A B : I → Format)
    (f : (i : I) → (A i).obj → (B i).obj → F) (m : I → ℕ),
    (∀ i, Kernel F u L (A i) (B i) (f i) (m i)) →
      Kernel F u L (Fmt.pi A) (Fmt.pi B) (fun x y => ∏ i, f i (x i) (y i)) (∑ i, m i))
    ?_ ?_ ?_ I A B f m h
  · intro J I _ e ih A B f m h
    let _ := Fintype.ofEquiv I e.symm
    have k := ih (fun j => A (e j)) (fun j => B (e j)) (fun j => f (e j))
      (fun j => m (e j)) (fun j => h (e j))
    rw [e.sum_comp] at k
    refine k.renamePins (e.sigmaCongrLeft (β := fun i => (A i).pins))
      (e.sigmaCongrLeft (β := fun i => (B i).pins)) ?_
    intro x y
    exact e.prod_comp (fun i => f i ((Fmt.pi A).code.symm x i) ((Fmt.pi B).code.symm y i))
  · intro A B f m h
    let emp (C : PEmpty → Format) : (Fmt.pi C).pins ≃ slots .unit :=
      ⟨fun x => x.1.elim, Empty.elim, fun x => x.1.elim, fun x => Empty.elim x⟩
    refine Kernel.of_layout (emp A) (emp B) ⟨0, Nat.zero_le _, ?_⟩
    simpa using (Wide.empty (K := F) (u := u) (labels := L))
  · intro J _ ih A B f m h
    have k := ih (fun j => A (some j)) (fun j => B (some j)) (fun j => f (some j))
      (fun j => m (some j)) (fun j => h (some j))
    rw [Fintype.sum_option]
    refine ((h none).par k).renamePins (optionPins A) (optionPins B) ?_
    intro x y
    rw [Fintype.prod_option]
    rfl

theorem Map.family {A B : I → Format} {f : (i : I) → (A i).obj → (B i).obj}
    {m : I → ℕ} (h : ∀ i, Map F u L (A i) (B i) (f i) (m i)) :
    Map F u L (Fmt.pi A) (Fmt.pi B) (fun x i => f i (x i)) (∑ i, m i) := by
  unfold Map at h ⊢
  convert Kernel.family h using 1
  funext x y
  by_cases he : (fun i => f i (x i)) = y
  · subst y
    simp
  · rw [ite_eq_right he]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp he
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Weighted deterministic maps on a common set of labels

Weights can encode rejection as well as field scalars withdrawn
during intermediate contractions. They multiply under composition.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical
variable {F : Type} [Field F] {A B C D : Format} {u m n : ℕ} {L : Set (Table F)}

def Action (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (A B : Format) (f : A.obj → B.obj) (w : A.obj → F) (m : ℕ) : Prop :=
  Kernel F u L A B (fun x y => if f x = y then w x else 0) m

def lookup (F : Type) (A B : Format) (f : A.obj → B.obj → F) : Table F :=
  ⟨word A.width, word B.width, fun x y => f (view A (names A) x) (view B (names B) y)⟩

theorem Kernel.lookup {f : A.obj → B.obj → F} (hu : A.width + B.width ≤ u)
    (hl : Assembly.lookup F A B f ∈ L) : Kernel F u L A B f (1 + A.width + B.width) := by
  apply Kernel.of_layout (names A) (names B)
  exact ⟨_, by simp [add_assoc], .table _ _ _ (by simpa using hu) (.inr hl)⟩

theorem Kernel.vec {t : ℕ} (f : Coloring.B t → A.obj → B.obj → F)
    (h : ∀ i, Kernel F u L A B (f i) m) :
    Kernel F u L (.vec t A) (.vec t B) (fun x y => ∏ i, f i (x i) (y i)) (2 ^ t * m) := by
  have hs := Kernel.family (A := fun _ => A) (B := fun _ => B) h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] at hs
  exact hs.renamePins (Equiv.sigmaEquivProd _ _) (Equiv.sigmaEquivProd _ _) fun _ _ => rfl

namespace Action
variable {f : A.obj → B.obj} {w : A.obj → F}

theorem mono (h : Action F u L A B f w m) (hm : m ≤ n) : Action F u L A B f w n :=
  Kernel.mono h hm

theorem of_map (h : Map F u L A B f m) : Action F u L A B f (fun _ => 1) m := h

theorem comp {g : B.obj → C.obj} {v : B.obj → F}
    (h : Action F u L A B f w m) (k : Action F u L B C g v n) :
    Action F u L A C (g ∘ f) (fun x => w x * v (f x)) (m + n) := by
  let _ := Fintype.ofFinite B.obj
  have hh := Kernel.comp h k
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hh
  simpa only [Action, Function.comp_apply, mul_ite, mul_zero] using hh

theorem par {g : C.obj → D.obj} {v : C.obj → F} (h : Action F u L A B f w m)
    (k : Action F u L C D g v n) :
    Action F u L (.pair A C) (.pair B D) (Prod.map f g) (fun x => w x.1 * v x.2) (m + n) := by
  have hh := Kernel.par h k
  simp only [ite_mul, zero_mul] at hh
  simpa only [Action, Prod.ext_iff, Prod.map_fst, Prod.map_snd, ite_and, mul_ite, mul_zero] using hh

theorem pre {g : C.obj → A.obj} (h : Action F u L A B f w m) (k : Map F u L C A g n) :
    Action F u L C B (f ∘ g) (w ∘ g) (n + m) := k.then_kernel h

theorem post {g : B.obj → C.obj} (h : Action F u L A B f w m) (k : Map F u L B C g n) :
    Action F u L A C (g ∘ f) w (m + n) := by
  simpa only [mul_one] using h.comp (of_map k)

theorem vec {t : ℕ} (f : Coloring.B t → A.obj → B.obj) (w : Coloring.B t → A.obj → F)
    (h : ∀ i, Action F u L A B (f i) (w i) m) :
    Action F u L (.vec t A) (.vec t B) (fun x i => f i (x i)) (fun x => ∏ i, w i (x i)) (2 ^ t * m) := by
  have hk := Kernel.vec _ h
  unfold Action
  convert hk using 1
  funext x y
  by_cases he : (fun i => f i (x i)) = y
  · subst y
    simp
  · rw [ite_eq_right he]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp he
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

end Action

theorem Map.vec {t : ℕ} (f : Coloring.B t → A.obj → B.obj) (h : ∀ i, Map F u L A B (f i) m) :
    Map F u L (.vec t A) (.vec t B) (fun x i => f i (x i)) (2 ^ t * m) := by
  have he := Action.vec f _ (fun i => Action.of_map (h i))
  simp only [Finset.prod_const_one] at he
  exact he

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Partial computation on encoded states

Only reachable records need to be checked. Auxiliary data may be
kept by charging its actual width. Zero weight rejects a branch.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} [Field F] {u m n : ℕ} {L : Set (Table F)} {I J : Type*}
  {A B C D : Format}

def Computes (F : Type) [Field F] (u : ℕ) (L : Set (Table F))
    (A B : Format) (x : I → A.obj) (y : I → B.obj) (w : I → F) (m : ℕ) : Prop :=
  ∃ f, Kernel F u L A B f m ∧ ∀ i v, f (x i) v = if y i = v then w i else 0

namespace Computes

variable {x : I → A.obj} {y : I → B.obj} {z : I → C.obj}
  {w v : I → F}

theorem restrict (h : Computes F u L A B x y w m) (j : J → I) :
    Computes F u L A B (x ∘ j) (y ∘ j) (w ∘ j) m :=
  let ⟨f, k, he⟩ := h
  ⟨f, k, fun i => he (j i)⟩

theorem mono (h : Computes F u L A B x y w m) (hm : m ≤ n) :
    Computes F u L A B x y w n :=
  let ⟨f, k, he⟩ := h
  ⟨f, k.mono hm, he⟩

theorem comp (h : Computes F u L A B x y w m) (k : Computes F u L B C y z v n) :
    Computes F u L A C x z (fun i => w i * v i) (m + n) := by
  let _ := Fintype.ofFinite B.obj
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨g, hg, hg'⟩ := k
  refine ⟨_, hf.comp hg, fun i t => ?_⟩
  simp only [he, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    hg', mul_ite, mul_zero]

theorem par {q : I → D.obj} (h : Computes F u L A B x y w m) (k : Computes F u L C D z q v n) :
    Computes F u L (.pair A C) (.pair B D) (fun i => (x i, z i)) (fun i => (y i, q i))
      (fun i => w i * v i) (m + n) := by
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨g, hg, hg'⟩ := k
  refine ⟨_, hf.par hg, fun i t => ?_⟩
  simp only [he, hg', ite_mul, zero_mul]
  simp only [Prod.ext_iff, ite_and, mul_ite, mul_zero]

theorem of_action {f : A.obj → B.obj} {p : A.obj → F} (h : Action F u L A B f p m)
    (hf : ∀ i, f (x i) = y i) (hp : ∀ i, p (x i) = w i) : Computes F u L A B x y w m :=
  ⟨_, h, fun i t => by simp only [hf, hp]⟩

theorem of_map {f : A.obj → B.obj} (h : Map F u L A B f m)
    (hf : ∀ i, f (x i) = y i) : Computes F u L A B x y (fun _ => 1) m :=
  of_action (Action.of_map h) hf (fun _ => rfl)

theorem pair (hu : 3 ≤ u) (h : Computes F u L A B x y w m) (k : Computes F u L A C x z v n) :
    Computes F u L A (.pair B C) x (fun i => (y i, z i)) (fun i => w i * v i)
      (20 * A.width + (m + n)) := by
  have c : Circuit F A (.pair A A) (fun a => (a, a)) (5 * A.width) := by
    refine (Circuit.project (D := .pair A A) (Sum.elim id id) ?_).mono ?_
    · rintro a (i|i) <;> rfl
    · simp only [Format.width_pair]; omega
  have cp := of_map (L := L) (x := x) (Map.circuit hu c) (fun _ => rfl)
  have hh := cp.comp (h.par k)
  simpa only [one_mul, ← mul_assoc, show 4 * 5 = 20 by decide] using hh

end Computes
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# A controlled permutation of wide records

The tag order on the binary tree may differ from the numerical
order of addresses. A fixed permutation of the source slots
reconciles the two orders without any gates.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring Install
open scoped Classical

variable {F : Type} [Field F] {j v m : ℕ}

theorem labeled_perm {A D : Type} (name : B j ≃ A) (a : B j → A)
    (x y : B j → D) :
    (List.ofFn (fun i => (a i, y i))).Perm (List.ofFn (fun i => (name i, x i))) ↔
      Function.Bijective a ∧ ∀ i, y i = x (name.symm (a i)) := by
  constructor
  · intro h
    have he := h.map Prod.fst
    simp only [List.map_ofFn, Function.comp_def] at he
    have hi := List.nodup_ofFn.mp (he.symm.nodup (List.nodup_ofFn.mpr name.injective))
    have hh : Function.Surjective a := by
      intro k
      exact List.mem_ofFn.mp (he.symm.subset (List.mem_ofFn.mpr ⟨name.symm k, name.apply_symm_apply _⟩))
    refine ⟨⟨hi, hh⟩, fun i => ?_⟩
    obtain ⟨l, hl⟩ := List.mem_ofFn.mp (h.subset (List.mem_ofFn.mpr ⟨i, rfl⟩))
    rw [← (Prod.mk.inj hl).1, name.symm_apply_apply]
    exact (Prod.mk.inj hl).2.symm
  · rintro ⟨ha, h⟩
    let e := (Equiv.ofBijective a ha).trans name.symm
    have he : (fun i => (a i, y i)) = (fun i => (name i, x i)) ∘ e := by
      funext i
      exact Prod.ext (name.apply_symm_apply _).symm (h i)
    rw [he]
    exact Equiv.Perm.ofFn_comp_perm _ _

abbrev PermBus (j v : ℕ) :=
  (B j × slots (word v)) ⊕ (B j × (slots (word j) ⊕ slots (word v)))

def PermBus.address (z : PermBus j v → Bool) (i : B j) :=
  Control.decode j (fun p => z (.inr (i, .inl p)))

def PermBus.valid (z : PermBus j v → Bool) : Prop :=
  Function.Bijective (address z) ∧ ∀ i p, z (.inr (i, .inr p)) = z (.inl (address z i, p))

theorem permutation_weight (ht : Radix.Tag F j v m) :
    Weight F (fun z : PermBus j v → Bool => if PermBus.valid z then 1 else 0) m := by
  obtain ⟨A, hA⟩ := Layout.exists_tree (word j) j
  obtain ⟨B, hB⟩ := Layout.exists_tree (word v) j
  obtain ⟨C, hC⟩ := Layout.exists_tree (Tagged.row j (word v)) j
  let a := A.read (Tagged.indices j)
  have hi : Function.Injective a := List.nodup_ofFn.mp (by rw [hA]; exact Tagged.indices_nodup _)
  let π := Equiv.ofBijective (Control.index j ∘ a)
    (Finite.injective_iff_bijective.mp ((Control.index j).injective.comp hi))
  let e := ((π.symm.prodCongr (.refl _)).trans B.positions).sumCongr C.positions
  apply Weight.of_layout (a := Tagged.inputs j (word v)) e
  refine ⟨m, le_rfl, ?_⟩
  unfold Radix.Tag at ht
  convert ht using 1
  funext ⟨x, y⟩ _
  let z := bits (Tagged.inputs j (word v)) (x, y) ∘ e
  let n := π.trans (Control.index j).symm
  let s := fun i => (C.read y i).1
  let t := fun i => (C.read y i).2
  have hn : ⇑n = a := by funext i; exact (Control.index j).symm_apply_apply _
  have hL : flatten j (Tagged.label j x) = List.ofFn (fun i => (n i, B.read x i)) := by
    rw [Tagged.label, Control.flatten_zip, ← hB, ← hA, Control.zip_ofFn, hn]
  have hR : flatten j y = List.ofFn (fun i => (s i, t i)) := (hC y).symm
  have he (i : Coloring.B j) : PermBus.address z i = Control.index j (s i) := rfl
  have hb : Function.Bijective (PermBus.address z) ↔ Function.Bijective s := by
    constructor
    · intro h
      have h' := (Control.index j).symm.bijective.comp h
      simpa only [Function.comp_def, he, Equiv.symm_apply_apply] using h'
    · exact fun h => (Control.index j).bijective.comp h
  have hy (i : Coloring.B j) : (∀ p, z (.inr (i, .inr p)) = z (.inl (PermBus.address z i, p))) ↔
      t i = B.read x (n.symm (s i)) := by
    change _ ↔ (bits (word v)).symm _ = (bits (word v)).symm _
    rw [(bits (word v)).symm.injective.eq_iff, funext_iff]
    rfl
  have hv : PermBus.valid z ↔ (flatten j y).Perm (flatten j (Tagged.label j x)) := by
    rw [hL, hR, labeled_perm, PermBus.valid, hb]
    simp only [hy]
  change (if PermBus.valid z then (1 : F) else 0) = Tagged.tag F j (word v) (x, y) ()
  simp only [Tagged.tag, Tagged.permuted, hv]

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Tagged exchange on a vector of records with an arbitrary bit format -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly

open Coloring Install
open scoped Classical

variable {F : Type} [Field F] {j v m u : ℕ} {L : Set (Table F)} (A : Format)

abbrev exchangeIn (j : ℕ) := (Perm j).pair (.vec j A)
abbrev exchangeOut (j : ℕ) := Format.vec j A

def exchange (F : Type) [Field F] (x : (exchangeIn A j).obj) (y : (exchangeOut A j).obj) : F :=
  if Function.Bijective x.1 ∧ y = x.2 ∘ x.1 then 1 else 0

def exchangeCheck (F : Type) [Field F] (z : (exchangeIn A j).pins ⊕ (exchangeOut A j).pins → Bool) :=
  exchange A F ((exchangeIn A j).code.symm (z ∘ Sum.inl)) ((exchangeOut A j).code.symm (z ∘ Sum.inr))

private def namesIn (e : A.pins ↪ slots (word v)) :
    (exchangeIn A j).pins ⊕ (exchangeOut A j).pins ↪ PermBus j v :=
  ((Equiv.sumComm _ _).sumCongr (.refl _)).toEmbedding.trans
    ((Equiv.sumAssoc _ _ _).toEmbedding.trans
      (((Function.Embedding.refl _).prodMap e).sumMap
        ((Equiv.prodSumDistrib _ _ _).symm.toEmbedding.trans
          ((Function.Embedding.refl _).prodMap ((Function.Embedding.refl _).sumMap e)))))

private theorem pad_weight {I T : Type} [Fintype I] [Fintype T] (e : I ↪ T)
    {f : (T → Bool) → F} (h : Weight F f m) :
    Weight F (fun x => f (Function.extend e x (fun _ => false)))
      (Fintype.card I + 34 * Fintype.card T + m) := by
  have hd : Depends (fun x => Function.extend e x (fun _ => false)) 1 := by
    intro k
    by_cases hk : k ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hk
      exact ⟨{a}, by simp, fun x y h => by simpa [e.injective.extend_apply] using h a (by simp)⟩
    · exact ⟨∅, by simp, fun x y _ => by simp only [Function.extend_apply' _ _ _ hk]⟩
  exact (hd.bnet F).weight h

theorem exchange_weight (ht : Radix.Tag F j v m) (ha : A.width ≤ v) :
    Weight F (exchangeCheck (j := j) A F) (m + 100 * 2 ^ j * (j + v + 1)) := by
  obtain ⟨e⟩ : Nonempty (A.pins ↪ slots (word v)) :=
    Function.Embedding.nonempty_of_card_le (by simpa [Format.width] using ha)
  let k := namesIn (j := j) A e
  have h := pad_weight k (permutation_weight ht)
  have hn : Fintype.card ((exchangeIn A j).pins ⊕ (exchangeOut A j).pins) +
      34 * Fintype.card (PermBus j v) + m ≤ m + 100 * 2 ^ j * (j + v + 1) := by
    have hh := Fintype.card_le_of_embedding k
    change Fintype.card ((exchangeIn A j).pins ⊕ (exchangeOut A j).pins) ≤ Fintype.card (PermBus j v) at hh
    have he : Fintype.card (PermBus j v) = 2 ^ j * v + 2 ^ j * (j + v) := by simp [PermBus]
    rw [he] at hh ⊢
    generalize Fintype.card ((exchangeIn A j).pins ⊕ (exchangeOut A j).pins) = n at hh ⊢
    ring_nf at hh ⊢
    omega
  convert h.mono hn using 1
  funext z
  let t := Function.extend k z (fun _ => false)
  let x := (exchangeIn A j).code.symm (z ∘ Sum.inl)
  let y := (exchangeOut A j).code.symm (z ∘ Sum.inr)
  have h₁ (i : B j) (s : A.pins) : t (.inl (i, e s)) = z (.inl (.inr (i, s))) :=
    k.injective.extend_apply _ _ (.inl (.inr (i, s)))
  have h₂ (i : B j) (s : A.pins) : t (.inr (i, .inr (e s))) = z (.inr (i, s)) :=
    k.injective.extend_apply _ _ (.inr (i, s))
  have haddr : PermBus.address t = x.1 := by
    funext i
    apply congrArg (Control.decode j)
    funext s
    exact k.injective.extend_apply _ _ (.inl (.inl (i, s)))
  have hp (i l : B j) :
      y i = x.2 l ↔ ∀ s, t (.inr (i, .inr s)) = t (.inl (l, s)) := by
    change A.code.symm _ = A.code.symm _ ↔ _
    rw [A.code.symm.injective.eq_iff, funext_iff]
    constructor
    · intro he s
      by_cases hs : s ∈ Set.range e
      · obtain ⟨a, rfl⟩ := hs
        rw [h₁, h₂]
        exact he _
      have he₁ : Sum.inr (i, Sum.inr s) ∉ Set.range k := by
        rintro ⟨(a | a) | a, hh⟩ <;> first
          | solve | cases hh
          | exact hs ⟨a.2, Sum.inr.inj (Prod.mk.inj (Sum.inr.inj hh)).2⟩
      have he₂ : Sum.inl (l, s) ∉ Set.range k := by
        rintro ⟨(a | a) | a, hh⟩ <;> first
          | solve | cases hh
          | exact hs ⟨a.2, (Prod.mk.inj (Sum.inl.inj hh)).2⟩
      simp only [t, Function.extend_apply' _ _ _ he₁, Function.extend_apply' _ _ _ he₂]
    · intro h s
      exact (h₂ i s).symm.trans ((h (e s)).trans (h₁ l s))
  have he : PermBus.valid t ↔ Function.Bijective x.1 ∧ y = x.2 ∘ x.1 := by
    simp only [PermBus.valid, haddr, funext_iff, Function.comp_apply, hp]
  change (if Function.Bijective x.1 ∧ y = x.2 ∘ x.1 then (1 : F) else 0) =
    if PermBus.valid t then 1 else 0
  simp only [he]

theorem permutation_kernel (hu : 3 ≤ u) (ht : Radix.Tag F j v m) (ha : A.width ≤ v) :
    Kernel F u L (exchangeIn A j) (exchangeOut A j) (exchange A F)
      (4 * m + 1000 * 2 ^ j * (j + v + 1)) := by
  have h := Kernel.of_weight hu (Transcript.of_weight (L := L) hu (exchange_weight A ht ha))
  have hh : 4 * (m + 100 * 2 ^ j * (j + v + 1)) + 4 * (exchangeOut A j).width ≤ 4 * m + 1000 * 2 ^ j * (j + v + 1) := by
    rw [Format.width_vec]
    have := Nat.mul_le_mul_left (2 ^ j) ha
    ring_nf at this ⊢
    omega
  simpa [exchangeCheck, Function.comp_def] using h.mono hh

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# A common interface for exchanging wide records

The compression argument uses a trivalent tagged permutation.
The many-list descent can instead spend a sorting table. Both
realizations have the same bit-level correctness condition.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring

def Access (F : Type) [Field F] (u : ℕ) (L : Set (Table F)) (j v n : ℕ) : Prop :=
  ∀ A : Format, A.width ≤ v →
    Kernel F u L (exchangeIn A j) (exchangeOut A j) (exchange A F) (4 * n + 1000 * 2 ^ j * (j + v + 1))

variable {F : Type} [Field F] {u j v n : ℕ} {L : Set (Table F)}

theorem Access.tag (h : 3 ≤ u) (ht : Radix.Tag F j v n) : Access F u L j v n :=
  fun A => permutation_kernel A h ht

theorem Access.widen {u' : ℕ} {L' : Set (Table F)} (h : Access F u L j v n)
    (hu : u ≤ u') (hL : L ⊆ L') : Access F u' L' j v n :=
  fun A ha => (h A ha).widen hu hL

end OAI.LinearAlgebra.MatrixExponent.Assembly
end
