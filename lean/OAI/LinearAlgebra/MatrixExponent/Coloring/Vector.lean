import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Control.Address

/-!
# Circuits on encoded data

A format is a bijection between data and assignments to named bits.
Cost includes the lengths of both boundaries when accounting for
near-linear computation with polynomial overhead in the address width.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

open Install
abbrev B (h : ℕ) := Fin (2 ^ h)

structure Format where
  obj : Type
  pins : Type
  [finite : Fintype pins]
  code : obj ≃ (pins → Bool)

attribute [instance] Format.finite

namespace Format

abbrev width (A : Format) := Fintype.card A.pins

abbrev wire (a : Wire) : Format := ⟨Val a, slots a, bits a⟩

abbrev bit := wire .bit
abbrev addr (h : ℕ) : Format := ⟨B h, slots (word h), (Control.decode h).symm⟩

abbrev pair (A D : Format) : Format :=
  ⟨A.obj × D.obj, A.pins ⊕ D.pins,
    (A.code.prodCongr D.code).trans (Equiv.sumPiEquivProdPi (fun _ => Bool)).symm⟩

abbrev vec (h : ℕ) (A : Format) : Format :=
  ⟨B h → A.obj, B h × A.pins,
    (Equiv.piCongrRight (fun _ => A.code)).trans (Equiv.curry _ _ _).symm⟩

@[simp] theorem width_bit : bit.width = 1 := rfl
@[simp] theorem width_addr (h : ℕ) : (addr h).width = h := by simp [width]
@[simp] theorem width_pair (A D : Format) : (pair A D).width = A.width + D.width :=
  Fintype.card_sum
@[simp] theorem width_vec (h : ℕ) (A : Format) : (vec h A).width = 2 ^ h * A.width := by
  simp [width, Fintype.card_prod]

end Format

abbrev Perm (h : ℕ) := Format.vec h (.addr h)

def Circuit (F : Type) [Field F] (A D : Format) (f : A.obj → D.obj) (m : ℕ) : Prop :=
  BNet F (D.code ∘ f ∘ A.code.symm) m

def Cheap (F : Type) [Field F] (h k : ℕ) (A D : Format) (f : A.obj → D.obj) (c : ℕ) : Prop :=
  ∃ m, Circuit F A D f m ∧ A.width + D.width + m ≤ 2 ^ h * (100 + k) ^ c

namespace Circuit

variable {F : Type} [Field F] {A D E G : Format} {m n h : ℕ} {f : A.obj → D.obj}

theorem mono (hf : Circuit F A D f m) (h : m ≤ n) : Circuit F A D f n :=
  BNet.mono hf h

theorem comp {g : D.obj → E.obj} (hf : Circuit F A D f m) (hg : Circuit F D E g n) :
    Circuit F A E (g ∘ f) (m + n) := by
  simpa only [Circuit, Function.comp_def, Equiv.symm_apply_apply] using BNet.comp hf hg

theorem pair {g : A.obj → E.obj} (hf : Circuit F A D f m) (hg : Circuit F A E g n) :
    Circuit F A (.pair D E) (fun x => (f x, g x)) (5 * A.width + m + n) :=
  BNet.pair hf hg

theorem par {g : E.obj → G.obj} (hf : Circuit F A D f m) (hg : Circuit F E G g n) :
    Circuit F (.pair A E) (.pair D G) (Prod.map f g) (m + n) :=
  BNet.parallel hf hg

theorem map (f : B h → A.obj → D.obj) (hf : ∀ i, Circuit F A D (f i) m) :
    Circuit F (.vec h A) (.vec h D) (fun x i => f i (x i)) (2 ^ h * m) :=
  BNet.family h _ hf

theorem id (F : Type) [Field F] (A : Format) : Circuit F A A _root_.id A.width := by
  simp only [Circuit, Function.comp_def, id_eq, Equiv.apply_symm_apply]
  exact BNet.id F A.pins

/-- A structural projection can reuse bits arbitrarily. -/
theorem project (e : D.pins → A.pins) (he : ∀ x i, D.code (f x) i = A.code x (e i)) :
    Circuit F A D f (A.width + 2 * D.width) := by
  intro a b i j
  unfold Format.width
  rw [Fintype.card_congr i, Fintype.card_congr j, card_slots, card_slots]
  convert Install.project_net F (i ∘ e ∘ j.symm) using 1
  funext x
  apply (bits b).injective
  funext k
  simp only [bits_project, Function.comp_apply, Equiv.apply_symm_apply, he]

theorem of_dnet {a b : Wire} (i : A.pins ≃ slots a) (j : D.pins ≃ slots b)
    {g : Val a → Val b} (hg : DNet F a b g m)
    (he : ∀ x, bits b (g x) ∘ j = D.code (f (A.code.symm (bits a x ∘ i)))) :
    Circuit F A D f m := by
  apply BNet.of_layout i j
  convert hg using 1
  funext x
  apply (bits b).injective
  rw [Equiv.apply_symm_apply]
  funext k
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using (congrFun (he x) (j.symm k)).symm

end Circuit
end OAI.LinearAlgebra.MatrixExponent.Coloring
