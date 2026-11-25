import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Price
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Ballot
import OAI.LinearAlgebra.MatrixExponent.Sphere.Verifier.Caps
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Shapes
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Weight

/-!
# Choosing physical codes for dictionary addresses

A code is a bijection. Its length equals the logical address width,
so changing codes costs no additional bits. A visible bit is a
constant or one projection, uniformly over a family of inputs.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical

structure Code (n : ℕ) where
  pins : Type
  [finite : Fintype pins]
  write : B n ≃ (pins → Bool)

attribute [instance] Code.finite

variable {m h d n : ℕ}

namespace Code

def format (c : Code n) : Format := ⟨B n, c.pins, c.write⟩
def std (n : ℕ) : Code n := ⟨(Format.addr n).pins, (Format.addr n).code⟩

theorem width (c : Code n) : Fintype.card c.pins = n := by
  have e := Fintype.card_congr c.write
  simp only [B, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool] at e
  exact Nat.pow_right_injective (by decide : 2 ≥ 2) e.symm

def recode (f : Format) (g : B n ≃ f.obj) : Code n := ⟨f.pins, g.trans f.code⟩

def numbered (f : Format) : Code f.width := recode f (Design.number f).symm

theorem number (f : Format) (x : f.obj) :
    (numbered f).write (Design.number f x) = f.code x :=
  congrArg f.code ((Design.number f).symm_apply_apply x)

end Code

abbrev Sites (m h : ℕ) := B m × B h
abbrev Source (Ω : Type*) (m h : ℕ) := Sites m h → Set (Ω → Bool)

variable {Ω : Type*} {src : Source Ω m h} {nav : B m → B d → B m} {a : Ω → Bool}

def Visible (src : Source Ω m h) (nav : B m → B d → B m) (r : ℕ) (p : Sites m h) (a : Ω → Bool) : Prop :=
  (∃ b, a = fun _ => b) ∨ ∃ y, Reach nav r p.1 y ∧ a ∈ src (y, p.2)

private theorem walk_add {x y z : B m} {r s : ℕ} (hx : Reach nav r x y) (hy : Reach nav s y z) :
    Reach nav (s + r) x z := by
  induction r generalizing x with
  | zero => subst y; exact hy
  | succ _ ih =>
    obtain ⟨i, hi, h⟩ := hx
    exact ⟨i, hi, ih h⟩

variable {x y : B m} {j : B h} {r s : ℕ}

theorem Visible.start (ha : a ∈ src (x, j)) : Visible src nav r (x, j) a :=
  .inr ⟨x, Reach.refl .., ha⟩

theorem Visible.move (ha : Visible src nav r (y, j) a) (h : Reach nav s x y) :
    Visible src nav (r + s) (x, j) a := by
  rcases ha with ha|⟨z, hz, ha⟩
  · exact .inl ha
  · exact .inr ⟨z, walk_add h hz, ha⟩

theorem Visible.mono (ha : Visible src nav r (x, j) a) (h : r ≤ s) :
    Visible src nav s (x, j) a := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ha.move (Reach.refl ..)

def Local (src : Source Ω m h) (nav : B m → B d → B m) (r : ℕ) (c : Code n)
    (f : Ω → B m → B h → B n) : Prop :=
  ∀ i j t, Visible src nav r (i, j) (fun w => c.write (f w i j) t)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-!
# Synchronous forwarding of requested bits

Each request receives its own register. Round zero initializes it
locally. At each subsequent tick it either stays or moves through
one host link, without changing blocks or reading another register.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical

variable {m h d r : ℕ} {Ω I : Type*} {nav : B m → B d → B m}

def Reciprocal (nav : B m → B d → B m) := ∀ i j, nav i j ≠ i → ∃ l, nav (nav i j) l = i

theorem Visible.weaken {src src' : Source Ω m h} {p f} (h : Visible src nav r p f)
    (hs : ∀ p, src p ⊆ src' p) : Visible src' nav r p f := by
  rcases h with h|⟨v, h, hv⟩
  · exact .inl h
  · exact .inr ⟨v, h, hs _ hv⟩

private theorem path_of_reach {x y : B m} (h : Reach nav r x y) :
    ∃ p : ℕ → B m, p 0 = x ∧ p r = y ∧
      ∀ t < r, p (t + 1) = p t ∨ ∃ i, nav (p t) i = p (t + 1) := by
  induction r generalizing x with
  | zero => exact ⟨fun _ => x, rfl, h, by simp⟩
  | succ r ih =>
    obtain ⟨z, hz, h⟩ := h
    obtain ⟨p, hp, hf, hs⟩ := ih h
    let f : ℕ → B m := fun n => Nat.casesOn n x p
    refine ⟨f, rfl, hf, ?_⟩
    rintro (_|t) ht
    · change p 0 = x ∨ ∃ i, nav x i = p 0
      rw [hp]; exact hz
    · exact hs t (by omega)

structure Plan (src : Source Ω m h) (nav : B m → B d → B m) (r : ℕ)
    (dest : I → Sites m h) (value : I → Ω → Bool) where
  station : I → ℕ → B m
  start : ∀ i, (∃ b, value i = fun _ => b) ∨ value i ∈ src (station i 0, (dest i).2)
  step : ∀ i t, t < r → station i (t + 1) = station i t ∨ ∃ j, nav (station i t) j = station i (t + 1)
  finish : ∀ i, station i r = (dest i).1

variable {src : Source Ω m h} {dest : I → Sites m h} {value : I → Ω → Bool}

def plan (sym : Reciprocal nav) (hw : ∀ i, Visible src nav r (dest i) (value i)) :
    Plan src nav r dest value := by
  have exists_route (i : I) : ∃ a : ℕ → B m,
      ((∃ b, value i = fun _ => b) ∨ value i ∈ src (a 0, (dest i).2)) ∧
      (∀ t < r, a (t + 1) = a t ∨ ∃ j, nav (a t) j = a (t + 1)) ∧ a r = (dest i).1 := by
    rcases hw i with hg|⟨v, hv, h⟩
    · exact ⟨fun _ => (dest i).1, .inl hg, fun _ _ => .inl rfl, rfl⟩
    obtain ⟨f, hi, hf, hs⟩ := path_of_reach (hv.symm sym)
    exact ⟨f, .inr (hi.symm ▸ h), hs, hf⟩
  choose p hi hs hf using exists_route
  exact ⟨p, hi, hs, hf⟩

namespace Plan
variable (p : Plan src nav r dest value)

/-- A register is initialized once, then copied at every clock tick.
The fixed route determines both the sending and receiving host. -/
def register (a : Ω) (i : I) : ℕ → Bool
  | 0 => value i a
  | k + 1 => register a i k

theorem register_eq (a : Ω) (i : I) (t : ℕ) : register (value:=value) a i t = value i a := by
  induction t with
  | zero => rfl
  | succ _ ih => exact ih

def loc (i : I) (t : ℕ) : Sites m h := (p.station i t, (dest i).2)

theorem reaches (i : I) (t : Fin (r + 1)) : Reach nav r (p.station i t) (dest i).1 := by
  have h (k : ℕ) : Reach nav k (p.station i t) (p.station i (min (t.val + k) r)) := by
    induction k with
    | zero => rw [Nat.add_zero t.val, min_eq_left (Nat.le_of_lt_succ t.isLt)]; rfl
    | succ k ih =>
      apply ih.tail
      by_cases hk : t.val + k < r
      · rw [min_eq_left hk.le, min_eq_left (by omega : t.val + (k + 1) ≤ r), ← Nat.add_assoc]
        exact p.step i _ hk
      · rw [min_eq_right (by omega : r ≤ t.val + k), min_eq_right (by omega : r ≤ t.val + (k + 1))]
        exact .inl rfl
  simpa only [min_eq_right (Nat.le_add_left r t.val), p.finish] using h r

end Plan
end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-! # Counting copies and transmissions in a local schedule -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical

namespace Plan
variable {m h d r : ℕ} {Ω I J : Type*} [Fintype I] [Fintype J]
    {nav : B m → B d → B m} {src : Source Ω m h} {dest : I → Sites m h} {value : I → Ω → Bool}
    (p : Plan src nav r dest value)

/-- Each initialization or copy occupies one slot. We charge stays
including those used for padding the shorter paths. -/
abbrev Event (_ : Plan src nav r dest value) := Fin (r + 1) × I

def site (t : p.Event) := p.loc t.2 t.1

def Sends (t : p.Event) := t.1.val < r ∧ p.loc t.2 (t.1.val + 1) ≠ p.site t

theorem copies : Fintype.card p.Event = (r + 1) * Fintype.card I := by
  change Fintype.card (Fin (r + 1) × I) = _
  rw [Fintype.card_prod, Fintype.card_fin]

theorem transmissions : Fintype.card {t : p.Event // p.Sends t} ≤ r * Fintype.card I := by
  let f (t : {t : p.Event // p.Sends t}) : Fin r × I := (⟨t.val.1, t.property.1⟩, t.val.2)
  have hi : Function.Injective f := by
    intro a b e
    obtain ⟨h, h'⟩ := Prod.mk.inj e
    exact Subtype.ext (Prod.ext (Fin.ext (congrArg (fun x : Fin r => x.val) h)) h')
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_le_of_injective f hi

/-- At most one requested bit of each kind per destination. Charge
all registers visiting a site, even those forwarded elsewhere. -/
theorem congestion (slot : I → J) (inj : Function.Injective (fun i => (dest i, slot i))) (v : Sites m h) :
    Fintype.card {t : p.Event // p.site t = v} ≤ (r + 1) * 2 ^ ((d + 1) * r) * Fintype.card J := by
  let A := {t : p.Event // p.site t = v}
  have reach (t : A) : Reach nav r v.1 (dest t.val.2).1 := by
    have h := p.reaches t.val.2 t.val.1
    have eq : p.station t.val.2 t.val.1 = v.1 := congrArg Prod.fst t.property
    rw [eq] at h
    exact h
  choose idx atIdx using fun t : A => mem.mpr (reach t)
  let f (t : A) := ((t.val.1, idx t), slot t.val.2)
  have hi : Function.Injective f := by
    intro a b e
    obtain ⟨he, hj⟩ := Prod.mk.inj e
    obtain ⟨ht, hs⟩ := Prod.mk.inj he
    have left : (dest a.val.2).1 = (dest b.val.2).1 := by rw [← atIdx a, ← atIdx b, hs]
    have right : (dest a.val.2).2 = (dest b.val.2).2 := by
      have hh := congrArg Prod.snd (a.property.trans b.property.symm)
      exact hh
    exact Subtype.ext (Prod.ext ht (inj (Prod.ext (Prod.ext left right) hj)))
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_le_of_injective f hi

end Plan
end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-! # A window code consists entirely of nearby old bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical
variable {m h d e k : ℕ}

def Code.wave (c : Code e) (d r t k : ℕ) : Code (Fmt.wave d r t (.addr e) (.addr k)).width :=
  Code.recode (Fmt.wave d r t c.format (.addr k)) (Design.number (Fmt.wave d r t (.addr e) (.addr k))).symm

theorem Code.wave_at (c : Code e) (d r t k : ℕ) (x : (Fmt.wave d r t (.addr e) (.addr k)).obj) :
    (c.wave d r t k).write (Design.number _ x) = (Fmt.wave d r t c.format (.addr k)).code x :=
  congrArg (Fmt.wave d r t c.format (.addr k)).code ((Design.number _).symm_apply_apply x)

variable {Ω : Type*} {src : Source Ω m h} {nav : B m → B d → B m}
    {rows : Ω → (Fmt.rows m d h (.addr e)).obj} {sel : Ω → B m → B h → B k}
    (hnav : ∀ a i, (rows a i).1 = nav i)
    {s : ℕ} {c : Code e}

def windows (r t : ℕ) (x : (Fmt.rows m d h (.addr e)).obj) (y : B m → B h → B k) :=
  fun i j => Design.number _ ((Fmt.around r t (show (Fmt.waveIn m d h (.addr e) (.addr k)).obj
    from (x, y)) i).2 j)

include hnav in
theorem Local.wave (hx : Local src nav s c (fun a i => (rows a i).2))
    (hy : Local src nav 0 (Code.std k) sel) (r t : ℕ) :
    Local src nav (s + r + t) (c.wave d r t k) (fun a => windows r t (rows a) (sel a)) := by
  rintro i j ⟨v, l, b⟩
  let x := expand t nav i v
  let y := expand r nav x l
  have hu : Reach nav t i x := mem.mp ⟨v, rfl⟩
  have hv : Reach nav r x y := mem.mp ⟨l, rfl⟩
  have he (a : Ω) : (c.wave d r t k).write (windows r t (rows a) (sel a) i j) (v, l, b) =
      (Format.pair c.format (.addr k)).code ((rows a y).2 j, sel a y j) b := by
    unfold windows
    rw [Code.wave_at]
    change (Format.pair c.format (.addr k)).code _ b = _
    apply congrArg (fun p => (Format.pair c.format (.addr k)).code p b)
    unfold Fmt.around Fmt.expand Fmt.zip y x
    simp only [hnav]
    rfl
  simp_rw [he]
  cases b with
  | inl b => exact ((hx y j b).move hv).move hu
  | inr b => exact (((hy y j b).mono (Nat.zero_le s)).move hv).move hu

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-! # Appending a literal slot number to a window of copied labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical
variable {F K N : Type} {m d h ℓ M r t q D k n u j z : ℕ}
  (U : Print.Printer F K N m d h ℓ M r t q D k n u j z)

def Code.advance (c : Code ℓ) : Code U.labelBits :=
  Code.recode ((c.wave d 1 1 U.digits).format.pair (.addr U.childBits))
    (Match.rowIndex U.window.width U.childBits)

variable [Field F] [Finite K] {Ω : Type*} {src : Source Ω m h} {nav : B m → B d → B m}
    {rows : Ω → U.rows.obj} {sel : Ω → U.selectors.obj} {s : ℕ} {c : Code ℓ}

theorem Local.advance (hnav : ∀ a i, (rows a i).1 = nav i)
    (hx : Local src nav s c (fun a i => (rows a i).2))
    (hy : Local src nav 0 (Code.std U.digits) sel) (status : Ω → (Print.Children.Header m d).obj)
    (i : B (m + U.childBits)) (l : B h) (b : (Code.advance U c).pins) :
    Visible src nav (s + 2) ((U.split i).1, l)
      (fun a => (Code.advance U c).write (((U.advance (rows a) (status a) (sel a)).1 i).2 l) b) := by
  let C := (c.wave d 1 1 U.digits).format.pair (.addr U.childBits)
  have eq (a : Ω) :
      (Code.advance U c).write (((U.advance (rows a) (status a) (sel a)).1 i).2 l) b =
      C.code (windows 1 1 (rows a) (sel a) (U.split i).1 l, (U.split i).2) b :=
    congrArg (fun p => C.code p b) (Print.Children.label_at (U.update (rows a) (status a) (sel a)) i l)
  simp_rw [eq]
  cases b with
  | inl b => exact Local.wave hnav hx hy 1 1 _ l b
  | inr b => exact .inl ⟨_, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-! # Copying dictionary bits through a movement history -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical
variable {Ω : Type*} {e k : ℕ} (a : Design) (c : Code e)

def Code.path (k : ℕ) : (i : ℕ) → Code (a.widthAt e k i)
  | 0 => c
  | i + 1 => (path k i).wave a.d a.U (a.U + 1) k

theorem path_nav (r : (a.port e).obj) (i : ℕ) (x : Fin i → (a.selectors k).obj) (j : B a.m) :
    (a.path r i x j).1 = (r j).1 := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih (Fin.init x)

variable {a c} {nav : B a.m → B a.d → B a.m} {src : Source Ω a.m a.h}
    {r : Ω → (a.port e).obj} {s : ℕ} (hnav : ∀ w j, (r w j).1 = nav j)

include hnav in
theorem Local.path (hx : Local src nav s c (fun w i => (r w i).2)) (i : ℕ)
    (x : Ω → Fin i → (a.selectors k).obj)
    (hy : ∀ j, Local src nav 0 (Code.std k) (fun w => x w j)) :
    Local src nav (s + i * (2 * a.U + 1)) (Code.path a c k i) (fun w j => (a.path (r w) i (x w) j).2) := by
  induction i with
  | zero =>
    rw [Nat.zero_mul, Nat.add_zero]
    exact hx
  | succ i ih =>
    let z w := a.path (r w) i (Fin.init (x w))
    have vz (w j) : (z w j).1 = nav j := (path_nav ..).trans (hnav w j)
    have hz := ih (fun w => Fin.init (x w)) (fun j => hy j.castSucc)
    have h := Local.wave (rows:=z) vz hz (hy (Fin.last i)) a.U (a.U + 1)
    rw [show s + (i + 1) * (2 * a.U + 1) = s + i * (2 * a.U + 1) + a.U + (a.U + 1) by ring]
    exact h

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-! # Revised labels copy an old address, a printed address and an outline -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical
variable {n m : ℕ}

def Code.pair (a : Code n) (b : Code m) : Code (n + m) :=
  Code.recode (a.format.pair b.format) (Match.rowIndex n m)

theorem Code.pack (a : Code n) (b : Code m) (x : B n) (y : B m) :
    (a.pair b).write ((Match.rowIndex _ _).symm (x, y)) = Sum.elim (a.write x) (b.write y) :=
  congrArg (a.format.pair b.format).code ((Match.rowIndex _ _).apply_symm_apply (x, y))

variable {F Z : Type} (S : Scheme F)
    {d e M r t q D k n u j z : ℕ} (U : Print.Printer F Z (B S.k) S.m d S.h e M r t q D k n u j z)

def Code.revised (x : Code S.ℓ) (y : Code U.labelBits) : Code (U.addressBits S) :=
  x.pair (y.pair (Code.std (U.planBits S)))

theorem revised_write (x : Code S.ℓ) (y : Code U.labelBits) (a : U.Ticket S) :
    (Code.revised S U x y).write (U.ticket S a) =
      Sum.elim (x.write a.1) (Sum.elim (y.write a.2.1)
        ((Format.addr (U.planBits S)).code (Print.indexCode (U.Outline S) a.2.2))) := by
  rcases a with ⟨b, c, f⟩
  change (x.pair (y.pair (.std _))).write ((Match.rowIndex _ _).symm
    (b, (Match.rowIndex _ _).symm (c, Print.indexCode _ f))) = _
  rw [Code.pack, Code.pack]
  rfl

variable {Ω : Type*} {V : Type} {g σ p : ℕ} (loc : V ↪ Sites S.m S.h)
    (a : Ω → V → U.Tag S g σ p)

def tagSource : Source Ω S.m S.h := fun i =>
  {f | ∃ v, loc v = i ∧ ∃ b, f = fun y => U.tagCode S g σ p (a y v) b}

theorem outline_visible {nav : B S.m → B S.d → B S.m} {R : ℕ}
    (i : Sites S.m S.h) (j : U.bluePins S) :
    Visible (tagSource S U loc a) nav R i (fun w => U.blueCode S
      (U.complete S loc (fun x => (a w x).1) i.1 i.2) j) := by
  by_cases hi : i ∈ Set.range loc
  · obtain ⟨v, rfl⟩ := hi
    refine .inr ⟨_, Reach.refl .., v, rfl, .inl j, funext fun w => ?_⟩
    rw [U.complete_here]
    rfl
  · refine .inl ⟨U.blueCode S (fun _ => Geometry.Outline.empty) j, funext fun w => ?_⟩
    rw [U.complete_vacant _ _ _ hi]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-! # Bootstrapping the dictionary from one neighborhood -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical
variable {Ω : Type*} {m h d e k : ℕ} {src : Source Ω m h} {nav : B m → B d → B m}
    {rows : Ω → (Fmt.rows m d h (.addr e)).obj} {sel : Ω → B m → B h → B k}
    (hnav : ∀ a i, (rows a i).1 = nav i)

def boot (r t : ℕ) (x : (Fmt.rows m d h (.addr e)).obj) (y : B m → B h → B k) :=
  fun i j => Design.number _ ((Boot.around r t (show (Boot.source m d h e k).obj from (x, y)) i).2 j)

include hnav in
theorem Local.boot (hx : Local src nav 0 (Code.std e) (fun a i => (rows a i).2))
    (hy : Local src nav 0 (Code.std k) sel) (r t : ℕ) :
    Local src nav 1 (Code.numbered (Boot.query d r t e k)) (fun a => boot r t (rows a) (sel a)) := by
  intro i j
  let own (a : Ω) (x : B m) := ((rows a x).2 j, tone nav r x, tone nav t x, sel a x j)
  have one (x : B m) (hs : Reach nav 1 i x) (b : (Boot.own d r t e k).pins) :
      Visible src nav 1 (i, j) (fun a => (Boot.own d r t e k).code (own a x) b) := by
    rcases b with b|b|b|b
    · exact (hx x j b).move hs
    · exact .inl ⟨_, rfl⟩
    · exact .inl ⟨_, rfl⟩
    · exact (hy x j b).move hs
  have he (a : Ω) : (Code.numbered (Boot.query d r t e k)).write (Copy.boot r t (rows a) (sel a) i j) =
      (Boot.query d r t e k).code (own a i, fun l => own a (nav i l)) := by
    unfold Copy.boot
    rw [Code.number]
    unfold Boot.around Boot.colored own
    simp only [hnav]
    rfl
  intro b
  simp_rw [he]
  rcases b with b|⟨l, b⟩
  · exact one _ (Reach.refl ..) b
  · exact one _ ⟨_, .inr ⟨l, rfl⟩, rfl⟩ b

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-! # Selector projections and fixed padding away from occupied positions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical
variable {Ω : Type*} {V : Type} {m h d l k w f : ℕ}

abbrev TicketPins (k w f : ℕ) := slots (word k) ⊕ (Fin w × slots (word k)) ⊕ slots (word f)

def ticket (x : B k × (Fin w → B k) × B f) : TicketPins k w f → Bool
  | .inl t => (Format.addr k).code x.1 t
  | .inr (.inl (i, t)) => (Format.addr k).code (x.2.1 i) t
  | .inr (.inr t) => (Format.addr f).code x.2.2 t

variable (x : Ω → (Fmt.rows m d h (.addr l)).obj) (loc : V ↪ Sites m h) (c : Ω → Journal V k w f)

def source : Source Ω m h := fun i =>
  {a | (∃ t, a = fun y => (Format.addr l).code ((x y i.1).2 i.2) t) ∨
       ∃ v, loc v = i ∧ ∃ t, a = fun y => ticket (c y v) t}

variable (nav : B m → B d → B m)

theorem initial : Local (source x loc c) nav 0 (.std l) (fun a i => (x a i).2) :=
  fun _ _ t => Visible.start (.inl ⟨t, rfl⟩)

private theorem packed {n : ℕ} (pad : B n) (s : Ω → V → B n)
    (hs : ∀ (v : V) (b : slots (word n)), ∃ t, ∀ y, (Format.addr n).code (s y v) b = ticket (c y v) t) :
    Local (source x loc c) nav 0 (.std n) (fun y => Sparse.pack loc pad (s y)) := by
  intro i j b
  by_cases hv : (i, j) ∈ Set.range loc
  · obtain ⟨v, hv⟩ := hv
    obtain ⟨t, ht⟩ := hs v b
    refine Visible.start (.inr ⟨v, hv, t, funext fun y => ?_⟩)
    dsimp only [Sparse.pack]
    rw [← hv, loc.injective.extend_apply]
    exact ht y
  · exact .inl ⟨(Format.addr n).code pad b, funext fun y =>
      congrArg (fun z => (Format.addr n).code z b) (Sparse.pack_supported loc pad (s y) (i, j) hv)⟩

theorem opening : Local (source x loc c) nav 0 (.std k) (fun y => (c y).opening loc) :=
  packed x loc c nav 0 _ (fun _ b => ⟨.inl b, fun _ => rfl⟩)

theorem moves (j : Fin w) : Local (source x loc c) nav 0 (.std k) (fun y => (c y).moves loc j) :=
  packed x loc c nav 0 _ (fun _ b => ⟨.inr (.inl (j, b)), fun _ => rfl⟩)

theorem close (pad : B f) : Local (source x loc c) nav 0 (.std f) (fun y => (c y).close loc pad) :=
  packed x loc c nav pad _ (fun _ b => ⟨.inr (.inr b), fun _ => rfl⟩)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-! # Fixed wiring for the local labels of a complete concentration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical
open Rounds Rounds.Input

variable {F : Type} (S : Scheme F) (g ℓ D b d p l k : ℕ)
local notation "Cfg" => design S g ℓ D b d p l
local notation "query" => panelQuery S g ℓ D b d p l k

abbrev Code.lastPage : Code (endWidth S g ℓ D b d p l k) :=
  Code.path Cfg (Code.numbered query) k (Cfg).waves

def radius (a : Design) := (a.waves + 1) * (2 * a.U + 4)

variable {g ℓ D b d p l k} {T f : ℕ} {V : Type} {Ω : Type*}
    (sc : SphereScale.Scales g ℓ D T (p ^ l) b d) (x : Ω → S.format.obj)
    (loc : V ↪ Sites S.m S.h) (c : Ω → Journal V k (Input.design S g ℓ D b d p l).waves f)
    {nav : B S.m → B S.d → B S.m} (hnav : ∀ w i, (x w i).1 = nav i)

local notation "src" => source x loc c

include hnav in
theorem lastPage_nav (w : Ω) (i : B S.m) :
    (Input.lastPage S sc (x w) loc (c w) i).1 = nav i :=
  (path_nav Cfg ..).trans (hnav w i)

include hnav in
theorem local_page :
    Local src nav (1 + (Cfg).waves * (2 * (Cfg).U + 1)) (Code.lastPage S g ℓ D b d p l k)
      (fun w i => (Input.lastPage S sc (x w) loc (c w) i).2) := by
  let start w := panelTape S sc (x w) ((c w).opening loc)
  have first : Local src nav 1 (Code.numbered query) (fun w i => (start w i).2) :=
    Local.boot hnav (initial x loc c nav) (opening x loc c nav) _ _
  exact Local.path (a:=Cfg) (r:=start) hnav first (Cfg).waves
    (fun w => Scenario.before ((c w).moves loc) le_rfl) (fun i => moves x loc c nav i)

variable [Field F] {r t n u a : ℕ} (U : LocalPrinter S g ℓ D b d p l k r t n u a)
    (C : Ω → Journal V k (Input.design S g ℓ D b d p l).waves U.digits)

abbrev Code.final := Code.advance U (Code.lastPage S g ℓ D b d p l k)

include hnav in
theorem local_advance (status : Ω → (Print.Children.Header S.m S.d).obj) (pad : B U.digits)
    (i : B (S.m + U.childBits)) (z : B S.h) (j : (Code.final S U).pins) :
    Visible (source x loc C) nav (radius Cfg) ((U.split i).1, z)
      (fun w => (Code.final S U).write
        (((U.advance (Input.lastPage S sc (x w) loc (C w)) (status w) ((C w).close loc pad)).1 i).2 z) j) := by
  have hw := Local.advance U (lastPage_nav S sc x loc C hnav) (local_page S sc x loc C hnav)
    (close x loc C nav pad) status i z j
  refine hw.mono ?_
  unfold radius
  rw [add_mul, one_mul, mul_add, mul_add, mul_one]
  omega

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-! # Distributing all child labels of all occupied occurrences -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical

variable {V : Type} {Ω : Type*} {m h d w e r : ℕ}
    {src : Source Ω m h} {nav : B m → B d → B m}
    (loc : V ↪ Sites m h) (C : Code e) (f : Ω → B (m + w) → B h → B e)

abbrev Request (V : Type) (w : ℕ) (C : Code e) := V × B w × C.pins

def destination (i : Request V w C) := loc i.1

def requested (i : Request V w C) (a : Ω) :=
  C.write (f a ((Match.rowIndex m w).symm ((loc i.1).1, i.2.1)) (loc i.1).2) i.2.2

abbrev Delivery (src : Source Ω m h) (nav : B m → B d → B m) (r : ℕ) :=
  Plan src nav r (destination loc C) (requested loc C f)

def deliver (sym : Reciprocal nav)
    (vis : ∀ i j t, Visible src nav r ((Match.rowIndex m w i).1, j) (fun a => C.write (f a i j) t)) :
    Delivery loc C f src nav r := by
  apply plan sym
  rintro ⟨i, j, t⟩
  have h := vis ((Match.rowIndex m w).symm ((loc i).1, j)) (loc i).2 t
  rw [Equiv.apply_symm_apply] at h
  exact h

variable {loc C f} [Fintype V]

theorem Delivery.bounds (p : Delivery loc C f src nav r) :
    Fintype.card p.Event = (r + 1) * (Fintype.card V * (2 ^ w * e)) ∧
    Fintype.card {t : p.Event // p.Sends t} ≤ r * (Fintype.card V * (2 ^ w * e)) ∧
    ∀ x, Fintype.card {t : p.Event // p.site t = x} ≤ (r + 1) * 2 ^ ((d + 1) * r) * (2 ^ w * e) := by
  have sz : Fintype.card (B w × C.pins) = 2 ^ w * e := by
    rw [Fintype.card_prod, Fintype.card_fin, C.width]
  have card : Fintype.card (Request V w C) = Fintype.card V * (2 ^ w * e) := by
    change Fintype.card (V × B w × C.pins) = _
    rw [Fintype.card_prod, sz]
  have inj : Function.Injective (fun i : Request V w C => (destination loc C i, i.2)) :=
    fun _ _ h => Prod.ext (loc.injective (Prod.mk.inj h).1) (Prod.mk.inj h).2
  refine ⟨by rw [p.copies, card], by simpa only [card] using p.transmissions, fun x => ?_⟩
  simpa only [sz] using p.congestion Prod.snd inj x

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end

/-! # Sending schedule messages along the original host contacts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical

variable {m d h r : ℕ} {V : Type} (host : V ↪ B m) (adj : V → Finset V)
  (nav : B m → B d → B m)

def Suitable := ∀ v j, ∃ w ∈ insert v (adj v), host w = nav (host v) j

variable {nav}

private theorem reaches_host (ok : Suitable host adj nav) {v : V} {z : B m}
    (hx : Reach nav r (host v) z) : z ∈ Set.range host := by
  induction r generalizing v with
  | zero => exact ⟨v, hx⟩
  | succ r ih =>
    obtain ⟨y, h, hy⟩ := hx
    rcases h with rfl|⟨j, rfl⟩
    · exact ih hy
    · obtain ⟨w, _, hw⟩ := ok v j
      rw [← hw] at hy
      exact ih hy

variable {Ω I : Type*} {src : Source Ω m h} {dest : I → Sites m h} {value : I → Ω → Bool}

def Plan.On (p : Plan src nav r dest value) : Prop :=
  ∃ v : I → Fin (r + 1) → V,
    (∀ i t, host (v i t) = p.station i t) ∧
    ∀ i (t : Fin r), v i t.succ ∈ insert (v i t.castSucc) (adj (v i t.castSucc))

theorem Plan.on_host (p : Plan src nav r dest value) (hr : Reciprocal nav) (hs : Suitable host adj nav)
    (he : ∀ i, (dest i).1 ∈ Set.range host) : p.On host adj := by
  have occurs (i : I) (t : Fin (r + 1)) : ∃ v, host v = p.station i t := by
    obtain ⟨x, hx⟩ := he i
    have h := (p.reaches i t).symm hr
    rw [← hx] at h
    exact reaches_host host adj hs h
  choose f hf using occurs
  refine ⟨f, hf, fun i t => ?_⟩
  have h₁ : host (f i t.succ) = p.station i (t.val + 1) := hf _ _
  have h₂ : host (f i t.castSucc) = p.station i t := hf _ _
  have step := p.step i t.val t.isLt
  rw [← h₁, ← h₂] at step
  rcases step with h|⟨j, hj⟩
  · exact Finset.mem_insert.mpr (.inl (host.injective h))
  · obtain ⟨w, hw, he⟩ := hs _ j
    exact host.injective (he.trans hj) ▸ hw

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}

variable (h sc)

def NoExtras (A : P.HostChart S z) (status : (Print.Children.Header S.m S.d).obj) : Prop :=
  ∀ v j, A.graph (A.host v) j ≠ A.host v → (status (A.host v)).2 j = true

include h in
theorem nav_suitable (hx : NoExtras A status) : Copy.Suitable A.host P.adj A.graph := by
  intro v j
  obtain ⟨w, hw⟩ := h.parents.closed v j
  refine ⟨w, ?_, hw⟩
  by_cases he : v = w
  · exact Finset.mem_insert.mpr (.inl he.symm)
  exact Finset.mem_insert_of_mem ((h.parents.edge v w he).mpr
    ⟨j, hw.symm, hx v j (fun eq => he (A.host.injective (hw.trans eq)).symm)⟩)

include h in
theorem deliveries (hx : NoExtras A status) {Ω : Type*} {e a R : ℕ}
    {src : Copy.Source Ω S.m S.h} {C : Copy.Code e} {f : Ω → B (S.m + a) → B S.h → B e}
    (p : Copy.Delivery A.coord C f src A.graph R) : p.On A.host P.adj :=
  p.on_host A.host P.adj A.sym (h.nav_suitable hx) (fun i => ⟨i.1.val.1, rfl⟩)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-! # Synchronous schedules for raw and revised output labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
open Coloring Assembly Assembly.Neighborhood Surface.Local
open scoped Classical
open Rounds Rounds.Input
variable {F V : Type} [Field F] {Ω : Type*} (S : Scheme F)
    {g ℓ D b d p l k r t n u f T : ℕ} (U : LocalPrinter S g ℓ D b d p l k r t n u f)
    (sc : SphereScale.Scales g ℓ D T (p ^ l) b d) (x : Ω → S.format.obj)
    (loc : V ↪ Sites S.m S.h) (c : Ω → Journal V k (Input.design S g ℓ D b d p l).waves U.digits)
    (status : Ω → (Print.Children.Header S.m S.d).obj) (pad : B U.digits)
    {nav : B S.m → B S.d → B S.m} (hnav : ∀ w i, (x w i).1 = nav i) (sym : Reciprocal nav)

local notation "Cfg" => design S g ℓ D b d p l
local notation "src" => source x loc c
local notation "R" => radius Cfg

def printed (a : Ω) := U.advance (Input.lastPage S sc (x a) loc (c a)) (status a) ((c a).close loc pad)

local notation "out" => printed S U sc x loc c status pad

def rawDelivery : Delivery loc (Code.final S U)
    (fun a i => ((out a).1 i).2) src nav R :=
  deliver _ _ _ sym (local_advance S sc x loc hnav U c status pad)

variable {g' σ w : ℕ} (tag : Ω → V → U.Tag S g' σ w)

def sources : Source Ω S.m S.h := fun i => source x loc c i ∪ tagSource S U loc tag i

abbrev Code.overlay := Code.revised S U (.std S.ℓ) (Code.final S U)

def revised (a : Ω) := U.overlay S (x a) (out a) (U.complete S loc fun v => (tag a v).1)

local notation "target" => revised S U sc x loc c status pad tag
local notation "pool" => sources S U x loc c tag

include hnav in
theorem local_overlay (i : B (S.m + U.childBits)) (j : B S.h) (z : (Code.overlay S U).pins) :
    Visible pool nav R ((U.split i).1, j) (fun a => (Code.overlay S U).write (((target a).1 i).2 j) z) := by
  have hx (a : Ω) : (Code.overlay S U).write (((target a).1 i).2 j) z =
      Sum.elim ((Code.std S.ℓ).write ((x a (U.split i).1).2 j))
        (Sum.elim ((Code.final S U).write (((out a).1 i).2 j)) (fun b =>
          U.blueCode S (U.complete S loc (fun v => (tag a v).1) (U.split i).1 j) ((U.split i).2, b))) z :=
    congrFun (revised_write S U (.std _) (Code.final S U) _) z
  simp_rw [hx]
  rcases z with z|z|z
  · exact ((initial x loc c nav _ _ z).mono (Nat.zero_le _)).weaken (fun _ => Set.subset_union_left)
  · exact (local_advance S sc x loc hnav U c status pad i j z).weaken (fun _ => Set.subset_union_left)
  · exact (outline_visible S U loc tag ((U.split i).1, j) ((U.split i).2, z)).weaken
      (fun _ => Set.subset_union_right)

def overlayDelivery : Delivery loc (Code.overlay S U)
    (fun a i => ((target a).1 i).2) pool nav R :=
  deliver _ _ _ sym (local_overlay S U sc x loc c status pad hnav tag)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy
end
