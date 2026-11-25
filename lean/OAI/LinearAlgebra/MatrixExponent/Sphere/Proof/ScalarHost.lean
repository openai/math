import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Weight
import OAI.LinearAlgebra.MatrixExponent.Sphere.Verifier.Caps
import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.Accept
import OAI.LinearAlgebra.MatrixExponent.Sphere.Scalar.Term
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Origin
import OAI.LinearAlgebra.MatrixExponent.Sphere.Price.Allowance
import OAI.LinearAlgebra.MatrixExponent.Sphere.Copy.Overlay
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access

/-!
# Reading the scalar weight from a child address

Each address is an encoding of the preceding neighborhood. Its
central entry recovers the earlier address, allowing a dictionary
to accumulate every tariff independently of the input and selectors.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Design
open Assembly Coloring

variable (a : Design) {F N A : Type} {e : ℕ}
  [Field F] [Fintype F] [ExpChar F a.p] (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (menu : a.Menu F N A e) (k : ℕ) (start : B e → F)

def historyWeight : (i : ℕ) → i ≤ a.waves → B (a.widthAt e k i) → F
  | 0, _, x => start x
  | i + 1, hi, x => historyWeight i (Nat.le_of_succ_le hi) (a.previous x) *
      a.tariff hF ⟨i, hi⟩ (a.menuAt hF menu k i (Nat.le_of_succ_le hi)) k
        ((number (a.observed (a.widthAt e k i) k)).symm x)

theorem historyWeight_path (p : (a.port e).obj) {i : ℕ} (hi : i ≤ a.waves)
    (c : Fin i → (a.selectors k).obj) (v : B a.m × B a.h) :
    a.historyWeight hF menu k start i hi ((a.path p i c v.1).2 v.2) =
      start ((p v.1).2 v.2) * a.localCharge p hF menu i hi c v := by
  induction i with
  | zero => simp [historyWeight, path, localCharge]
  | succ i ih =>
    rw [historyWeight, path, previous_update, ih, localCharge, mul_assoc]
    simp only [update, Fmt.update, Equiv.symm_apply_apply]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Design

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Surface.Local

theorem window_label {F K N : Type} [Field F] [Finite K] {m d h ℓ M r t q D k n u j z : ℕ}
    (U : Printer F K N m d h ℓ M r t q D k n u j z)
    (data : U.rows.obj) (status : (Children.Header m d).obj) (choice : U.selectors.obj)
    (v : B m × B h) (i : B U.childBits) :
    Match.rowIndex U.window.width U.childBits (((U.advance data status choice).1 (U.split.symm (v.1, i))).2 v.2) =
      (Design.number U.window ((U.around data choice v.1).2 v.2), i) := by
  let e := U.split.symm (v.1, i)
  change Match.rowIndex _ _ (Children.label _ (U.update data status choice) e v.2) = _
  rw [Children.label_at (U.update data status choice) e v.2]
  change (((U.update data status choice).1 (U.split e).1).2 v.2, (U.split e).2) = _
  rw [show U.split e = _ from U.split.apply_symm_apply _]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p]
    (S : Scheme F) (z : S.format.obj) (sc : Scales g ℓ D T (p ^ l) b d)
    (hK : Ready K ℓ D g (p ^ l) b d)
    (hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F)
    (mobility : B S.ℓ → B S.k → Bool) (U : LocalPrinter S g ℓ D b d p l k r t n u f)

local notation "Cfg" => design S g ℓ D b d p l

def weightOf (raw : B U.labelBits) : F :=
  let window := (Design.number U.window).symm (Match.rowIndex _ _ raw).1
  let start := panelGuard S sc k ∘ (Design.number (panelQuery S g ℓ D b d p l k)).symm
  (Cfg).historyWeight hF (localMenu S hK mobility k) k start (Cfg).waves le_rfl (window 0 0).1 *
    U.tariff window

theorem journalWeight_label {V : Type} (loc : V ↪ B S.m × B S.h)
    (c : Journal V k (Cfg).waves U.digits) (status : (Print.Children.Header S.m S.d).obj)
    (v : B S.m × B S.h) (i : B U.childBits) :
    journalWeight S z sc hK hF mobility U loc c v =
      weightOf S sc hK hF mobility U
        (((U.advance (lastPage S sc z loc c) status (c.close loc U.pad)).1 (U.split.symm (v.1, i))).2 v.2) := by
  let page := lastPage S sc z loc c
  let choice := c.close loc U.pad
  let raw : B U.labelBits := (((U.advance page status choice).1 (U.split.symm (v.1, i))).2 v.2)
  let window := ((U.around page choice v.1).2 v.2)
  have he : (Design.number U.window).symm (Match.rowIndex _ _ raw).1 = window := by
    rw [show Match.rowIndex _ _ raw = (Design.number U.window window, i) from
      U.window_label page status choice v i]
    exact (Design.number U.window).symm_apply_apply window
  have hc : (window 0 0).1 = (page v.1).2 v.2 := by
    simp only [window, Print.Printer.around, Fmt.around, Fmt.expand, Fmt.zip, Neighborhood.origin]
  change _ = weightOf S sc hK hF mobility U raw
  unfold weightOf
  dsimp only
  rw [he, hc]
  unfold page lastPage Input.page
  rw [Scenario.before_self, Design.historyWeight_path]
  simp only [journalWeight, Function.comp_apply, panelTape, Fmt.update, Equiv.symm_apply_apply, mul_assoc]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # A single scalar dictionary independent of the input and proposed layout -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Sphere SphereScale Surface Surface.Local
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {sc : Scales g ℓ D T (p ^ l) b d} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l

section
variable (S sc hK hF mobility U)

/-- The siblings share a window. Replace only the child index
to reconstruct the full canonical blueprint. -/
private def tagOf (old : B S.ℓ) (raw : B U.labelBits) : U.Tag S g ℓ (Cfg).waves :=
  let e := Match.rowIndex U.window.width U.childBits
  (fun i => U.original S old (e.symm ((e raw).1, i)),
    credits S hK hF mobility k (U.centerLabel S raw))

def factorOf : B S.ℓ × B U.labelBits × U.Tag S g ℓ (Cfg).waves → F :=
  fun (old, raw, tag) => if tag = tagOf S hK hF mobility U old raw then weightOf S sc hK hF mobility U raw else 0

end

namespace ReadyPanel
variable (h : P.ReadyPanel A hK hF mobility k U status pres) (sc : Scales g ℓ D T (p ^ l) b d)

private theorem tag_eq (c : h.Book) (v : P.Occupied) :
    h.actual sc c v = tagOf S hK hF mobility U ((z (A.coord v).1).2 (A.coord v).2)
      (U.printedAt S (h.printing sc c) (U.centerAt S (A.coord v).1 (A.coord v).2 0)) := by
  let w := A.coord v
  let data := lastPage S sc z A.coord c
  let choice := c.close A.coord U.pad
  let raw (i : B U.childBits) : B U.labelBits :=
    U.printedAt S (h.printing sc c) (U.centerAt S w.1 w.2 i)
  let old : B S.ℓ := (z w.1).2 w.2
  let e := Match.rowIndex U.window.width U.childBits
  let window := (U.around data choice w.1).2 w.2
  have hr i : e (raw i) = (Design.number U.window window, i) :=
    U.window_label data status choice w i
  have hi i : raw i = e.symm ((e (raw 0)).1, i) := by
    apply e.injective
    rw [Equiv.apply_symm_apply, hr, hr]
  have hc : U.centerLabel S (raw 0) = (data w.1).2 w.2 := by
    change ((Design.number U.window).symm (e (raw 0)).1 0 0).1 = _
    rw [hr, Equiv.symm_apply_apply]
    simp only [window, Print.Printer.around, Fmt.around, Fmt.expand, Fmt.zip, Neighborhood.origin]
  apply Prod.ext
  · funext i
    exact congrArg (U.original S old) (hi i)
  · exact congrArg (credits S hK hF mobility k) hc.symm

theorem factor_eq (c : h.Paths sc) (v : P.Occupied) :
    h.factor sc c v = factorOf S sc hK hF mobility U
      ((z (A.coord v).1).2 (A.coord v).2,
       U.printedAt S (h.printing sc c.1) (U.centerAt S (A.coord v).1 (A.coord v).2 0), c.2.val v) := by
  let w := A.coord v
  let old : B S.ℓ := (z w.1).2 w.2
  let raw : B U.labelBits := U.printedAt S (h.printing sc c.1) (U.centerAt S w.1 w.2 0)
  have ht : h.actual sc c.1 v = tagOf S hK hF mobility U old raw := h.tag_eq sc c.1 v
  have hw : h.weight sc c.1 v = weightOf S sc hK hF mobility U raw :=
    journalWeight_label S z sc hK hF mobility U A.coord c.1 status w 0
  change _ = factorOf S sc hK hF mobility U (old, raw, c.2.val v)
  unfold factor Geometry.factor factorOf
  dsimp only
  by_cases hh : c.2.val v = h.actual sc c.1 v
  · rw [ite_eq_left hh, ite_eq_left (hh.trans ht), hw]
  · rw [ite_eq_right hh, ite_eq_right (fun e => hh (e.trans ht.symm))]

end ReadyPanel
end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Exact evaluation of the geometrically checked expansion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
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
variable (E : Expansion sc h) (i : E.I)

private theorem sameValue (M : CertifiedTerm E i) (y' : U.template.format.obj) (a' : U.Matrix S)
    (ok : U.Valid S z y' a') {V : Type} [Fintype V] (G : U.Graph S y' V)
    (hy : y' = E.record i) (ha : a' = U.canonical S z (E.record i)) :
    (U.admitted S z y' a' ok G pres h.directed).term.diagram.eval = (E.term i).diagram.eval := by
  subst y' a'
  exact (M.eval G h.directed ((E.release i.1 i.2.1).retains i.2.2)).symm

theorem aligned (M : CertifiedTerm E i) (c : h.Paths sc)
    (hi : c.1 = E.select.write i) (ha : c.2.val = h.actual sc (E.select.write i)) :
    (h.term sc c).diagram.eval = (E.term i).diagram.eval := by
  have hy : h.printing sc c.1 = E.record i := by rw [hi]; exact (E.record_eq i).symm
  have hb : h.geometry sc c = U.canonical S z (E.record i) := by
    unfold geometry
    rw [ha, actual_eq]
    exact U.complete_of_vacant S A.coord _ M.away
  exact sameValue E i M (h.printing sc c.1) (h.geometry sc c) c.2.property.1 (h.hostGraph sc c.1) hy hb

variable (h sc)

@[instance_reducible] private def enumPaths {J V C : Type} [Fintype J] [Fintype V] [Fintype C]
    (ok : J → (V → C) → Prop) : Fintype (Candidate ok) := inferInstance

instance : Fintype (h.Paths sc) := enumPaths (h.admissible sc)

/-- The index set is checked by bit operations. Its scalar factors
are table entries. In particular the sums are exact in finite characteristic. -/
theorem identity (v : Val x) (w : Val y) :
    P.diagram.eval v w = ∑ c : h.Paths sc, (∏ i, h.factor sc c i) * (h.term sc c).diagram.eval v w := by
  let m := h.measured sc
  let E := m.toExpansion
  have ok : ∀ i, h.admissible sc (E.select.write i) (h.actual sc (E.select.write i)) :=
    fun i => accepted E i (m.checked i)
  rw [E.value v w]
  symm
  apply checked_sum E.select (h.actual sc) (h.admissible sc) ok (h.weight sc) E.coeff E.valid
    (fun c => (h.term sc c).diagram.eval v w) (fun i => (E.term i).diagram.eval v w)
  intro i
  rw [aligned E i (m.checked i) _ rfl rfl]

/-- Charge one isolated scalar per occupied cell, including zero coefficients. -/
abbrev summand (c : h.Paths sc) := P.weighted (h.term sc c) (h.factor sc c)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-! # One dictionary for the physical stations and scalar factors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
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
variable (S hK hF mobility U)

abbrev Ticket := B (U.addressBits S) ⊕ B S.ℓ × B U.labelBits × U.Tag S g ℓ (Cfg).waves

def dictionary (sc : Scales g ℓ D T (p ^ l) b d) : Ticket S U → Table F
  | .inl c => ((U.revised S).scheme.decode c).orderedTable 0
  | .inr c => Diagram.scalarTable (factorOf S sc hK hF mobility U c)

variable {S hK hF mobility U} (h sc)

def ticket (c : h.Paths sc) : (h.summand sc c).diagram.V → Ticket S U
  | .inl v =>
    let i := (h.shows sc c).pres.vertex v
    .inl (((h.data sc c).1 i.1).2 i.2.1)
  | .inr v =>
    let i := A.coord v
    .inr ((z i.1).2 i.2, U.printedAt S (h.printing sc c.1) (U.centerAt S i.1 i.2 0), c.2.val v)

theorem table (c : h.Paths sc) (v : (h.summand sc c).diagram.V) :
    (h.summand sc c).diagram.table v = dictionary S hK hF mobility U sc (h.ticket sc c v) := by
  cases v with
  | inl v =>
    let i := (h.shows sc c).pres.vertex v
    change (((U.revised S).scheme.decode (((h.data sc c).1 i.1).2 i.2.1)).orderedTable i.2.2) =
      (((U.revised S).scheme.decode (((h.data sc c).1 i.1).2 i.2.1)).orderedTable 0)
    rw [Fin.eq_zero i.2.2]
    rfl
  | inr v =>
    exact congrArg Diagram.scalarTable (h.factor_eq sc c v)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-! # Physical bit encoding of the common output dictionary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
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
variable (S U)

/-- First distinguish the ordinary and scalar labels. The unused field is zero. -/
abbrev Pins := Unit ⊕ (Copy.Code.overlay S U).pins ⊕ (Copy.Code.std S.ℓ).pins ⊕
  (Copy.Code.final S U).pins ⊕ U.tagPins S g ℓ (Cfg).waves

def encode : Ticket S U → Pins S U → Bool
  | .inl a => Sum.elim (fun _ => false) (Sum.elim ((Copy.Code.overlay S U).write a) (fun _ => false))
  | .inr v => Sum.elim (fun _ => true) (Sum.elim (fun _ => false)
      (Sum.elim ((Copy.Code.std S.ℓ).write v.1) (Sum.elim ((Copy.Code.final S U).write v.2.1)
        (U.tagCode S g ℓ (Cfg).waves v.2.2))))

omit [Field F] [Fintype F] [ExpChar F p] in
theorem encode_injective : Function.Injective (encode S U) := by
  rintro (a|a) (b|b) hab
  · refine congrArg Sum.inl ((Copy.Code.overlay S U).write.injective ?_)
    exact funext fun i => congrFun hab (.inr (.inl i))
  · exact Bool.false_ne_true (congrFun hab (.inl ())) |>.elim
  · exact Bool.false_ne_true (congrFun hab (.inl ())).symm |>.elim
  · refine congrArg Sum.inr (Prod.ext ?_ (Prod.ext ?_ ?_))
    · exact (Copy.Code.std S.ℓ).write.injective (funext fun i => congrFun hab (.inr (.inr (.inl i))))
    · exact (Copy.Code.final S U).write.injective (funext fun i => congrFun hab (.inr (.inr (.inr (.inl i)))))
    · exact (U.tagCode S g ℓ (Cfg).waves).injective (funext fun i => congrFun hab (.inr (.inr (.inr (.inr i)))))

omit [Field F] [Fintype F] [ExpChar F p] in
theorem pin_count : Fintype.card (Pins S U) =
    U.addressBits S + (1 + S.ℓ + U.labelBits + U.tagWidth S g ℓ (Cfg).waves) := by
  unfold Pins
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_unit,
    Copy.Code.width, Copy.Code.width, Copy.Code.width, Print.Printer.tagSize]
  omega

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-! # Child slots and parent contacts after adjoining the scalar bank -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
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

variable (c : h.Paths sc)

abbrev ChildSlot (g ℓ D n : ℕ) :=
  Print.Children.Part (chunks ℓ D) D (Layout.Sharing.allocation g ℓ) n ⊕ Unit

def scalarParent : (h.summand sc c).V → P.V := Sum.elim (h.parent sc c) id

def scalarSlots : (h.summand sc c).V ≃ P.V × ChildSlot g ℓ D n :=
  ((Print.Children.parts P.V (chunks ℓ D) D (Layout.Sharing.allocation g ℓ) n).sumCongr
    (Equiv.prodUnique P.V Unit).symm).trans (Equiv.prodSumDistrib _ _ _).symm

theorem scalarSlots_parent (v : (h.summand sc c).V) :
    (h.scalarSlots sc c v).1 = h.scalarParent sc c v := by cases v <;> rfl

include h sc in
theorem scalar_count : Fintype.card (ChildSlot g ℓ D n) ≤ D ^ (terminalExponent g ℓ) + 1 := by
  change Fintype.card (Print.Children.Part (chunks ℓ D) D (Layout.Sharing.allocation g ℓ) n ⊕ Unit) ≤ _
  rw [Fintype.card_sum, Fintype.card_unit]
  exact Nat.add_le_add_right (h.per_parent sc) _

theorem scalar_common (c' : h.Paths sc) :
    (h.summand sc c).V = (h.summand sc c').V ∧
    (h.summand sc c).frame.N = (h.summand sc c').frame.N ∧
    (h.summand sc c).frame.C = (h.summand sc c').frame.C ∧
    (h.summand sc c).frame.frozen = (h.summand sc c').frame.frozen := ⟨rfl, rfl, rfl, rfl⟩

theorem scalar_mem {v w : (h.summand sc c).V} (he : w ∈ (h.summand sc c).frame.N v) :
    h.scalarParent sc c w ∈ insert (h.scalarParent sc c v) (P.adj (h.scalarParent sc c v)) := by
  rcases v with v|v
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp he
    exact h.parent_mem sc c hz
  · exact (Finset.notMem_empty _ he).elim

theorem scalar_ext (i : slots x ⊕ slots y) :
    let v := (h.summand sc c).frame.place (Packing.portEnd (h.summand sc c).diagram i)
    (h.scalarParent sc c v.1, v.2) = P.place (Packing.portEnd P.diagram i) := by
  change (fun v => (h.scalarParent sc c v.1, v.2)) (P.scalarPlace _
    (Packing.portEnd (P.weighted (h.term sc c) (h.factor sc c)).diagram i)) = _
  rw [P.weighted_portEnd (h.term sc c) (h.factor sc c) i]
  exact h.parent_ext sc c i

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-!
# Uniform widths for a proposed layout

The integers in the geometric proposal are independent of the host
count, the block size, the long input labels and the field. The
number of selector bits and the output label width have linear growth.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Sphere SphereScale Surface.Local

private def reserveFor (a : Sphere.Surface.Local.Design) (g ℓ D n A : ℕ) : Reserve :=
  let M := chunks ℓ D
  let t := Layout.Sharing.allocation g ℓ
  let slot := Print.Children.Part M D t n
  let lane := Print.Compass.FinalLane (Fin a.R) (panelKeys a) M D t n
  let cap := 2 * terminalExponent g ℓ * D * D ^ terminalExponent g ℓ
  ⟨a.d, a.hops, a.waves, a.inflation, slope A D a.M, M * (a.R + 2 * (2 * D ^ t)),
    Print.indexBits slot, Print.indexBits (Print.Band lane cap)⟩

private def growthFor (q : Reserve) (g ℓ D m : ℕ) :=
  let plan := Print.indexBits (Geometry.Outline q.degree q.span m)
  let tags := Nat.card (Geometry.Blueprint q.child q.degree q.span m × Geometry.Credits g ℓ D q.waves)
  q.scale + 2 ^ ((q.deg + 1) * (D ^ 5 + 1)) + tags + (1 + q.label + plan) +
    (q.slope * (1 + q.waves) + q.digits + Nat.clog 2 tags)

private def stub (d : ℕ) : Scheme ℕ :=
  ⟨0, d, 0, 0, 0, 0, fun _ => ⟨fun _ _ => 0, fun _ _ => false, fun _ _ => none, fun _ _ => 1⟩⟩

def growth (g ℓ D n A d m : ℕ) :=
  growthFor (reserveFor (design (stub d) g ℓ D 0 0 0 0) g ℓ D n A) g ℓ D m

variable {F : Type} [Field F] (S : Scheme F) {g ℓ D b d p l k r t n u f A : ℕ}
  (U : LocalPrinter S g ℓ D b d p l k r t n u f)

local notation "Cfg" => design S g ℓ D b d p l
local notation "T" => Nat.card (Print.Printer.Tag S U g ℓ (Surface.Local.Design.waves Cfg))

structure GrowthBounds (J : ℕ) : Prop where
  waves : (Cfg).waves ≤ J
  radius : 2 ^ ((S.d + 1) * ((Cfg).U + 1)) ≤ J
  child : 2 ^ U.childBits ≤ J
  span : 2 ^ U.spanBits ≤ J
  degree : 2 ^ U.template.scheme.d ≤ J
  plan : U.planBits S ≤ J
  tags : T ≤ J
  selectors : k + k * (Cfg).waves + U.digits + Nat.clog 2 T ≤ J * (1 + f)
  address : U.addressBits S ≤ J * (1 + S.ℓ + f)

private theorem selector_bound {s w k f z c : ℕ} (hk : k ≤ s * (1 + f)) :
    k + k * w + f * z + c ≤ (s * (1 + w) + z + c) * (1 + f) := by
  calc
    _ ≤ s * (1 + f) + s * (1 + f) * w + (1 + f) * z + c * (1 + f) := by
      gcongr
      · omega
      · exact Nat.le_mul_of_pos_right _ (by omega)
    _ = _ := by ring

private theorem parts {j p r t b l s : ℕ} (he : j = p + r + t + (1 + l + b) + s) :
    p ≤ j ∧ r ≤ j ∧ t ≤ j ∧ b ≤ j ∧ 1 + l + b ≤ j ∧ s ≤ j := by omega

theorem growth_bounds (hc : U.cap = 2 * terminalExponent g ℓ * D * D ^ terminalExponent g ℓ)
    (hk : k ≤ slope A D (room ℓ D g) * (1 + f)) : GrowthBounds S U (growth g ℓ D n A S.d S.k) := by
  let q := reserveFor Cfg g ℓ D n A
  let J := growth g ℓ D n A S.d S.k
  have hspan : U.spanBits = q.span := by
    unfold Print.Printer.spanBits
    rw [hc]
    rfl
  have hplan : U.planBits S = Print.indexBits (Geometry.Outline q.degree q.span S.k) := by
    rw [← hspan]
    rfl
  have htag : T = Nat.card (Geometry.Blueprint q.child q.degree q.span S.k × Geometry.Credits g ℓ D q.waves) := by
    rw [← hspan]
    rfl
  have he : J = q.scale + 2 ^ ((S.d + 1) * ((Cfg).U + 1)) + T + (1 + q.label + U.planBits S) +
      (q.slope * (1 + q.waves) + q.digits + Nat.clog 2 T) := by
    rw [htag, hplan]
    rfl
  obtain ⟨hs, hr, ht, hb, ha, hsel⟩ := parts he
  have hq := q.fits hs
  have hd : U.digits = f * q.digits := mul_assoc ..
  let X := 1 + S.ℓ + f
  have hX : 0 < X := by unfold X; omega
  have hw : endWidth S g ℓ D b d p l k ≤ q.motion * X :=
    ((Cfg).last_fits S.ℓ k).trans (((Cfg).arity_bound S.ℓ k).trans (q.motion_bound hk))
  have hw' : U.window.width ≤ q.window * X := by
    rw [U.window_width, mul_one, hd]
    exact q.window_bound hw (by unfold X; omega)
  have hchild : U.childBits = q.child := rfl
  have hlabel : U.labelBits ≤ q.label * X := by
    rw [Print.Printer.labelBits, hchild, Reserve.label, add_mul]
    exact Nat.add_le_add hw' (Nat.le_mul_of_pos_right _ hX)
  change GrowthBounds S U J
  refine ⟨?_, hr, hq.contacts, by rw [hspan]; exact hq.span, hq.degree, hb, ht, ?_, ?_⟩
  · change q.waves ≤ J
    exact (show ∀ w d : ℕ, w ≤ 10001 + 4 * w + d by omega) q.waves _ |>.trans hq.common
  · rw [hd]
    exact (selector_bound (s := q.slope) (w := q.waves) hk).trans
      (Nat.mul_le_mul_right (1 + f) hsel)
  · apply le_trans _ (Nat.mul_le_mul_right X ha)
    rw [Print.Printer.addressBits, add_mul, add_mul, one_mul]
    have := Nat.le_mul_of_pos_right (U.planBits S) hX
    omega

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Number of selector bits including every field of the proposed layout -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
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
private theorem candidate_bound {I V C : Type} [Finite V] [Finite C] [Finite I]
    (ok : I → (V → C) → Prop) :
    Nat.card (Candidate ok) ≤ Nat.card I * (Nat.card C) ^ (Nat.card V) := by
  let e : Candidate ok → I × (V → C) := fun c => (c.1, c.2.val)
  have inj : Function.Injective e := by
    rintro ⟨i, z⟩ ⟨j, w⟩ he
    obtain ⟨rfl, r⟩ := Prod.mk.inj he
    exact congrArg (Sigma.mk i) (Subtype.ext r)
  simpa only [Nat.card_prod, Nat.card_fun] using Nat.card_le_card_of_injective e inj

variable (h sc)

def selectorWidth (_h : P.ReadyPanel A hK hF mobility k U status pres) :=
  k + k * (Cfg).waves + U.digits + Nat.clog 2 (Nat.card (U.Tag S g ℓ (Cfg).waves))

theorem count : Nat.card (h.Paths sc) ≤ 2 ^ (h.selectorWidth * Fintype.card P.Occupied) := by
  have hc := candidate_bound (h.admissible sc)
  let b := Nat.card h.Guess
  have hh := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) b) (Fintype.card P.Occupied)
  have hj : Nat.card h.Book = 2 ^ ((k + k * (Cfg).waves + U.digits) * Fintype.card P.Occupied) := by
    unfold Book Journal
    simp only [Nat.card_fun, Nat.card_prod, B, Nat.card_fin, pow_mul, pow_add, mul_assoc, Nat.card_eq_fintype_card (α := P.Occupied)]
  rw [hj, Nat.card_eq_fintype_card (α := P.Occupied)] at hc
  refine hc.trans ((Nat.mul_le_mul_left _ hh).trans_eq ?_)
  rw [←pow_mul, ←pow_add, ←add_mul]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-! # Unique bit strings for the complete local proposal -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
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

private theorem ticket_bijective (a w b : ℕ) : Function.Bijective (Copy.ticket (k := a) (w := w) (f := b)) := by
  let C := (Format.addr a).code
  let D := (Format.addr b).code
  constructor
  · intro x y he
    refine Prod.ext (C.injective ?_) (Prod.ext (funext fun j => C.injective ?_) (D.injective ?_))
    · exact funext fun i => congrFun he (.inl i)
    · exact funext fun i => congrFun he (.inr (.inl (j, i)))
    · exact funext fun i => congrFun he (.inr (.inr i))
  · intro z
    refine ⟨(C.symm (z ∘ Sum.inl), fun j => C.symm (fun i => z (.inr (.inl (j, i)))),
      D.symm (fun i => z (.inr (.inr i)))), ?_⟩
    funext i
    rcases i with i|⟨j, i⟩|i
    · exact congrFun (C.apply_symm_apply _) i
    · exact congrFun (C.apply_symm_apply _) i
    · exact congrFun (D.apply_symm_apply _) i

abbrev ControlPins (_h : P.ReadyPanel A hK hF mobility k U status pres) :=
  Copy.TicketPins k (Cfg).waves U.digits ⊕ U.tagPins S g ℓ (Cfg).waves

variable (h sc)

def controls (c : h.Paths sc) (v : P.Occupied) : h.ControlPins → Bool :=
  Sum.elim (Copy.ticket (c.1 v)) (U.tagCode S g ℓ (Cfg).waves (c.2.val v))

theorem control_size :
    Fintype.card h.ControlPins = k + k * (Cfg).waves + U.digits + U.tagWidth S g ℓ (Cfg).waves := by
  unfold ControlPins
  rw [Fintype.card_sum, U.tagSize]
  simp only [Copy.TicketPins, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_slots, wd_word]
  ring

theorem controls_injective : Function.Injective (h.controls sc) := by
  rintro ⟨a, b⟩ ⟨c, d'⟩ he
  have ha : a = c := funext fun v => (ticket_bijective ..).1
    (funext fun i => congrFun (congrFun he v) (.inl i))
  subst c
  have hb : b = d' := Subtype.ext (funext fun v => (U.tagCode S g ℓ (Cfg).waves).injective
    (funext fun i => congrFun (congrFun he v) (.inr i)))
  rw [hb]

/-- After recognizing the finite tag, the journal bits need no test.
The visible check is independent of their values. -/
theorem controls_range (c₀ : h.Book) (bits : P.Occupied → h.ControlPins → Bool) :
    bits ∈ Set.range (h.controls sc) ↔
      ∃ a : P.Occupied → h.Guess, (∀ v, U.tagCode S g ℓ (Cfg).waves (a v) = bits v ∘ Sum.inr) ∧
        h.admissible sc c₀ a := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.2.val, fun _ => rfl, (h.admissible_eq sc c.1 c₀ c.2.val).mp c.2.property⟩
  · rintro ⟨a, hcode, ha⟩
    choose j hj using fun v => (ticket_bijective k (Cfg).waves U.digits).2 (bits v ∘ Sum.inl)
    refine ⟨⟨j, a, (h.admissible_eq sc c₀ j a).mp ha⟩, ?_⟩
    funext v i
    cases i with
    | inl i => exact congrFun (hj v) i
    | inr i => exact congrFun (hcode v) i

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-! # The unweighted sum on the extended host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
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

def exponent (g ℓ : ℕ) := Geometry.overhead g (terminalExponent g ℓ) + 2

theorem exact_sum (a : Val x) (b : Val y) :
    P.diagram.eval a b = ∑ c : h.Paths sc, (h.summand sc c).diagram.eval a b := by
  rw [h.identity sc]
  exact Finset.sum_congr rfl fun c _ => (P.weighted_eval (h.term sc c) (h.factor sc c) a b).symm

theorem bounded (c : h.Paths sc) : Concentrated P (h.summand sc c) (exponent g ℓ) n ℓ := by
  have hi : ℓ ≤ terminalExponent g ℓ := by
    have eq := (Layout.Fanout.exponent_bounds (c := Layout.Sharing.radius (Layout.Sharing.allocation g ℓ))
      (ℓ := ℓ) le_rfl).1
    unfold terminalExponent
    omega
  have hu := (Nat.mul_le_mul_left u (Nat.pow_le_pow_right sc.Dpos hi)).trans h.units
  exact (h.concentrated sc c).weighted (h.factor sc c) (le_trans (by decide) U.large) hu

theorem core_degree (c : h.Paths sc) (v : (h.summand sc c).V) : ((h.summand sc c).frame.C v).card ≤ 3 := by
  cases v with
  | inl i => exact (Finset.card_map _).le.trans (h.trivalent sc c i)
  | inr _ => exact Nat.zero_le _

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end
