import OAI.Computability.BorderVNP.DiagonalCellLeaves
import OAI.Computability.BorderVNP.ShortenNetworkBundle
import OAI.Computability.BorderVNP.CrossingDescent

/-!
# Paying for a crossing over the formal parameter ring

The shortening tables have entries in the gadget field. The old network
can have parameter monomials as entries. Replacing a group of its wires
keeps all the old local tables, records the positions selected in the new
gadget tables, and preserves the contracted polynomial after interpreting
the gadget counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening MvPolynomial
open scoped BigOperators Classical

variable {D m j : ℕ} {P : Type*} {bits : P → ℕ} {E Param Gadget : Type*} [Field E]

/-- Interpret every local counter record as a parameter-ring polynomial. -/
noncomputable def interpretPack (values : Gadget → E) (p : Pack D P bits (Entry Param Gadget)) :
    Pack D P bits (MvPolynomial Param E) :=
  ⟨p.layout, fun v a x => interpret values (p.table v a x)⟩

/-- Local profile tables retain the *one-copy entry addresses*, even when
many equal entries occur or an entry happens to vanish after specialization. -/
noncomputable def profileTags (e : PaidIdentity E D m) (position : e.Entry → Gadget)
    (j : ℕ) (p : Fin e.count → ℕ) (first : Fin D × Bool) :
    (e.profile j p).Tables (Entry Param Gadget) :=
  Profile.tables e.net antipodalPosition
    (fun v => by obtain ⟨i,b⟩ := v; cases b <;> simp [antipodalPosition]) j p first
    (fun a v z x => gadget (position ⟨a,v,z,x⟩))

/-- The interpreted tagged profile is the original field-valued profile
extended as constants to the polynomial ring. -/
theorem interpret_profileTags (e : PaidIdentity E D m) (position : e.Entry → Gadget)
    (values : Gadget → E) (lookup : ∀ i, values (position i) = e.entry i)
    (j : ℕ) (p : Fin e.count → ℕ) (first : Fin D × Bool) (v : (e.profile j p).Site) (z x) :
    interpret values (profileTags (Param := Param) e position j p first v z x) =
      C (e.profileTables j p first v z x) := by
  let bound (v : Fin D × Bool) : ‖antipodalPosition v‖ ≤ 1 := by
    obtain ⟨i,b⟩ := v; cases b <;> simp [antipodalPosition]
  let tags (a) : (e.net a).Tables (Entry Param Gadget) := fun v z x => gadget (position ⟨a,v,z,x⟩)
  have h₁ := Profile.map_tables e.net antipodalPosition bound j p first tags
    (interpret values) v z x
  have h₂ := Profile.map_tables e.net antipodalPosition bound j p first e.table
    (C : E →+* MvPolynomial Param E).toMonoidWithZeroHom v z x
  refine h₁.trans (?_ : _ = _)
  apply Eq.trans _ h₂.symm
  have he (a) (v : (e.net a).Site) (z x) :
      interpret values (tags a v z x) = C (e.table a v z x) := by
    change interpret values (gadget (position ⟨a,v,z,x⟩)) = _
    rw [interpret_gadget, lookup]; rfl
  simp only [he]
  rfl

/-- All public histogram choices and each corresponding tagged output.
The original site's tagged factor remains at the exterior of the cut. -/
noncomputable def replace (src : Pack D P bits (Entry Param Gadget))
    (S : Finset src.layout.Edge) (bundle : Bundle src.layout S (j*m))
    (e : PaidIdentity E D m) (position : e.Entry → Gadget) (hist : Fin e.count → ℕ)
    (first : Fin D × Bool) : Pack D P bits (Entry Param Gadget) :=
  let O := src.layout.cut S
  let G := bundle.expose (e.profile j hist)
  ⟨O.sew G, O.sewTables G (src.layout.cutTables S src.table)
    (bundle.exposeTables _ (profileTags e position j hist first))⟩

/-- The concrete cable replacement is an ordinary sum over the attained
histograms *in the polynomial ring*. It therefore remains valid for
substituted batches containing original unary powers with poles. -/
theorem value_replacements (src : Pack D P bits (Entry Param Gadget))
    (S : Finset src.layout.Edge) (bundle : Bundle src.layout S (j*m))
    (e : PaidIdentity E D m) (position : e.Entry → Gadget) (first : Fin D × Bool)
    (values : Gadget → E) (lookup : ∀ i, values (position i) = e.entry i) (x : Ports bits) :
    (interpretPack values src).tensor x =
      ∑ h ∈ Finset.univ.image (@Profile.histogram e.count j),
        (interpretPack values (replace src S bundle e position h first)).tensor x := by
  let H := Finset.univ.image (@Profile.histogram e.count j)
  let prof (h : ↥H) := bundle.expose (e.profile j h.val)
  let scalar (h : ↥H) := bundle.exposeTables (e.profile j h.val) (e.profileTables j h.val first)
  let inner (h : ↥H) : (prof h).Tables (MvPolynomial Param E) := fun v a z => C (scalar h v a z)
  have fieldJoint (s : Ports (src.layout.cutWidths S)) :
      src.layout.cutEquality (R := E) S s = ∑ h : ↥H, (prof h).value (scalar h) s := by
    rw [bundle.cutEquality_gather]
    simp only [prof, scalar, Bundle.value_expose]
    exact (e.profile_sum j first (bundle.gather s)).symm.trans (Finset.sum_coe_sort H _).symm
  have joint (s : Ports (src.layout.cutWidths S)) :
      src.layout.cutEquality (R := MvPolynomial Param E) S s = ∑ h : ↥H, (prof h).value (inner h) s := by
    have eq := congrArg (C : E →+* MvPolynomial Param E) (fieldJoint s)
    simpa only [Network.cutEquality, apply_ite C, map_one, map_zero, map_sum, map_prod,
      Network.value, Network.read, inner] using eq
  have h := src.layout.value_replace S (interpretPack values src).table prof inner joint x
  rw [← Finset.sum_coe_sort H]
  refine h.trans (Finset.sum_congr rfl fun t _ => ?_)
  let O := src.layout.cut S
  apply congrArg (fun tab : (O.sew (prof t)).Tables (MvPolynomial Param E) =>
    (O.sew (prof t)).value tab x)
  funext v z a
  cases v with
  | inl v => rfl
  | inr v =>
    change C (e.profileTables j t.val first v _ _) = interpret values (profileTags e position j t.val first v _ _)
    exact (interpret_profileTags e position values lookup j t.val first v _ _).symm

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
