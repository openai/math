import OAI.Computability.BorderVNP.DiagonalPowerWords
import OAI.Computability.BorderVNP.DiagonalPowerTransport
import OAI.Computability.BorderVNP.ShortenCombiningStep

/-! # The parameter-ring identity and use-bit readback for simultaneous seed profiles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening MvPolynomial
open scoped BigOperators Classical

variable {D m b : ℕ} {P : Type*} {bits : P → ℕ} {E Param Gadget Team : Type*}
    [Field E] {A : Type} [Fintype A]
variable (src : Pack D P bits (Entry Param Gadget)) (e : PaidIdentity E D m)
    (position : e.Entry → Gadget) (j : A → ℕ) (t : AddressPartition src.layout A)
    (bundle : ∀ a, Bundle src.layout (t.part a) (j a*m)) (first : Fin D × Bool)
    (q : ProfileCounts e j)

/-- Network of all selected profiles, attached to the cut in seed order. -/
noncomputable abbrev seedLayout :=
  t.parallel (fun a => (bundle a).expose (e.profile (j a) (q a).val))

/-- Each local bank reads and counts its concrete one-copy gadget positions. -/
noncomputable def seedInner :
    (seedLayout src e j t bundle q).Tables (Entry Param Gadget) :=
  t.parallelTables _ (fun a => (bundle a).exposeTables _
    (profileTags e position (j a) (q a).val first))

/-- Physical result of the simultaneous replacement, indexed directly by
the attained public histogram at each seed. -/
noncomputable def seedTags : Pack D P bits (Entry Param Gadget) :=
  let O := src.layout.cut t.selected
  let G := seedLayout src e j t bundle q
  ⟨O.sew G, O.sewTables G (src.layout.cutTables t.selected src.table)
    (seedInner src e position j t bundle first q)⟩

/-- A source's grouped unary labels survive every public histogram insertion. -/
noncomputable def seedWords [Fintype Team] [Fintype Param]
    (words : PowerWords Team Param Gadget b src.layout src.table) :
    PowerWords Team Param Gadget b (seedTags src e position j t bundle first q).layout
      (seedTags src e position j t bundle first q).table :=
  words.cutSew t.selected _ _ (fun ⟨a,v⟩ _ _ =>
    profile_noPower e position (j a) (q a).val first v _ _)

/-- For every choice of private fine variables, specialization of the true
field-valued seed identities gives an exact polynomial sum. In particular,
the weighted unary positions remain formal throughout the adaptive construction. -/
theorem sum_seedTags (values : Gadget → E) (lookup : ∀ i, values (position i) = e.entry i)
    (x : Ports bits) :
    (interpretPack values src).tensor x =
      ∑ q : ProfileCounts e j, (interpretPack values (seedTags src e position j t bundle first q)).tensor x := by
  let empty : Pack D P bits E := ⟨src.layout, fun _ _ _ => 0⟩
  let G := seedLayout src e j t bundle
  let scalar (h : ProfileCounts e j) : (G h).Tables E :=
    t.parallelTables _ (seedTables e j (p := empty) t bundle first h)
  let inner (h : ProfileCounts e j) : (G h).Tables (MvPolynomial Param E) :=
    fun v z y => C (scalar h v z y)
  have field (s : Ports (src.layout.cutWidths t.selected)) :
      src.layout.cutEquality t.selected s = ∑ h, (G h).value (scalar h) s :=
    sum_seedNetworks e j (p := empty) t bundle first s
  have joint (s : Ports (src.layout.cutWidths t.selected)) :
      src.layout.cutEquality (R := MvPolynomial Param E) t.selected s =
        ∑ h, (G h).value (inner h) s := by
    have eq := congrArg (C : E →+* MvPolynomial Param E) (field s)
    simpa only [Network.cutEquality, apply_ite C, map_one, map_zero, map_sum, map_prod,
      Network.value, Network.read, inner] using eq
  refine (src.layout.value_replace t.selected (interpretPack values src).table G inner joint x).trans ?_
  apply Finset.sum_congr rfl
  intro h _
  apply congrArg (fun tab : ((src.layout.cut t.selected).sew (G h)).Tables (MvPolynomial Param E) =>
    ((src.layout.cut t.selected).sew (G h)).value tab x)
  funext v z y
  rcases v with old | ⟨a,w⟩
  · rfl
  · exact (interpret_profileTags e position values lookup (j a) (h a).val first w _ _).symm

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
