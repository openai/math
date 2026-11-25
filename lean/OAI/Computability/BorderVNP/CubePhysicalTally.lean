import OAI.Computability.BorderVNP.CubePhysicalContraction
import OAI.Computability.BorderVNP.CubePhysicalDeclaration
import OAI.Computability.BorderVNP.DiagonalPowerWords

/-! # Team-owned parameter and gadget tallies for an actual cube path

A weighted host site can hold several original parameter occurrences. All
of them are read from the separated end words. The chosen cube entries add
only scalar multiplicities, at the team owning their concrete product-alphabet
label. Reconstructing the team tallies recovers the polynomial weight of
each passing path, including paths with a zero-valued selected table entry.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal Diagonal.CellEntries MvPolynomial
open scoped Classical

set_option synthInstance.maxSize 768

variable {n d blocks b h K s D B : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable {Team Param Gadget E : Type*} [Fintype Team] [Fintype Param] [Fintype Gadget] [Field E]
variable {N : Network D P bits} {cell : N.Site → Cell}
variable (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (tags : N.Tables (Entry Param Gadget))
variable (x : Ports bits) (pos : Packet n d blocks → TableEntry n b h K s → Gadget)

/-- Independent original host-site cable words read on the path. -/
noncomputable def pathEdges (a : Path N cell n d blocks b h K s) : PowerSites.LocalEdges N :=
  fun v i => siteWord N cell v i a.1 (fun dir bit => readEnd a.2.1 a.2.2.1 dir (slot bit))

/-- The chosen scalar event at one packet and one cube vertex. -/
noncomputable def pathExtra (a : Path N cell n d blocks b h K s)
    (pv : Packet n d blocks × Vertex (n+1)) : Entry Param Gadget :=
  (packetNetwork D b s (a.2.2.2.1 pv.1)).read
    (packetTables (fun g => gadget (Param := Param) (pos pv.1 g)) D (a.2.2.2.1 pv.1))
    (a.2.2.2.2 pv.1) (a.2.2.1 pv.1) pv.2

omit [Fintype Cell] [DecidableEq Cell] [Fintype Param] [Fintype Gadget] in
private theorem pathExtra_scalar (a : Path N cell n d blocks b h K s)
    (pv : Packet n d blocks × Vertex (n+1)) : (counters (pathExtra (Param := Param) pos a pv)).1 = 0 := rfl

omit [Fintype Param] [Fintype Gadget] in
/-- A passing path has exactly the product of its original cell factors
and the individual selected cube-position tags. -/
theorem pathTag_eq_product (a : Path N cell n d blocks b h K s)
    (hpass : pathTag N cell slot tags x pos a ≠ 0) :
    pathTag N cell slot tags x pos a =
      (∏ v, tags v (pathEdges slot a v) (fun p => x p.val)) * ∏ pv, pathExtra pos a pv := by
  have eq : ∏ pv, pathExtra (Param := Param) pos a pv =
      ∏ i, assignmentEntry (packetNetwork D b s (a.2.2.2.1 i))
        (packetTables (fun g => gadget (Param := Param) (pos i g)) D (a.2.2.2.1 i))
        (a.2.2.2.2 i) (a.2.2.1 i) := Fintype.prod_prod_type _
  rw [eq]
  unfold pathTag globalEntry host at hpass ⊢
  split_ifs at hpass ⊢
  · exact congrArg (· * _) (Fintype.prod_fiberwise cell (fun v => tags v (pathEdges slot a v) (fun p => x p.val)))
  · simp at hpass

/-- Ownership of the actual physical factors for the chosen minimizing
coordinate. Both an original cell site and a cube vertex route by their
symbol in that coordinate. -/
def pathOwner (label : Cell → Label (n+1) d) (team : Fin d → Team)
    (a : Path N cell n d blocks b h K s) : N.Site ⊕ (Packet n d blocks × Vertex (n+1)) → Team :=
  let i := chosen b s a.2.2.2.1
  Sum.elim (fun v => team (label (cell v) i)) (fun pv => team (vertexLabel pv.1 pv.2 i))

variable (words : PowerWords Team Param Gadget B N tags)
variable (label : Cell → Label (n+1) d) (team : Fin d → Team)

/-- Distributed tallies, using precisely one slot for each original weighted
occurrence, even when several occur in the same packed host box. -/
noncomputable def pathTally (a : Path N cell n d blocks b h K s) : Tally Team Param Gadget B :=
  words.localTally (pathEdges slot a) (fun _ p => x p.val) (pathExtra pos a) (pathOwner label team a)

/-- Each passing path's polynomial is the monomial reconstructed from its
team-owned multiplicities and original binary power choices. -/
theorem interpret_path_tally (values : Gadget → E) (a : Path N cell n d blocks b h K s)
    (hpass : pathTag N cell slot tags x pos a ≠ 0) :
    interpret values (pathTag N cell slot tags x pos a) =
      monomial (pathTally slot tags x pos words label team a).exponents
        ((pathTally slot tags x pos words label team a).coefficient values) := by
  have eq := pathTag_eq_product slot tags x pos a hpass
  rw [eq]
  exact words.interpret_local_product (pathEdges slot a) (fun _ p => x p.val) (pathExtra pos a)
    (pathOwner label team a) values (pathExtra_scalar pos a) (eq ▸ hpass)

/-- The actual polynomial contraction as the passing, team-tallied path sum. -/
theorem value_eq_tallied_paths (values : Gadget → E) (ht : ∀ i, ValidTables (values ∘ pos i)) :
    N.value (fun v r p => interpret values (tags v r p)) x =
      ∑ a ∈ Finset.univ.filter (fun a => pathTag N cell slot tags x pos a ≠ 0),
        monomial (pathTally slot tags x pos words label team a).exponents
          ((pathTally slot tags x pos words label team a).coefficient values) := by
  rw [value_eq_physical_paths N cell slot tags x pos values ht, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hz : pathTag N cell slot tags x pos a = 0
  · simp [hz]
  · rw [ite_eq_left hz]
    exact interpret_path_tally slot tags x pos words label team values a hz

private theorem filters_same {A : Type*} (p : A → Prop) (d e : DecidablePred p) (i j : Fintype A) :
    @Finset.filter A p d (@Finset.univ A i) = @Finset.filter A p e (@Finset.univ A j) := by
  cases Subsingleton.elim d e
  cases Subsingleton.elim i j
  rfl

/-- The same expansion with the caller's enumeration of physical paths.
Enumerations arising from explicit public row orders and from abstract finite
networks agree on the finite set of accepted paths. -/
theorem value_eq_enumerated_tallies (values : Gadget → E) (ht : ∀ i, ValidTables (values ∘ pos i))
    (paths : Fintype (Path N cell n d blocks b h K s))
    (test : DecidablePred (fun a => pathTag N cell slot tags x pos a ≠ 0)) :
    N.value (fun v r p => interpret values (tags v r p)) x =
      ∑ a ∈ @Finset.filter _ (fun a => pathTag N cell slot tags x pos a ≠ 0) test (@Finset.univ _ paths),
        monomial (pathTally slot tags x pos words label team a).exponents
          ((pathTally slot tags x pos words label team a).coefficient values) := by
  refine (value_eq_tallied_paths slot tags x pos words label team values ht).trans ?_
  exact Finset.sum_congr (filters_same _ _ _ _ _) fun _ _ => rfl

end Cube.Physical

end BorderVNP
end Computability
end OAI
