import OAI.Computability.BorderVNP.CubeTableSpecialization
import OAI.Computability.BorderVNP.DiagonalCellEntries
import OAI.Computability.VPVNP.RAMSerialization

/-!
# Realizing the cube identity as tagged physical bit networks

For one packet of §8.2, the two external words of an antipodal pair
are attached to their respective cube vertices. Every supplied edge
has one shared bit word, even when several incident half-edge indices
occur in the local matrix notation. The labels name individual matrix
positions and therefore retain the multiplicities required in §11.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

open Crossing VPVNP.WireTensor VPVNP.MotifBase VPVNP.RAMSerialization
open Diagonal.CellEntries MvPolynomial
open scoped BigOperators Classical

variable {n b h K s D : ℕ}

/-- External ends of the antipodal pairs in an individual packet. -/
abbrev Ends (n : ℕ) := Vertex n × Bool

/-- In a selected term the only internal cables are the cube edges. Width zero
still has one possible word and contributes no communication cost. -/
def packetNetwork (D b s : ℕ) (u : Selector n K h) :
    Network D (Ends n) (fun _ => h*b) where
  Site := Vertex (n+1)
  Edge := Edge (n+1)
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := Prod.fst
  dst := head
  width := payload (onEdge s) u.2
  attach := fun p => if p.2 then stop p.1 else start p.1
  position := fun _ => 0
  in_ball := by simp

private def demandInput (x : Ports (fun _ : Ends n => h*b)) (v : Vertex (n+1)) :
    DemandBasis n b h v :=
  ⟨fun e _ => (wordBits _).symm (x (e,false)), fun e _ => (wordBits _).symm (x (e,true))⟩

/-- Read the matrix entry identified by the external antipodal words and
the local incident cube cables. -/
def packetTables {A : Type*} (label : TableEntry n b h K s → A) (D : ℕ)
    (u : Selector n K h) : (packetNetwork D b s u).Tables A := fun v y x =>
  label ⟨u, v,
    ⟨fun e hv => (wordBits _).symm (x ⟨(e,false), hv.symm⟩),
      fun e hv => (wordBits _).symm (x ⟨(e,true), hv.symm⟩)⟩,
    ⟨fun e hv => (wordBits _).symm (y ⟨e, Or.inl hv.symm⟩),
      fun e hv => (wordBits _).symm (y ⟨e, Or.inr hv.symm⟩)⟩⟩

variable {E : Type*} [CommRing E]

/-- The tensor contraction for a selected term is exactly the indicated
local linear map on the supply tensor. This reindexes the actual bit-word
assignments using the integer basis `Fin (2^width)`. -/
theorem packet_value (table : TableEntry n b h K s → E) (D : ℕ) (u : Selector n K h)
    (x : Ports (fun _ : Ends n => h*b)) :
    (packetNetwork D b s u).value (packetTables table D u) x =
      ∑ z : (e : Edge (n+1)) → Fin (2 ^ payload (onEdge s) u.2 e),
        ∏ v, table ⟨u,v,demandInput x v,edgeAssignment Prod.fst head z v⟩ := by
  let code : (packetNetwork D b s u).Assignment ≃
      (∀ e, Fin (2 ^ payload (onEdge s) u.2 e)) :=
    Equiv.piCongrRight fun _ => (wordBits _).symm
  exact Fintype.sum_equiv code _ _ fun _ => rfl

/-- A single packet, after ordinary summation over its selectors, realizes
exactly its antipodal equality checks. -/
theorem packet_sum (table : TableEntry n b h K s → E) (ht : ValidTables table) (D : ℕ)
    (x : Ports (fun _ : Ends n => h*b)) :
    (∑ u, (packetNetwork D b s u).value (packetTables table D u) x) =
      ∏ e : Vertex n, if x (e,false) = x (e,true) then 1 else 0 := by
  simp_rw [packet_value]
  refine (ht.read (demandInput x)).trans ?_
  simp only [demandInput, Equiv.apply_eq_iff_eq]

/-- Label every selected position with one gadget-count event. Interpreting
the tagged contraction yields the cube identity over the formal parameter
ring, without evaluating the parameter variables. -/
theorem packet_sum_tagged {Param Gadget : Type*} (pos : TableEntry n b h K s → Gadget)
    (values : Gadget → E) (ht : ValidTables (values ∘ pos)) (D : ℕ)
    (x : Ports (fun _ : Ends n => h*b)) :
    (∑ u : Selector n K h, ∑ z : (packetNetwork D b s u).Assignment,
      interpret values (assignmentEntry (packetNetwork D b s u)
        (packetTables (fun i => gadget (Param := Param) (pos i)) D u) z x)) =
      ∏ e : Vertex n, if x (e,false) = x (e,true) then 1 else 0 := by
  have h := congrArg (C : E →+* MvPolynomial Param E) (packet_sum (values ∘ pos) ht D x)
  simpa only [Network.value, Network.read, assignmentEntry, packetTables, map_sum, map_prod,
    interpret_gadget, apply_ite C, map_one, map_zero, Function.comp_apply] using h

end Cube

end BorderVNP
end Computability
end OAI
