import OAI.Computability.BorderVNP.DiagonalSubstitution
import OAI.Computability.BorderVNP.FiniteOutputProduct
import OAI.Computability.BorderVNP.PackedProfiles
import OAI.Computability.BorderVNP.PackedCells
import OAI.Computability.BorderVNP.RoutingMessages

/-! # Exact finite-field contractions in §§7–8

The live contraction uses the actual field-valued universal program. A proposed
batch network is substituted at the same exterior slots but summed with an
independent internal assignment. Through adaptive packing the substituted
value becomes the sum of products of the contracted cell tables. Each routed
assignment of a fixed expansion term is counted once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open Crossing Packing Diagonal
open VPVNP.RAMTape VPVNP.UniversalMachine Filter
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]

/-- The batched finite-field tensor of Theorem 3.4, as a bit tensor with one
external port per processor input bit. -/
noncomputable def tensorPower (F : Type*) [Field F] [Fintype F] (n r : ℕ)
    (x : Ports (fun _ : Fin r × Fin n => 1)) : F :=
  ∏ j : Fin r, FPath.U F (fun i => x (j,i) 0)

/-- Restrict the exterior bits of a recursively packed network to a particular
original copy. The remaining indices are its original terminal types and widths. -/
def copyPorts {P : Type} {bits : P → ℕ} (b K : ℕ) : (t : ℕ) →
    Ports (packWidth bits b K t) → PackPorts Unit b K t → Ports bits
  | 0, x, i => fun p => x (i.1,p)
  | t+1, x, i => copyPorts b K t (fun p => x (i.1,p)) i.2

omit [Fintype F] in
/-- Original copies inside a pack have independent internal indices. -/
theorem unshortened_copies {P : Type} {bits : P → ℕ} {D : ℕ}
    (B : ValuedPack F D bits) (b K t : ℕ) (x : Ports (packWidth bits b K t)) :
    (unshortened B b K t).tensor x =
      ∏ i : PackPorts Unit b K t, B.tensor (copyPorts b K t x i) := by
  induction t with
  | zero =>
    calc
      _ = ∏ i : Fin b, B.tensor (fun p => x (i,p)) :=
        Network.parallel_value (fun _ : Fin b => B.1) (fun _ => B.2) x
      _ = _ := by
        change _ = ∏ i : Fin b × Unit, B.tensor (fun p => x (i.1,p))
        rw [Fintype.prod_prod_type]
        simp
  | succ t ih =>
    calc
      _ = ∏ i : Fin K, (unshortened B b K t).tensor (fun p => x (i,p)) :=
        Network.parallel_value (fun _ : Fin K => (unshortened B b K t).1)
          (fun _ => (unshortened B b K t).2) x
      _ = _ := by
        change _ = ∏ i : Fin K × PackPorts Unit b K t, B.tensor (copyPorts b K t (fun p => x (i.1,p)) i.2)
        rw [Fintype.prod_prod_type]
        exact Finset.prod_congr rfl fun i _ => ih (fun p => x (i,p))

variable {n r D b K : ℕ}
private abbrev unitBits (n r : ℕ) := fun _ : Fin r × Fin n => 1

/-- With one bit assignment for the shared live links, the exterior values of each
original network copy can be read by the same physical pin layout. -/
noncomputable def live {Wire : Type*} [Fintype Wire] (t : ℕ)
    (inputs : (Wire → Bool) → Ports (packWidth (unitBits n r) b K t)) : F :=
  ∑ links, ∏ team : PackPorts Unit b K t, tensorPower F n r (copyPorts b K t (inputs links) team)

/-- Substituting a network for each team preserves the live scalar contraction
if and only insofar as the network is used on inputs where the batched identity holds. -/
theorem live_eq_substituted {Wire : Type*} [Fintype Wire] (t : ℕ)
    (B : ValuedPack F D (unitBits n r))
    (computes : ∀ x, B.tensor x = tensorPower F n r x)
    (inputs : (Wire → Bool) → Ports (packWidth (unitBits n r) b K t)) :
    live t inputs = ∑ substitutedLinks, (unshortened B b K t).tensor (inputs substitutedLinks) := by
  apply Finset.sum_congr rfl
  intro links _
  rw [unshortened_copies]
  exact Finset.prod_congr rfl fun _ _ => (computes _).symm

/-- The exact adaptive history and its independently assigned cell interiors give
the substituted value in the finite-field model. No invertibility of any local
entry, including zero weights, is required. -/
theorem live_eq_cell_expansion {Wire Cell : Type} [Fintype Wire] [Fintype Cell] [DecidableEq Cell]
    (B : ValuedPack F D (unitBits n r)) (computes : ∀ x, B.tensor x = tensorPower F n r x)
    (t : ℕ) (select : ∀ l (child : Fin K → ValuedPack F D (packWidth (unitBits n r) b K l)),
      Shortening.History (parallelPacks child))
    (inputs : (Wire → Bool) → Ports (packWidth (unitBits n r) b K t)) :
    let epoch := fun l child => replacementProfiles (select l child)
    let H := packHistory (unshortened B b K 0) epoch t
    ∀ (cells : (h : H.Index) → (H.term h).1.Site → Cell)
      (pos : Cell → {x : EuclideanSpace ℝ (Fin D) // ‖x‖ ≤ 1}),
    live t inputs = ∑ links, ∑ h : H.Index,
      let pack := H.term h
      (pack.1.cellNetwork (cells h) pos).value (pack.1.cellTables (cells h) pos pack.2) (inputs links) := by
  intro epoch H cells pos
  rw [live_eq_substituted t B computes]
  apply Finset.sum_congr rfl
  intro links _
  rw [show (unshortened B b K t).tensor (inputs links) =
      ∑ h : H.Index, (H.term h).tensor (inputs links) from
    value_packHistory B epoch (exactEpoch_of_replacements select) t (inputs links)]
  exact Finset.sum_congr rfl fun h _ => (Network.value_cellNetwork _ _ _ _ _).symm

omit [Fintype F] in
/-- The routed header, two checked hops, and padding have exactly one compatible
physical assignment for each fixed contraction term. This also counts the unit term
with its single all-zero padding assignment. -/
theorem sum_routed {R : ℕ} (hR : 2 < R) (width : Fin R → Fin R → ℕ)
    {Header Pad : Type*}
    [Fintype (Routing.Messages hR width Header Pad)] (fixed : Routing.Block R)
    (header : Header) (high payload : Fin R → Fin R → ℕ → Bool) (v : F) :
    (∑ m : Routing.Messages hR width Header Pad,
      if Routing.Checks hR width fixed header high payload m then v else 0) = v := by
  obtain ⟨chosen,ok,unique⟩ := Routing.existsUnique_messages (Pad := Pad) hR width fixed header high payload
  have he m : Routing.Checks hR width fixed header high payload m ↔ m = chosen :=
    ⟨unique m, fun h => h ▸ ok⟩
  simp [he]

/-- Compile one weighted validator for every processor, with its own literal prefix
in the physical input, then evaluate the product over all team and link choices. -/
theorem native_contraction {Port State : Type} [DecidableEq Port] [Fintype Port] [Fintype State]
    (input : Port) (u : ℕ) (hu : 1 ≤ u) (hexp : 2*(u+2)+1 ≤ 100)
    (code : StackCode Port State) (factor terminal : State → F) (start : State) :
    ∃ program : Program, ∀ᶠ n : ℕ in atTop, ∀ (Wire Proc : Type) [Fintype Wire] [Fintype Proc]
      (layout : Proc → Fin n → InputSlot Empty Wire) (tails : Proc → List (InputSlot Empty Wire)),
      (∀ s, List.ofFn (layout s) = (programPrefix program).map InputSlot.literal ++ tails s) →
      (∑ links, ∏ proc, FPath.U F (fun j => (layout proc j).read Empty.elim links)) =
      ∑ links, ∏ proc, FieldStack.productPaths code factor terminal (n^u) start
        (StackCompiler.labeledInput input
          (programPrefix program ++ (tails proc).map (InputSlot.read Empty.elim links))) := by
  obtain ⟨program,hprog⟩ := FieldStack.eventually_product_program input u hu hexp code factor terminal start
  refine ⟨program,?_⟩
  filter_upwards [hprog] with n hn
  intro Wire Proc _ _ layout tails hprefix
  refine Finset.sum_congr rfl fun links _ => Finset.prod_congr rfl fun s _ => ?_
  let word := fun j => (layout s j).read Empty.elim links
  have hr : List.ofFn word = programPrefix program ++ (tails s).map (InputSlot.read Empty.elim links) := by
    change List.ofFn (InputSlot.read Empty.elim links ∘ layout s) = _
    rw [← List.map_ofFn, hprefix s, List.map_append, List.map_map]
    simp [InputSlot.read, Function.comp_def]
  have hlen := congrArg List.length hr.symm
  rw [List.length_ofFn] at hlen
  have h := hn ((tails s).map (InputSlot.read Empty.elim links)) hlen
  rw [← hr] at h ⊢
  change FPath.U F (List.ofFn word).get = _ at h
  simpa only [FPath.U_eq_paths, List.ofFn_get, List.length_ofFn, List.get_ofFn, Fin.cast_cast, Fin.cast_eq_self] using h

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
