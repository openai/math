import OAI.Computability.BorderVNP.FiniteEvaluatorCubeJointDictionary
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeBanksInputs

/-! # Routed finite-field cube terms and complete native return tuples

The flat cell work, selectors and common crossing suffixes are fixed. Varying
the private packet/singleton assignment runs through exactly the true team
histories. Their addressed cube entries multiply to the factor in the opened
field path, including for zero-valued entries and empty local directories.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.FieldRawLayout

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.Tally
open Padding.Banks FiniteEvaluator RoutingISA VPVNP.BurstRAM
open scoped Classical BigOperators

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable (V : FieldRawLayout L S) (R : ℕ) (raw : V.Raw R)

/-- Replace the distributed private fiber in the concrete raw path while
retaining the original selected tuple, observed common words and flat cell work. -/
def withPrivate (f : CubeTriple.Fiber raw.1.2) : V.Raw R := (⟨raw.1.1,f.val⟩,raw.2)

variable (layout : Fin (R+1) → TeamRowPrepare.Layout)
variable (packet single power base stop actual claimed : Fin (R+1) → ℕ)
variable (rows : Sym2 (Fin L.alphabet) → Fin (L.dimension+1) → ℕ) (pub : Fin (R+1) → Arg → Word w)
variable (mac : Fin (R+1) → TeamOpcode.Macros w 8) (initialRegs : Fin (R+1) → Bank w) (initial : Fin (R+1) → Memory w)

local notation "axis" => chosen L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "teamOwner" => V.owners R (Sigma.fst (Prod.fst raw))
local notation "number" => Fin.val ∘ teamOwner
local notation "scan" => CubeTriple.teamLayout layout (Fin.valEmbedding : Fin (R+1) ↪ ℕ) L.alphabet
local notation "enc" => nativeWordsEquiv L.bitWidth L.supply (Sigma.fst (Prod.fst raw)) axis teamOwner

/-- On the actual observed public setup the field path's private payload fiber
is in bijection with all returning owned-group histories, retaining each
physical address, incident bank word, selected cube factor, and measured bound. -/
theorem native_owned_dictionary
    (setup : ∀ t, TeamRows.PhysicalSetup (l := scan t) (V.bankData R raw (packet t) (single t)) number
      (power t) (base t) (stop t) (actual t) (claimed t) rows (pub t) (initial t)) :
    ∃ E : CubeTriple.Fiber raw.1.2 ≃ CubeTriple.Histories pub mac initialRegs initial L.dimension L.bitWidth L.copies L.alternatives L.supply,
      ∀ f, let next := V.withPrivate R raw f
        ((∀ t, let out := E f t
          let A := V.bankData R next (packet t) (single t)
          DiagonalResidueRAM.TraceOK out.val.1 (((enc f.val).2 t).val) out.val.1.length ∧
          traceCost out.val.1 ≤ 4+(TeamRows.ticks (scan t) (TeamRows.wordOwner number)
            (TeamRows.physicalCostAt (scan t) L.blocks L.bitWidth L.copies L.alternatives L.supply axis)+11) ∧
          CubeTriple.Readback (l := scan t) A number (power t) (base t) (stop t) (initial t) out.val.2.2 ∧
          ∀ j : Fin (V.teamPairs R next t).length, let z := V.teamVisit R next (packet t) t j
            z.tripleAt (readings out.val.2.2) (base t+3*j.val) ∧ VertexAt out.val.2.2 z.base z.selector z.vertex z.ends z.supply) ∧
          ∏ t : Fin (R+1), ∏ j : Fin (V.teamPairs R next t).length, V.teamEntry R next (packet t) t j =
            cubeTermWeight L.table (fun _ _ => 1) (V.read R next).2.2) := by
  obtain ⟨E,works⟩ := CubeTriple.assignment_dictionary ⟨Fin.val,Fin.val_injective⟩ layout packet single power base stop actual claimed
    rows pub mac initialRegs initial raw.1.2 setup
  refine ⟨E,fun f => ?_⟩
  let next := V.withPrivate R raw f
  refine ⟨fun t => ?_,V.team_entries R next packet⟩
  obtain ⟨trace,cost,read⟩ := works f t
  refine ⟨trace,cost,read,fun j => ?_⟩
  have tri := V.team_triples R next t (packet t) (single t) (base t) _ read.triples
  have views (x : View L.dimension L.alphabet L.blocks (L.copies*L.bitWidth)) (own : V.owners R next.1.1 (x.row axis).1=t) :
      (V.bankData R next (packet t) (single t)).Holds (E f t).val.2.2 x := by
    apply read.views x
    exact congrArg Fin.val own
  exact ⟨tri j,V.team_banks R next (packet t) (single t) _ t views j⟩

end FiniteDiagonal.FieldRawLayout

end BorderVNP
end Computability
end OAI
