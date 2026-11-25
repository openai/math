import OAI.Hierarchy.DescentOutgoingLoad
import OAI.Hierarchy.DescentStarRoster
import OAI.Hierarchy.DescentNativeNeighbors

namespace OAI
/-! # The paid-gain bound at each genuine occupied star -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentHostDegree GadgetNetwork
open scoped Classical BigOperators
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {n k : ℕ} {P : Type*} {bits : P→ℕ}
    (N : Network n P bits) (pos : N.Site→V) (block : N.Site→Block k)
    (carried : N.Site→ℕ) (near : V→Finset V) (a₀ Δ B : ℕ)
private abbrev paidSiteLoad (u : N.Site) := siteLoad N u + carried u
private abbrev paidBlockMass := blockMass N pos block (paidSiteLoad N carried)
variable (small : ∀ (v : V) (x : Block k), paidBlockMass N pos block carried v x ≤ B)
private abbrev paidHome := occupiedHome N pos block (paidSiteLoad N carried) near
  (gap Δ) (packExponent a₀ Δ) B small

local notation "full" => paidSiteLoad N carried
local notation "A" => packExponent a₀ Δ
local notation "D" => gap Δ
local notation "load" => paidBlockMass N pos block carried
local notation "home" => paidHome N pos block carried near a₀ Δ B small
local notation "Col" => occupied N B near (gap Δ) (packExponent a₀ Δ) (paidBlockMass N pos block carried) small pos block
local notation "col" => occupiedAddress N B near (gap Δ) (packExponent a₀ Δ) (paidBlockMass N pos block carried) small pos block
variable (core : Finset N.Edge) (sheet : Block k→Bool)
local notation "paint" => (sheet ∘ block)
local notation "pack" => coloredPack N core (paidHome N pos block carried near a₀ Δ B small) (sheet ∘ block) B
local notation "pick" => colorPick N core (paidHome N pos block carried near a₀ Δ B small) (sheet ∘ block) B
local notation "Pairs" => NativePair N core (paidHome N pos block carried near a₀ Δ B small) (sheet ∘ block) B

set_option Elab.async false in
omit [Fintype V] in
/-- Slot count, matching routes, roster size and all old pack loads are derived
from the physical core and its occupied dyadic colonies. -/
theorem occupied_gain {F : Type*} [Field F] (G : PoweredGadget F) (l : Bool)
    (positive : 0<B) (degree : ∀v,(near v).card≤Δ)
    (unit : ∀e∈core, 1 ≤ N.width e)
    (adj : ∀e∈core,pos (N.dst e)∈near (pos (N.src e)) ∧ pos (N.src e)∈near (pos (N.dst e)))
    (sameBlock : ∀e∈core,block (N.src e)=block (N.dst e)) (z : Pairs→ℕ) (p : Pairs→Profile G.C)
    (fit : ∀i s,N.width (pick (i,s))=z i*G.b) {d : ℕ}
    (position : Merged N pick l pack→EuclideanSpace ℝ (Fin d)) (ball : ∀q,‖position q‖≤1)
    (v : Merged N pick l pack) :
    let w : Pairs → Fin 8 → ℕ := fun i e => z i * (((p i).1 e).val + G.k)
    2*(siteLoad (merged N pick w l pack position ball) v+
      ∑u : {u : N.Site // newSite N pick l pack (.inl u)=v},carried u.val)≤2^gainExponent a₀ Δ*B := by
  let allow : Col → Finset Col := oneNeighbor near D col
  have colors (e) (he : e∈core) : paint (N.src e)=paint (N.dst e) := congrArg sheet (sameBlock e he)
  refine native_paid_gain N core home paint B allow colors l G (oneNeighbor_self near D col) ?_
    a₀ Δ positive ?_ ?_ carried ?_ z p fit position ball v
  · intro e he
    exact actual_neighbor N B near D A load small pos block (adj e he).2 (adj e he).1 (sameBlock e he)
  · intro c
    apply (oneNeighbor_card near D Δ col degree c).trans
    exact Nat.le_add_left _ _
  · intro c
    exact (thin_le_fiber N core home paint full unit (fun u=>Nat.le_add_right ..) c).trans
      (occupied_mass N pos block full near D A B small c)
  · intro c
    have mass := full_pack_mass N pos block full near D A B small paint core c
    rw [Finset.sum_filter] at mass
    refine le_trans ?_ mass
    apply Finset.sum_le_sum
    intro u _
    exact le_of_eq (@ite_cond_congr ℕ _ _
      (inferInstanceAs (Decidable (pack u = c))) (Classical.propDecidable (pack u = c)) _ _ rfl)

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
