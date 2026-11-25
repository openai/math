import OAI.Hierarchy.DescentSliceFields
import OAI.Hierarchy.DescentBundleQuotient

namespace OAI
/-! # Retained scalar tags and arities through rerouting and quotienting -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {p : ℕ} (hp : 0<p) {J H A A' Tag Fresh : Type} {B : J→Type} [Fintype J] [Fintype H]
variable {w : A→ℕ} {w' : A'→ℕ} {bw : (i:J)→B i→ℕ}
variable (r : ∀i,BitRecipe Tag (B i) (bw i)) (hw : H→ℕ)
    (route : ∀i, BitRef (bw i)→BitRef w ⊕ BitRef hw)
    (s : ∀i,Shape p (r i)) (multiple : ∀h,p∣hw h) (f : ∀i,PrivateMap p (bw i) w hw (route i))

theorem combined_tag (u : Σi,(r i).Node) :
    (((combined r hw route s multiple f).recipe hp).tag u)=((s u.1).recipe hp).tag u.2 := by
  exact (Shape.tag_fields hp (combined r hw route s multiple f) u).trans (Shape.tag_fields hp (s u.1) u.2).symm

theorem combined_arity (u : Σi,(r i).Node) :
    (((combined r hw route s multiple f).recipe hp).arity u)=((s u.1).recipe hp).arity u.2 := by
  exact (Shape.recipe_refs hp (combined r hw route s multiple f) u).trans (Shape.recipe_refs hp (s u.1) u.2).symm

theorem reroute_tag {r' : BitRecipe Tag A w} (t : Shape p r') {route' : BitRef w→BitRef w'}
    (f' : BlockMap p w w' route') (u : r'.Node) :
    ((t.reroute f').recipe hp).tag u=(t.recipe hp).tag u := by
  exact (Shape.tag_fields hp (t.reroute f') u).trans (Shape.tag_fields hp t u).symm

theorem reroute_arity {r' : BitRecipe Tag A w} (t : Shape p r') {route' : BitRef w→BitRef w'}
    (f' : BlockMap p w w' route') (u : r'.Node) :
    ((t.reroute f').recipe hp).arity u=(t.recipe hp).arity u := by
  exact (Shape.recipe_refs hp (t.reroute f') u).trans (Shape.recipe_refs hp t u).symm

theorem retag_field {r' : BitRecipe Tag A w} (s' : Shape p r') (f' : Tag→Fresh) (u : r'.Node) :
    ((s'.retag f').recipe hp).tag u=(f' (r'.tag u),s'.sliceFields u) := by
  exact Shape.tag_fields hp (s'.retag f') u

variable {F P C : Type} [Field F] [Fintype C] {d d' : ℕ} {bits : P→ℕ}
    (N : Network d P bits) (venue : N.Site→C) (center : C→EuclideanSpace ℝ (Fin d'))
    (within : ∀c,‖center c‖≤1) (history : SiteBits (U:=Tag) N)
    (bundle : ∀v,Shape p (history v)) (whole : ∀e,p∣N.width e)
local notation "receipt" => quotientShape N venue center within history bundle whole

theorem quotient_tag (c : C) (u : (quotientBits N venue center within history c).Node) :
    ((receipt c).recipe hp).tag u=((bundle u.1.val).recipe hp).tag u.2 :=
  combined_tag hp _ _ _ _ _ _ u

theorem quotient_arity (c : C) (u : (quotientBits N venue center within history c).Node) :
    ((receipt c).recipe hp).arity u=((bundle u.1.val).recipe hp).arity u.2 :=
  combined_arity hp _ _ _ _ _ _ u

end
end Hierarchy.DescentBundleHistory

end OAI
