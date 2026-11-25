import OAI.Hierarchy.DescentHubTetherLedger
import OAI.Hierarchy.DescentActorMass
import OAI.Hierarchy.DescentOccurrenceAllowance

namespace OAI
/-! # Original exterior equality tokens survive exactly at their actual attached ports -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentResetTrunks Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits)

def exteriorTokens (v : W.graph.Site) := bin W.graph.attach (fun _=>1) v
def exteriorWidth (v : W.graph.Site) := bin W.graph.attach bits v

/-- The two physical edge-end columns count precisely the original exterior width of
a hub at the conventional hub price. No entry in the paid scalar record list is used. -/
def HubExterior (flag : W.graph.Site→Bool) : Prop :=
  ∀v,flag v=true→W.siteUnits flag (fun _=>([] : List Unit)) 1 256 0 v=256*W.exteriorWidth v

omit [Field F] in
theorem exterior_fiber {Z : MarkedWorld F d P bits} (loc : W.graph.Site→Z.graph.Site)
    (attach : ∀p,Z.graph.attach p=loc (W.graph.attach p)) (n : P→ℕ) (v : Z.graph.Site) :
    bin loc (bin W.graph.attach n) v=bin Z.graph.attach n v := by
  rw [bin_comp]
  exact congrArg (fun f=>bin f n v) (funext fun p=>(attach p).symm)

omit [Field F] in
theorem exterior_token_card (v : W.graph.Site) : W.exteriorTokens v=Fintype.card {p //W.graph.attach p=v} := by
  rw [exteriorTokens,←width_bin]
  simp [DescentNamedContact.width]

omit [Field F] in
theorem exterior_width_eq {s : ℕ} (uniform : ∀p,bits p=s) (v : W.graph.Site) :
    W.exteriorWidth v=s*W.exteriorTokens v := by
  unfold exteriorWidth exteriorTokens
  have eqn : bits=fun p : P=>s*(1:ℕ) := funext fun p=>by simp [uniform p]
  exact (congrArg (fun a : P → ℕ => bin W.graph.attach a v) eqn).trans
    (bin_mul W.graph.attach (fun _ => 1) v s)

omit [Field F] in
theorem exterior_eq_zero (flag : W.graph.Site→Bool) (owns : ∀p,flag (W.graph.attach p)=true)
    (v : W.graph.Site) (ordinary : flag v=false) : W.exteriorTokens v=0 := by
  apply Finset.sum_eq_zero
  intro p _
  apply ite_eq_right
  intro eqn
  have attached := owns p
  rw [eqn,ordinary] at attached
  contradiction

omit [Field F] in
theorem HubExterior.map {Z : MarkedWorld F d P bits} {src : W.graph.Site→Bool} {dst : Z.graph.Site→Bool}
    (balance : W.HubExterior src) (inW : HubIncidence W src) (inZ : HubIncidence Z dst)
    (loc : W.graph.Site→Z.graph.Site) (image : TetherImage W Z loc)
    (same : ∀v,dst (loc v)=src v) (pins : ∀p,Z.graph.attach p=loc (W.graph.attach p)) :
    Z.HubExterior dst := by
  intro v hv
  let old := fun _ : W.graph.Site=>([] : List Unit)
  let new := fun _ : Z.graph.Site=>([] : List Unit)
  rw [image.siteUnits_fiber src dst inW inZ old new 1 256 0 v hv same (fun _ _=>rfl) rfl]
  calc
    _ = bin loc (fun u=>256*W.exteriorWidth u) v := by
      unfold bin
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : loc u=v
      · have hu : src u=true := (same u).symm.trans (by rw [h,hv])
        simp only [h,ite_true,balance u hu,old]
      · simp [h]
    _ = 256*Z.exteriorWidth v := by rw [bin_mul];exact congrArg (256*·) (W.exterior_fiber loc pins bits v)

theorem hub_token_room {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {G : PoweredGadget F} {q ε : ℝ} {k : ℕ} (A : GroupStage W G q ε J V k)
    (balance : W.HubExterior (fun z=>A.hub (A.pos z).2)) (s : ℕ) (uniform : ∀p,bits p=s)
    (hs : 0<s) (grain : A.z*G.b≤ s) (v : W.graph.Site) (hub : A.hub (A.pos v).2=true) :
    256*W.exteriorTokens v≤A.cap := by
  let tag := fun z=>A.hub (A.pos z).2
  have empty := A.noHubAtoms v hub
  have weighed : W.siteUnits tag A.records A.wire 256 A.hist v=
      A.wire*(W.siteUnits tag (fun _=>([] : List Unit)) 1 256 0 v) := by
    simp only [siteUnits,empty,Nat.mul_zero,List.length_nil,Nat.add_zero,Nat.one_mul,Nat.mul_add,
      Finset.mul_sum,mul_ite,Nat.mul_zero,Nat.mul_assoc]
  rw [balance v hub,W.exterior_width_eq uniform v] at weighed
  have cost := A.site_units_room v
  rw [show W.siteUnits tag A.records A.wire 256 A.hist v=_ from weighed] at cost
  have estimate : A.wire*s*(256*W.exteriorTokens v)≤A.wire*s*A.cap := by
    calc
      _ = A.wire*(256*(s*W.exteriorTokens v)) := by ring
      _ ≤ _ := cost.trans (Nat.mul_le_mul_right A.cap (Nat.mul_le_mul_left _ grain))
  exact Nat.le_of_mul_le_mul_left estimate (Nat.mul_pos A.wirePos hs)

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
