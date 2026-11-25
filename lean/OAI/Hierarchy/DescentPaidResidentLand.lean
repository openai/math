import OAI.Hierarchy.DescentPaidResidentGeometry
import OAI.Hierarchy.DescentIssuedDonorChart

namespace OAI
/-! # Charged particles follow the actual destination of each normalized row -/
namespace Hierarchy.DescentPaidResidentCount
open DescentKernelHistory DescentSixParty DescentStageEdgeReceipt DescentHostDirectory
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

private theorem appended_destination {Y : Type} (n : Normalize W) (s : Equiv.Perm n.result.graph.Site)
    (e : Equiv.Perm n.result.graph.Edge) (f : Y→W.graph.Site) (y : Y) :
    changeLand (n.appendNames_result s e) (s∘n.destination∘f) y=(n.appendNames s e).destination (f y) := by
  induction n with
  | done=>rfl
  | split W q m fit rest ih=>exact ih s e f
  | named W a b rest ih=>exact ih s e (a∘f)
  | merge W V key hub k g rest ih=>exact ih s e (MarkedWorld.address W key hub k g∘f)

variable {G : PoweredGadget F} {q ε : ℝ} {he : 0≤ε} {T : StageInput W G q ε} {c : (T.result he).Choice}

theorem Lands.canonical {N : MarkedWorld F d P bits} {norm : Normalize N} {land : (rawGraph he T c).Site→norm.result.graph.Site}
    (run : Lands he T c N norm land) (input : N=scanWorld he T c) :
    land=norm.destination∘rawInput he T c input := by
  induction run with
  | stage=>rfl
  | named n land prior s e ih=>
    rw [ih input]
    funext x
    exact appended_destination n s e _ x

theorem canonical_funds {N : MarkedWorld F d P bits} {norm : Normalize N} {counts : norm.result.graph.Site→ℕ}
    {hub : norm.result.graph.Site→Bool} (receipt : ParticleRows he T c N norm counts hub)
    (input : N=scanWorld he T c) (v : norm.result.graph.Site) :
    counts v=total (norm.destination∘rawInput he T c input) (fun u=>(T.records u).length) v := by
  obtain ⟨land,auth,funds⟩:=trajectory he T c receipt
  exact (funds v).trans (congrArg (fun f => total f (fun u => (T.records u).length) v)
    (auth.canonical input))

theorem destination_onto (norm : Normalize W) : Function.Surjective norm.destination := by
  induction norm with
  | done=>exact Function.surjective_id
  | split W q m fit rest ih=>exact ih
  | named W a b rest ih=>exact ih.comp a.surjective
  | merge W V key hub k g rest ih=>
    apply ih.comp
    intro v
    obtain ⟨u,_,hv⟩:=Finset.mem_image.mp v.property
    exact ⟨u,Subtype.ext hv⟩

theorem raw_destination_onto {N : MarkedWorld F d P bits} (norm : Normalize N) (state : N=scanWorld he T c) :
    Function.Surjective (norm.destination∘rawInput he T c state) := by
  apply (destination_onto norm).comp
  subst N
  intro v
  let r := BitDescription.scannedRows he T
  obtain ⟨u,hu⟩ := DescentSixParty.old_surjective W.graph r.pick
    (bestLayout (branchWidth G (fun _ => T.z) (r.profile c))) r.pack v
  exact ⟨.inl u,hu⟩

theorem total_on_fiber {O B X Y : Type} [Fintype O] [Fintype B] (f : O⊕B→X) (g : O⊕B→Y)
    (x : X) (y : Y) (same : ∀a,f a=x↔g a=y) (cost : O→ℕ) :
    total f cost x=total g cost y := by
  let old : {a : O //f (.inl a)=x}≃{a : O //g (.inl a)=y}:=Equiv.subtypeEquivRight (fun a=>same (.inl a))
  let born : {a : B //f (.inr a)=x}≃{a : B //g (.inr a)=y}:=Equiv.subtypeEquivRight (fun a=>same (.inr a))
  exact congrArg₂ (·+·) (Fintype.sum_equiv old _ _ (fun _=>rfl)) (Fintype.card_congr born)

end
end Hierarchy.DescentPaidResidentCount

end OAI
