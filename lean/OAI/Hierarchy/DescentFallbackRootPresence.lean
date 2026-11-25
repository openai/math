import OAI.Hierarchy.DescentMixedPrivateRoots
import OAI.Hierarchy.DescentResetActorTable
import OAI.Hierarchy.DescentResetLocalRows

namespace OAI
/-! # Which fallback root occupies a normalized host ticket -/
namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentColonies DescentGL DescentPlainTerminal DescentPlainTerminal.Suffix DescentIssuedFallbackPanel
open DescentChosenRouter DescentRelativeContacts DescentContacts DescentResetHostSize
open scoped Classical
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
variable {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool} (frame : SourceFrame Z T pos ix hub g)
variable (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K Δ : ℕ)
    (wt : V→Block k→ℕ) (flow : V→V→Block k→ℝ) (roster : SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K flow Δ wt)
local notation "c" => T.commonDepth
local notation "tags" => (2^Z.n:ℕ)
local notation "r" => Z.k-c
local notation "fit" => frame.enough.trans (Nat.sub_le ..)
local notation "b" => fun v=>Z.placement.b (frame.host v)
set_option quotPrecheck false in
local notation "safe" => roster.2.2.2.2.2.choose
local notation "ep" => endpoint near b frame.basis wt f (32*Nat.clog 2 (2*Δ)) B g tags safe
  (fun v j=>(frame.host v,j)∈Z.placement.keys) hub
local notation "μ" => rearrange frame.basis
local notation "relative" => fun t=>shortName c (T.code t)
set_option quotPrecheck false in
local notation "row" => fun v hi lo=>fieldsRelative c (ep v ((μ).symm (join fit hi lo)))

private theorem field_inj {Y : ℕ} : Function.Injective (DescentPlainTerminal.fields (Y:=Y)) := by
  rintro ⟨address,a⟩ ⟨address',otherTag⟩ eqn
  have sameAddress : address=address' := congrArg (fun entry : (ℕ×ℕ)×Option ℕ=>entry.1) eqn
  have sameTag : a.map Fin.val=otherTag.map Fin.val := congrArg Prod.snd eqn
  exact Prod.ext sameAddress ((Option.map_inj_right (fun _ _ h=>Fin.ext h)).mp sameTag)

include roster in
theorem each_label (v : V) (x : Block k) : ∃t,(T.code t).1=frame.host v ∧ DescentPlainTerminal.fields (T.code t).2=ep v x :=
  (roster.2.2.2.2.2.choose_spec.2 v (ep v x)).2 ⟨x,rfl⟩

include roster in
private theorem high_of_row (v : V) (x : Block k) (t : Z.Fallback) (label : DescentPlainTerminal.fields (T.code t).2=ep v x) :
    coarseName c (T.code t)=(high fit (μ x)).val := by
  have component : (ep v x).1.2=group (ep v x).1.1 (μ x) := by
    cases hv : hub v <;> simp [DescentPlainTerminal.endpoint,hv,DescentFineTerminals.leafKey]
  have day:=congrArg (fun a : (ℕ×ℕ)×Option ℕ=>a.1) label
  change (T.code t).2.1=(ep v x).1 at day
  rw [←day] at component
  have low:=(T.codeLegal t).1
  have top:=(T.codeLegal t).2.1.trans_eq frame.extent
  change (T.code t).2.1.2/2^((T.code t).2.1.1-c)=group c (μ x)
  rw [component]
  unfold group DescentColonies.width
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add]
  congr 2
  omega

include roster in
theorem root_presence (v : V) (hi : Block c) (ticket : Code r×Option (Fin tags)) :
    (∃t : Z.Fallback,(T.code t).1=frame.host v ∧ Z.rootBlock T (.inr t)=hi ∧
      Z.rootTicket T (.inr t)=.inr ticket) ↔
    ∃lo : Block (k-c),row v hi lo=DescentPlainTerminal.fields (ticket.1.val,ticket.2) := by
  constructor
  · rintro ⟨t,host,coord,kind⟩
    obtain ⟨x,atx⟩:=(roster.2.2.2.2.2.choose_spec.2 v (DescentPlainTerminal.fields (T.code t).2)).mp ⟨t,host,rfl⟩
    have whole : high fit (μ x)=hi:=Fin.ext ((high_of_row frame vertex near n f B wire K Δ wt flow roster v x t atx.symm).symm.trans (congrArg Fin.val coord))
    let lo:=@DescentPlainTerminal.low k T.commonDepth (μ x)
    have back : join fit hi lo=μ x:=whole ▸ join_high_low fit (μ x)
    have same:=Sum.inr.inj kind
    have fd : (relative t).2=(ticket.1.val,ticket.2) :=
      congrArg (fun z : Code r×Option (Fin tags)=>(z.1.val,z.2)) same
    refine ⟨lo,?_⟩
    change fieldsRelative c (ep v ((μ).symm (join fit hi lo)))=_
    rw [back,Equiv.symm_apply_apply,atx,←fields_relative,fd]
  · rintro ⟨lo,atLo⟩
    let x:=(μ).symm (join fit hi lo)
    obtain ⟨t,host,atx⟩:=each_label frame vertex near n f B wire K Δ wt flow roster v x
    have coarse:=(high_of_row frame vertex near n f B wire K Δ wt flow roster v x t atx)
    simp only [x,Equiv.apply_symm_apply,high_join] at coarse
    have rel : DescentPlainTerminal.fields (relative t).2=DescentPlainTerminal.fields (ticket.1.val,ticket.2):=by
      rw [fields_relative,atx];exact atLo
    have pair:=field_inj rel
    exact ⟨t,host,Fin.ext coarse,congrArg Sum.inr (Prod.ext (Subtype.ext (congrArg Prod.fst pair)) (congrArg (fun z : DescentContacts.Endpoint tags=>z.2) pair))⟩

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
