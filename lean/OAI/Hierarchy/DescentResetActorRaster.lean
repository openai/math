import OAI.Hierarchy.DescentPackedActorRaster
import OAI.Hierarchy.DescentReentryCommonBlocks

namespace OAI
/-! # Authentic reset-bank occupancy of trunks, rotor boards and exceptional trees -/

namespace Hierarchy.DescentCommonPalette
open scoped Classical
theorem path_exists (height : ℕ) (word : List Bool) :
    (∃v : (tree height).Site,path v=word) ↔ word.length≤height := by
  constructor
  · rintro ⟨⟨d,f⟩,rfl⟩
    simpa [path] using Nat.le_of_lt_succ d.isLt
  · intro h
    refine ⟨⟨⟨word.length,Nat.lt_succ_of_le h⟩,word.get⟩,?_⟩
    simp [path]
end Hierarchy.DescentCommonPalette

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentResetAttachments DescentChosenRouter DescentCommonHost DescentRelativeContacts
open DescentContacts DescentCanonicalPorts DescentColonies
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
local notation "W" => reenter Z T
local notation "R" => Z.placement
local notation "depth₀" => T.commonDepth
local notation "lab" => fun t=>shortName depth₀ (T.code t)
local notation "X" => Node Z.V (Z.V×Endpoint (2^Z.n)) (Computability.BorderVNP.Crossing.Network.Site (DescentCommonPalette.rotor Z.graph))

/-- At an observed base every configured rotor cell is present. On the
fallback side an arbitrary path exists exactly up to the chosen directory's
true depth, even if no cable of positive width reaches that path. -/
def emits (q : X) (x : Block depth₀) : Prop :=
  match q with
  | .trunk _ z=>∃t : Z.Fallback,lab t=z ∧ coarseName depth₀ (T.code t)=x.val
  | .good _ u _=>∃v : Good (R).b (R).keys (R).hub,
      short (m:=depth₀) (R).b v.val=u ∧ (R).siteGroup depth₀ T.code (.inl v)=x.val
  | .fall s z ps=>∃t : Z.Fallback,
      lab t=z ∧ (R).siteGroup depth₀ T.code (.inr t)=x.val ∧ ps.length≤((R).fallbackBook s t).height

theorem reset_occupied (q : X) (x : Block depth₀) :
    (∃u : (W).graph.Site,commonName Z T u=q ∧ blockId Z T u=x) ↔ emits Z T q x := by
  let readName := rawName (R) Z.graph depth₀ T.code Z.positive Z.pay Z.circuit d
  let readBlock := rawCoordinate (R) Z.graph depth₀ T.code Z.positive Z.pay Z.circuit d
  have name (z : (Bool × Z.Fallback) ⊕ Z.bank.Site) :
      commonName Z T ((resetNames Z T).symm z) = readName z :=
    congrArg readName ((resetNames Z T).apply_symm_apply z)
  have coord (z : (Bool × Z.Fallback) ⊕ Z.bank.Site) :
      (blockId Z T ((resetNames Z T).symm z)).val = readBlock z :=
    congrArg readBlock ((resetNames Z T).apply_symm_apply z)
  constructor
  · rintro ⟨u,rfl,hx⟩
    obtain ⟨z,rfl⟩ := (resetNames Z T).symm.surjective u
    rw [name]
    have atBlock : readBlock z = x.val := (coord z).symm.trans (congrArg Fin.val hx)
    rcases z with ⟨s,t⟩ | ⟨⟨s,g|t⟩,node⟩
    · exact ⟨t,rfl,atBlock⟩
    · exact ⟨g,rfl,atBlock⟩
    · exact ⟨t,rfl,atBlock,(DescentCommonPalette.path_exists ((R).fallbackBook s t).height
        (DescentCommonPalette.path node)).mp ⟨node,rfl⟩⟩
  · cases q with
    | trunk s z=>
      rintro ⟨t,ht,id⟩
      refine ⟨(resetNames Z T).symm (.inl (s,t)),(name _).trans ?_,Fin.ext ((coord _).trans id)⟩
      exact congrArg (fun label => (Node.trunk s label : X)) ht
    | good s u cell=>
      rintro ⟨g,tag,id⟩
      let layers := selectedRotorLayers (R) Z.graph Z.positive Z.pay Z.circuit s g
      let eqv := DescentCommonPalette.rotorSiteEquiv Z.graph d layers C Z.width Z.unit
      refine ⟨(resetNames Z T).symm (.inr ⟨(s,.inl g),eqv cell⟩),
        (name _).trans ?_,Fin.ext ((coord _).trans id)⟩
      change (Node.good s (short (m:=depth₀) (R).b g.val) (eqv.symm (eqv cell)) : X) = .good s u cell
      rw [Equiv.symm_apply_apply,tag]
    | fall s z ps=>
      rintro ⟨t,tag,id,depth⟩
      obtain ⟨node,hp⟩ := (DescentCommonPalette.path_exists ((R).fallbackBook s t).height ps).mpr depth
      refine ⟨(resetNames Z T).symm (.inr ⟨(s,.inr t),node⟩),
        (name _).trans ?_,Fin.ext ((coord _).trans id)⟩
      change (Node.fall s (lab t) (DescentCommonPalette.path node) : X) = .fall s z ps
      rw [tag,hp]

theorem reset_actor_word (q : ↥(commonNames Z T)) :
    DescentActorRaster.actorMask (placed Z T) (blockId Z T) q =
    DescentSIMDLookup.encode 1 (2^depth₀) (fun x=>if emits Z T q.val x then 1 else 0) := by
  unfold DescentActorRaster.actorMask
  apply congrArg (DescentSIMDLookup.encode 1 (2^depth₀))
  funext x
  have eqn : (∃u,placed Z T u=q ∧ blockId Z T u=x) ↔ emits Z T q.val x := by
    constructor
    · rintro ⟨u,hu,hx⟩
      exact (reset_occupied Z T q.val x).mp ⟨u,congrArg Subtype.val hu,hx⟩
    · intro he
      obtain ⟨u,hu,hx⟩ := (reset_occupied Z T q.val x).mpr he
      exact ⟨u,Subtype.ext hu,hx⟩
  simp only [DescentActorRaster.present,eqn]

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
