import OAI.Hierarchy.DescentDatedSignedHome
import OAI.Hierarchy.DescentIncidentMeasuredOrder
import OAI.Hierarchy.DescentParentFilterFused
import OAI.Hierarchy.DescentResetWindowFields
import OAI.Hierarchy.DescentGraphPairing

namespace OAI
/-! Transport the proven original marked cable incidence and its chronological material through the single physical naming. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentPacking DescentParallelBase DescentParallelBase.ParentFilter DescentSharedCableNames DescentSixParty
open DescentHaloWalkRAM DescentPackedZip DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin U : Type} [Field F] [Fintype U] [DecidableEq U] {d : ℕ} {bits : Pin→ℕ} {G:PoweredGadget F}
  {price ε : ℝ} {H H₀ D Q O K L b J k : ℕ} {W:MarkedWorld F d Pin bits}
local notation "P₀" => breadth D
local notation "group" => (Equiv.refl (Fin J)).toEmbedding
local notation "Host" => Stage.Host (Fin J) U k
variable (A:GroupStage W G price ε (Fin J) U k) (native:W.graph.Edge↪ℕ)
  (R:Fin H₀→Fin D→Option (Fin H₀)) (symm:∀u v j,R u j=some v→∃n,R v n=some u)
  (host:U↪Fin H) (pitch:ℕ) (space:Fused.capacity D Q K L≤2^b)
  (before:Fin (2^k)→Fin (breadth D*O)→Fin H→Fin J→Option (Fused.Raw R Q K L b))
  (parent:Fin (2^k)→Fin O→Fin H₀→Fin J→Option (ParentFilter.Source (breadth D) Q K L))
  (marks:Fin (2^k)→Fin (breadth D*O)→Fin H→Fin J→Cell 1)
local notation "who" => SignedExtent.wholeHost group host

structure SignedDrawing where
  edge : Type
  [finiteEdge : Fintype edge]
  raw : Type
  [finiteRaw : Fintype raw]
  ticket : Type
  [finiteTicket : Fintype ticket]
  site : Type
  blocks : Blocks (Stage.source A native) edge
  core : edge→Prop
  emission : DescentResetWindowFields.Emission A native blocks core
  observed : Measured blocks R raw ticket site Q O K L
  shelf : Measured.Shelf blocks R observed
  order : ∀h(e f:Local blocks h),Incidence.srcKey blocks R symm observed h e<Incidence.srcKey blocks R symm observed h f ↔
    observed.site (observed.src (observed.head h e))<observed.site (observed.src (observed.head h f))
  coordinate : ∀u,(host u.1.2).val=(observed.venue u).1.val*pitch+(observed.venue u).2.val
  low : ∀u,(observed.venue u).2.val<pitch
  address : ∀h(e:Local blocks h),observed.loc (observed.raw h e)=
    observed.loc (observed.raw (blocks.src e.val) ⟨e.val,e.property.1,Or.inl rfl⟩)
  input : ∀x j, before x j=Fused.cell blocks R observed shelf
    (fun h p a s f=>Fused.field_room R (observed.venue h) p (observed.loc a).1 s f space) (who x) j
  launch : ∀x h g t,who x h g=some t→∀e:Local blocks t,let a:=observed.loc (observed.raw t e)
    parent x a.2 a.1 g=some (observed.read (blocks.src e.val) ⟨e.val,e.property.1,Or.inl rfl⟩)
  mark : ∀x j h g t,who x h g=some t→∀e:Local blocks t,(Measured.roster blocks R symm observed).address t e=j→
    ((marks x j h g).val=1 ↔ core e.val)

namespace SignedDrawing
variable {W':MarkedWorld F d Pin bits}
/-- Change the name of the world while keeping the actual supplied parent diagram. -/
def named (eqn:W=W') (chronology:originalId W.graph.Edge=native)
    (drawing:SignedDrawing (cast (congrArg (fun w:MarkedWorld F d Pin bits=>GroupStage w G price ε (Fin J) U k) eqn) A)
      (originalId W'.graph.Edge) R symm host pitch space before parent marks) :
    SignedDrawing A native R symm host pitch space before parent marks:=by
  subst W'
  subst native
  exact drawing

theorem named_heq (eqn:W=W') (chronology:originalId W.graph.Edge=native)
    (drawing:SignedDrawing (cast (congrArg (fun w:MarkedWorld F d Pin bits=>GroupStage w G price ε (Fin J) U k) eqn) A)
      (originalId W'.graph.Edge) R symm host pitch space before parent marks) :
    HEq (named A native R symm host pitch space before parent marks eqn chronology drawing) drawing:=by
  subst W'
  subst native
  rfl

theorem named_blocks (eqn:W=W') (chronology:originalId W.graph.Edge=native)
    (drawing:SignedDrawing (cast (congrArg (fun w:MarkedWorld F d Pin bits=>GroupStage w G price ε (Fin J) U k) eqn) A)
      (originalId W'.graph.Edge) R symm host pitch space before parent marks) :
    HEq (named A native R symm host pitch space before parent marks eqn chronology drawing).blocks drawing.blocks:=by
  subst W'
  subst native
  rfl

theorem named_units (eqn:W=W') (chronology:originalId W.graph.Edge=native)
    (drawing:SignedDrawing (cast (congrArg (fun w:MarkedWorld F d Pin bits=>GroupStage w G price ε (Fin J) U k) eqn) A)
      (originalId W'.graph.Edge) R symm host pitch space before parent marks) :
    HEq (named A native R symm host pitch space before parent marks eqn chronology drawing).emission.units
      drawing.emission.units:=by
  subst W'
  subst native
  rfl

theorem of_named (eqn:W=W') (chronology:originalId W.graph.Edge=native)
    (found:Nonempty (SignedDrawing
      (cast (congrArg (fun w:MarkedWorld F d Pin bits=>GroupStage w G price ε (Fin J) U k) eqn) A)
      (originalId W'.graph.Edge) R symm host pitch space before parent marks)) :
    Nonempty (SignedDrawing A native R symm host pitch space before parent marks) :=by
  subst W'
  simpa only [cast_eq,chronology] using found
end SignedDrawing
end
end Hierarchy.DescentDatedAddressBook

end OAI
