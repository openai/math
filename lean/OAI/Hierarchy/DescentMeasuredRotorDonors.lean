import OAI.Hierarchy.DescentRotorInstalledMatrix
import OAI.Hierarchy.DescentStemCoordinateBook
import OAI.Hierarchy.DescentResetStemCompactOrder

namespace OAI
/-! # Group and fine source coordinates of every genuine paid rotor donor -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentResetAttachments StarKeys DescentChosenRouter DescentRouterSlots DescentResetStemCompactOrder
open DescentStemCoordinateBook
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P V : Type} [Field F] {groups : ℕ} [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃Fin groups×Block k) (native : W.graph.Edge↪ℕ)
local notation "Wold" => W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site => (A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "cutDepth" => T.commonDepth
local notation "fits" => frm.enough.trans (Nat.sub_le ..)
local notation "v₀" t:arg => frm.host.symm (t).val.1
local notation "hi₀" t:arg => Z.rootBlock T (.inl t)
local notation "item" s:arg t:arg => Item Z.placement.contact Z.placement.owner s (.inl t)
local notation "here" s:arg e:arg => localAddress A native S ready digits frm.basis (c:=cutDepth) s e
local notation "shape" ng:arg H:arg M:arg b:arg => (⟨m,k,m-cutDepth,H,ng,M,b⟩ : DescentStemCoordinateBook.Shape)

/-- The high/low GL coordinate sheet, addressed using the true physical row of
an old grain, gives the preceding source's compressed group and exact fine block
on both sides of the exceptional tree. -/
theorem rotor_coordinate_values {ng : ℕ} (H M b : ℕ) (side : Bool) (t : Z.placement.Good)
    (x : Block k) (band : Fin ng)
    (coarse : band.val*2^k+x.val=(hi₀ t).val)
    (split : ∀y : Block m, (digits y).1.val=y.val/2^k ∧ (digits y).2.val=y.val%2^k)
    (e : item side t) :
    (shape ng H M b).value frm.basis 0 x (here side e.val).1 band=
        compress (groupDomain digits frm.basis fits (v₀ t) (hi₀ t)) (A.pos (W.graph.src e.val.1)).1.val ∧
      (shape ng H M b).value frm.basis 1 x (here side e.val).1 band=(A.block (W.graph.src e.val.1)).val :=by
  let v:=v₀ t
  let hi:=hi₀ t
  let bank:=shape ng H M b
  let lo:=(here side e.val).1
  let old:=fun l : Block (m-cutDepth)=>donor digits frm.basis fits v hi l
  have cells (l : Block (m-cutDepth)) : bank.original frm.basis band x l=
      (rearrange frm.basis).symm (join fits hi l) :=by
    apply congrArg (rearrange frm.basis).symm
    apply Fin.ext
    change ((band.val*2^k+x.val)*2^(m-cutDepth)+l.val)%2^m=_
    rw [coarse]
    exact Nat.mod_eq_of_lt (join fits hi l).isLt
  have located:=rotorCellsAt A S ready digits Z T frm side t e.val e.property
  have placed : old lo=home A (endSite A side e.val) :=by
    change donor digits frm.basis fits v hi
      (subcell digits frm.basis (port A side e.val).1)=_
    rw [port_fst A side e.val]
    exact donor_locates digits frm.basis fits _ v hi located.1 located.2
  have moved : ((old lo).1.1,(old lo).2)=
      ((A.pos (W.graph.src e.val.1)).1,A.block (W.graph.src e.val.1)) :=by
    rw [placed]
    cases side with
    | false=>rfl
    | true=>
      obtain ⟨_,_,eqn⟩:=Finset.mem_map.mp (A.peers e.val.1).2
      have groupEq := congrArg Prod.fst eqn
      exact Prod.ext groupEq (A.same e.val.1).symm
  have gr (l : Block (m-cutDepth)) : (bank.original frm.basis band x l).val/2^k=(old l).1.1.val :=by
    rw [cells]
    exact (split _).1.symm
  constructor
  · change compress (Finset.univ.image (fun l=>(bank.original frm.basis band x l).val/2^k))
        ((bank.original frm.basis band x lo).val/2^k)=_
    rw [funext gr,gr lo]
    exact congrArg (compress (groupDomain digits frm.basis fits v hi))
      (congrArg (fun z : Fin groups×Block k=>z.1.val) moved)
  · change (bank.original frm.basis band x lo).val%2^k=_
    rw [cells]
    exact (split _).2.symm.trans (congrArg (fun z : Fin groups×Block k=>z.2.val) moved)

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
