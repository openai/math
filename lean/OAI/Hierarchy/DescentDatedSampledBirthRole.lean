import OAI.Hierarchy.DescentDatedBirthRoleBound
import OAI.Hierarchy.DescentDatedOriginalMouthStamp

namespace OAI
/-! # The measured W tag bounds the role used by the actual registered resolver -/
namespace Hierarchy.DescentOrdinaryOriginPorts
open DescentSIMDLookup DescentOrdinaryOriginMask
theorem tag_of_equal_stamp (R S : Return) (d : ℕ) (n : Fin R.newNodes) (j : Fin S.newNodes)
    (x : Cell (R.ordinalBits*R.newNodes)) (y : Cell (S.ordinalBits*S.newNodes))
    (degree : R.degree=S.degree) (depth : R.depth=S.depth) (previous : R.oldNodes=S.oldNodes)
    (cap : R.capacity=S.capacity)
    (same : ((encode R.ordinalBits R.newNodes).symm x n).val=((encode S.ordinalBits S.newNodes).symm y j).val) :
    readLaw R d n 0 x=readLaw S d j 0 y :=by
  cases R with
  | mk D k K c nodes bits H Q G B M =>
    cases S with
    | mk D' k' K' c' nodes' bits' H' Q' G' B' M' =>
      dsimp only at degree depth previous cap
      subst D';subst k';subst K';subst c'
      unfold readLaw
      simp only [same, extent]
      split
      · unfold tuple
        dsimp only
        let seat : Fin (DescentPackedActorMask.nodes (DescentHaloWalkRAM.breadth D * 2^k) K c) :=
          ⟨((encode bits' nodes').symm y j).val-1, by omega⟩
        cases part : finSumFinEquiv.symm (DescentOrdinaryAtomFieldRAM.bookItem D k K c seat) <;>
          simp only [seat] at part <;> simp only []
      · rfl
end Hierarchy.DescentOrdinaryOriginPorts

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryOriginMask DescentOrdinaryOriginPorts DescentOrdinaryAtomFieldRAM DescentOrdinaryMouthReturn
open DescentSIMDLookup DescentOperandVectorArena DescentHaloWalkRAM DescentPackedZip DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem split_host_cast {H H' Q : ℕ} (change_ : H=H') (h : Fin (H*Q)) :
    finProdFinEquiv.symm (h.cast (congrArg (·*Q) change_)) =
      ((finProdFinEquiv.symm h).1.cast change_,(finProdFinEquiv.symm h).2) :=by
  cases change_;rfl

variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (floor : ℕ) (A : v.ArgumentEntry)
  (mat : A.Match v floor) (shape : v.VectorShape)
local notation "l" => v.resolver
local notation "B" => v.bornBook
local notation "U" => v.vector
local notation "L" => v.mouthChart mat.newBlocks
local notation "rect" => References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes
  v.reference.capacity (v.resolver.size+2)
local notation "refs" => (A.directory v floor mat).refs

/-- The native origin and mouth programs read two potentially different pages of the
same W directory. Their measured donor stamp is identical even on padded receivers. -/
theorem raw_role_room {w nb mb : ℕ} (pg : Fin (U).pageCount) (rows : rect nb mb)
    (chip : Fin (B).hosts→Fin (B).groups→Cell (B).chipBits) (home : (B).hosts=(U).hosts)
    (groups : (B).groups=(U).groups*(U).radix) (bits : (B).bits=(l).size+2) (m : Memory w)
    (pitch : 0<(U).lanes*(U).radix)
    (pages : ∀p q,ScalarOperand.Measured (refs p q) (rows p q) (l).nodes ((U).lanes*(U).radix) (v.vectorStart floor) m)
    (j : Fin (l).jobs) (h : Fin (l).hosts) (g : Fin (l).groups)
    (tag : (v.originHeaderValue shape (rows pg) j 0 h g).val=2) :
    let donors:=v.headerMouthRows floor A mat rows home groups bits
    (ScalarOperand.take (((l).index.symm j).2.1) (v.mouthHeaderValue floor A mat shape donors chip home groups j 1 h g)).val≤10 :=by
  intro donors
  let key:=(l).index.symm j
  let arg:=key.2.2.cast (shape.operands.trans mat.newArgs.symm)
  let block:=key.1.cast shape.blocks
  let host:=h.cast (shape.hosts.trans (congrArg (·*(U).lows) home.symm))
  let old:=finProdFinEquiv.symm host
  let k:=(finProdFinEquiv (g.cast shape.groups,block)).cast groups.symm
  let n:=key.2.1
  let R:=(L).stampLayout v.originBits
  let mouthStamp:=selection (extent R) (l).nodes v.originBits (marked (donors arg old.2) old.1 k)
  let shared:=finProdFinEquiv.symm (h.cast shape.hosts)
  let priorStamp:=selection v.originCandidates (l).nodes v.originBits (marked (rows pg shared.2) shared.1
    (finProdFinEquiv (g.cast shape.groups,block)))
  have coordinates : old=(shared.1.cast home.symm,shared.2) :=
    split_host_cast home.symm (h.cast shape.hosts)
  have actual:=v.original_mouth_stamp floor A mat pg rows home groups bits m pitch pages arg old.2 n v.originBits old.1 k
  have equal : ((encode v.originBits (l).nodes).symm mouthStamp n).val=((encode v.originBits (l).nodes).symm priorStamp n).val :=by
    change HeaderWords.stamp (donors arg old.2) v.originBits (l).nodes n old.1 k=_
    rw [actual]
    simp only [coordinates,Fin.cast_cast,Fin.cast_refl]; rfl
  have same:=tag_of_equal_stamp R v.originChart v.operandShortBits n n mouthStamp priorStamp rfl rfl rfl mat.newCap equal
  have live : (readLaw R v.operandShortBits n 0 mouthStamp).val=2 :=by rw [same];exact tag
  have room : extent R<2^v.originBits:=by
    change DescentPackedActorMask.nodes _ _ (B).cap<_
    rw [mat.newCap]
    exact v.originBits_fit
  exact (L).guarded_role_bound donors chip groups arg block host (g.cast shape.groups) n v.operandShortBits room live

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
