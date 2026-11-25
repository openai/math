import OAI.Hierarchy.DescentOrdinaryAtomFieldRAM
import OAI.Hierarchy.DescentOrdinaryActorInputs
import OAI.Hierarchy.DescentStableAtomFields

namespace OAI
/-! # The field in a real new actor's compact RAM book -/
namespace Hierarchy.DescentOrdinaryLocalBirth
open DescentPackedLocalAtoms DescentSIMDLookup
open DescentSixParty DescentKernelHistory Computability.BorderVNP.Crossing DescentNetworkPartition
open DescentCableDonorNames DescentSharedCableNames
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V I T C : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    [Fintype I] [Fintype T] [Fintype C]
    {d k i D K Z d₁ d₂ : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (desc : BitDescription W) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (room : ∀i,z i≤Z) (prof : I→Profile G.C) (picked : ∀i,pick (i,0)∈W.core)
local notation "N" => W.graph
local notation "M" => GadgetNetwork.physical N pick (branchWidth G z prof)
local notation "r₀" => physicalBits G W.toWorld pick z room prof desc.recipe
variable (a : (GadgetNetwork.physical W.graph pick (branchWidth G z prof)).Site→T) (b : T→C)
variable (x₁ : T→EuclideanSpace ℝ (Fin d₁)) (x₂ : C→EuclideanSpace ℝ (Fin d₂))
    (ok₁ : ∀t,‖x₁ t‖≤1) (ok₂ : ∀t,‖x₂ t‖≤1)
local notation "mid" => quotient M a x₁ ok₁
local notation "r₁" => quotientBits M a x₁ ok₁ r₀
local notation "r₂" => quotientBits mid b x₂ ok₂ r₁
variable (halo : Halo C W.graph.Site D)
    (oldHere : ∀u : W.graph.Site,u∈halo.member (b (a (.inl u))))
    (newHere : ∀i j,W.graph.src (pick (i,0))∈halo.member (b (a (.inr (i,j)))))
    (oldRank : ∀u,(desc.recipe u).Node ↪ Fin K)



variable (c : C)


open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
variable {n m s H R lanes w : ℕ}
local notation "nodes" => Width D K A.cap
local notation "ids" => compact A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c

/-- `old` lives in the old donor's existing dense book. The other branch
is keyed by the genuine outgoing first-grain ordinal and born party. -/
def rawFields {cap : ℕ} (old : Fin D→Fin K→Cell s) (fresh : Fin D→Fin cap→Fin 6→Cell s) (j : Fin (Width D K cap)) :=
  let v:=finProdFinEquiv.symm j
  (finSumFinEquiv.symm v.2).elim (old v.1) (fun edge=>let f:=finProdFinEquiv.symm edge;fresh v.1 f.1 f.2)

def historyField (old : ∀v,(desc.recipe v).Node→Cell s) (fresh : I→Fin 6→Cell s) (v : (M).Site) : (r₀ v).Node→Cell s :=
  match v with
  | .inl u=>old u
  | .inr (p,j)=>fun _=>fresh p j

variable (old : Fin D→Fin K→Cell s) (fresh : Fin D→Fin A.cap→Fin 6→Cell s)
variable (previous : ∀v,(desc.recipe v).Node→Cell s) (primitive : I→Fin 6→Cell s)
variable (kept : ∀v (h:b (a (.inl v))=c) u,old (oldSlot pick z prof a b halo oldHere c v h) (oldRank v u)=previous v u)
    (born : ∀i j (h:b (a (.inr (i,j)))=c),fresh (birthSlot pick z prof a b halo newHere c i j h) (outgoingSlot A native S ready pick picked i) j=primitive i j)

include kept born in
theorem raw_fields (u : (r₂ c).Node) :
    rawFields (cap:=A.cap) old fresh (short A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c u)=
      let q:=roster desc pick z room prof a b x₁ x₂ ok₁ ok₂ c u
      historyField desc pick z room prof previous primitive q.1.val q.2 := by
  let q:=roster desc pick z room prof a b x₁ x₂ ok₁ ok₂ c u
  change rawFields old fresh (book A native S ready desc pick z room prof picked a b halo oldHere newHere oldRank c q)=historyField desc pick z room prof previous primitive q.1.val q.2
  rcases q with ⟨⟨v|⟨i,j⟩,h⟩,v'⟩
  · change rawFields old fresh (finProdFinEquiv
        (oldSlot pick z prof a b halo oldHere c v h,finSumFinEquiv (.inl (oldRank v v'))))=previous v v'
    simpa only [rawFields,Equiv.symm_apply_apply,Sum.elim_inl] using kept v h v'
  · change rawFields old fresh (finProdFinEquiv
        (birthSlot pick z prof a b halo newHere c i j h,
          finSumFinEquiv (.inr (finProdFinEquiv (outgoingSlot A native S ready pick picked i,j)))) )=primitive i j
    simpa only [rawFields,Equiv.symm_apply_apply,Sum.elim_inr] using born i j h

variable (wanted : Cell n) (address : Fin (DescentPackedActorMask.actors D A.cap)→Cell n) (count : Fin D→Cell m)
    (count_read : ∀d,(count d).val=((donorAt halo c d).map (fun u=>Fintype.card (desc.recipe u).Node)).getD 0)
    (target_old : ∀d,address (DescentPackedActorMask.oldAddress A.cap d)=wanted ↔ ∃u,donorAt halo c d=some u ∧ b (a (.inl u))=c)
    (target_new : ∀d slot j,address (DescentPackedActorMask.bornAddress d (finProdFinEquiv (slot,j)))=wanted ↔
      ∃i,donorAt halo c d=some (W.graph.src (pick (i,0))) ∧ outgoingSlot A native S ready pick picked i=slot ∧ b (a (.inr (i,j)))=c)
    (old_dense : ∀u (j : Fin K),j.val<Fintype.card (desc.recipe u).Node ↔ ∃v,oldRank u v=j)

include kept born count_read target_old target_new old_dense in
theorem physical_field {K' : ℕ} (alive : wanted≠0) (small : Fintype.card (r₂ c).Node≤K')
    (table : Fin H→Fin R→Cell (s*K')) (mem : Memory w) (out : ℕ) (hm : 0<lanes) (h : Fin H) (g : Fin R)
    (room_ : (s*K')*lanes≤w) (posted : ∀p : Row H R lanes,mem (out+(row H R lanes p).val)=((data table p).val:Computability.VPVNP.BurstRAM.Word w))
    (localBook : table h g=pack s nodes K' (DescentPackedActorMask.occupied D K A.cap m (DescentPackedActorMask.target n _ wanted (encode n _ address)) (encode m D count)) (encode s _ (rawFields old fresh)))
    (u : (r₂ c).Node) :
    let p:=position h g hm;let q:=roster desc pick z room prof a b x₁ x₂ ok₁ ok₂ c u
    digit s (ids u).val (digit (s*K') (lane g hm).val (mem (out+(row H R lanes p).val)).val)=
      (historyField desc pick z room prof previous primitive q.1.val q.2).val := by
  let p:=position h g hm;let l:=lane g hm
  have floor : p.2.val*lanes+l.val=g.val:=Nat.div_add_mod' ..
  have id : (⟨p.2.val*lanes+l.val,floor.trans_lt g.isLt⟩:Fin R)=g:=Fin.ext floor
  have size : (data table p).val<2^w:=(data table p).isLt.trans_le (Nat.pow_le_pow_right (by decide) room_)
  have laneAt : digit (s*K') l.val (mem (out+(row H R lanes p).val)).val=(table h g).val:=by
    rw [posted p,Fin.val_cast_of_lt size,data,digit_encode,dite_eq_left (floor.trans_lt g.isLt),id]
    rfl
  have typed:=venue_digit A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c wanted address count count_read target_old target_new old_dense alive small (rawFields old fresh) u
  exact (congrArg (digit s (ids u).val) (laneAt.trans (congrArg Fin.val localBook))).trans
    (typed.trans (congrArg Fin.val (raw_fields A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c old fresh previous primitive kept born u)))

end
end Hierarchy.DescentOrdinaryLocalBirth

end OAI
