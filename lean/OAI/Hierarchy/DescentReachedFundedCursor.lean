import OAI.Hierarchy.DescentResetFundedNodeCard
import OAI.Hierarchy.DescentReachedNodeCells
import OAI.Hierarchy.DescentFundedCompactReturn

namespace OAI
/-! # The physically funded count and the exact local recipe cursor at every padded slot -/
namespace Hierarchy.DescentSixParty.Reached.NodeCells
open DescentKernelHistory DescentLocalArchiveOrder DescentColonies DescentCompiler
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist : ℕ}
  (cap : Reached W G q ε S k age grain degree wire hist)
local notation "H" => S.hostSize age
local notation "J" => S.groupCount age
local notation "A" => cap.placement


open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentColonies
open scoped Classical BigOperators Fin.CommRing
local notation "rank" => cap.vertex.trans (Fin.castLEEmb cap.valid.host)

theorem funded_site (precision : ℕ) (x : Block k) (h : Fin H) (g : Fin J) :
    Census.count A (Equiv.refl _) rank precision h g x=
      (((siteAt cap x h g).elim 0 (fun u=>((A).records u).length):ℕ):Cell precision):=by
  classical
  cases found:siteAt cap x h g with
  | some u=>
    have loc:coordinate cap u=(h,g,x):=(siteAt_some cap x h g u).mp found
    have sameH:rank ((A).pos u).2=h:=congrArg Prod.fst loc
    have sameG:((A).pos u).1=g:=congrArg (fun l=>l.2.1) loc
    have sameX:(A).block u=x:=congrArg (fun l=>l.2.2) loc
    subst h g x
    have positive : ∃v,rank v=rank ((A).pos u).2:=⟨_,rfl⟩
    have where_:positive.choose=((A).pos u).2:=(rank).injective positive.choose_spec
    have mass:PackedCensus.histories W (A).pos (A).block (A).records ((A).pos u) ((A).block u)=((A).records u).length:=by
      unfold PackedCensus.histories StarKeys.blockMass
      rw [Finset.sum_eq_single u]
      · simp
      · intro v _ neq
        exact ite_eq_right fun hv=>neq (cap.valid.coordinates (Prod.ext hv.1 hv.2))
      · simp
    unfold Census.count
    rw [dite_eq_left positive, where_]
    exact congrArg (fun t : ℕ => (t : Cell precision)) mass
  | none=>
    have missed:∀u,coordinate cap u≠(h,g,x):=(siteAt_none cap x h g).mp found
    by_cases atHost:∃v,rank v=h
    · have blank:PackedCensus.histories W (A).pos (A).block (A).records (g,atHost.choose) x=0:=by
        unfold PackedCensus.histories StarKeys.blockMass
        apply Finset.sum_eq_zero
        intro u _
        apply ite_eq_right
        rintro ⟨pos,bl⟩
        apply missed u
        unfold coordinate
        rw [pos,bl]
        exact Prod.ext atHost.choose_spec rfl
      unfold Census.count
      rw [dite_eq_left atHost]
      change (PackedCensus.histories W (A).pos (A).block (A).records (g,atHost.choose) x : Cell precision)=_
      rw [blank]
      rfl
    · unfold Census.count
      rw [dite_eq_right atHost]
      rfl

theorem funded_cursor {N precision : ℕ} (B : BitDescription W) (ord : DescentLocalArchiveOrder.Local B)
    (fits : ∀v,((A).records v).length<2^precision)
    (within : ∀v,((A).records v).length≤Fintype.card (B.recipe v).Node)
    (x : Block k) (n : Fin N) (h : Fin H) (g : Fin J)
    (empty : whereAt cap B ord x n h g=none) :
    (Census.count A (Equiv.refl _) rank precision h g x).val≤n.val:=by
  rw [funded_site]
  cases q:siteAt cap x h g with
  | none=>simp
  | some v=>
    change (((A).records v).length : Cell precision).val≤_
    rw [Fin.val_cast_of_lt (fits v)]
    exact (within v).trans ((whereAt_pad cap B ord x n h g).mp empty v ((siteAt_some cap x h g v).mp q))

end
end Hierarchy.DescentSixParty.Reached.NodeCells

end OAI
