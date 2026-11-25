import OAI.Hierarchy.DescentOrdinarySourceReceipt

namespace OAI
/-! # The raw comparison fields return from the actual normalized source -/
namespace Hierarchy.DescentParallelBase.SourceReturn
open DescentHaloWalkRAM DescentSharedCableNames DescentSIMDLookup DescentParallelBase.ParentFilter
open scoped Classical Fin.CommRing
noncomputable section
variable {U E X T V : Type} [Fintype E] [DecidableEq U] [Fintype X] [Fintype T]
    {n H D Q O K L G b : ℕ} {B : Ends U n} (C : Blocks B E) (R : Fin H→Fin D→Option (Fin H))
    (symm : ∀v u i,R v i=some u→∃j,R u j=some v) (Z : Measured C R X T V Q O K L)
local notation "P" => breadth D
local notation "reach" => Gather.reaching R
variable (hosts : Fin Q→Fin H→Fin G→Option U)
variable (field : U→Fin (breadth D*O)→Cell b)

/-- A fixed comparator selects its own published slot. A query uses both
the real return path and the same previous donor's outgoing role. -/
def rawShelf (o : Fin O) (item : Option (Fin (P*O))) (low : Fin Q) (back : Fin P) (h : Fin H) (g : Fin G) : Cell b :=
  (hosts low h g).elim 0 (fun u=>field u (item.getD (finProdFinEquiv (back,o))))

theorem received_at (recv src : U) (e : Local C src) (g : Fin G) (p walk : Fin P)
    (seen : Gather.select reach (Z.venue recv).1 walk=some (Z.old src e))
    (forward : reach (Z.old src e) p=some (Z.venue src).1)
    (choice : Fin H→Fin G→Option (Fin (P*(Q*P)))) (low : Cell (Packed.bits Q)) (lowEq : low.val=(Z.venue src).2.val)
    (issued : Packed.token (choice (Z.old src e) g)=Query.finish P Q (Query.forward P Q (Packed.token (some p)) low)
      (Query.packedRoute R (Z.old src e) (some p)))
    (source : Fin Q→Fin P→Fin H→Fin G→Cell b) :
    donated reach source choice walk (Z.venue recv).1 g=source (Z.venue src).2 (finProdFinEquiv.symm ((Measured.roster C R symm Z).address src e)).1 (Z.venue src).1 g :=by
  let back:=(finProdFinEquiv.symm ((Measured.roster C R symm Z).address src e)).1
  have order:=source_order R C symm Z src e p forward
  have route:(Query.packedRoute R (Z.old src e) (some p)).val=back.val:=
    (Query.at_path R _ _).trans order.1.symm
  have selected : choice (Z.old src e) g=some (RAM.key p (Z.venue src).2 back) :=by
    have h:=issued.trans (Query.certified p (Z.venue src).2 back low _ lowEq route)
    simpa using congrArg (Packed.readToken (P*(Q*P))) h
  simp only [donated,seen,Option.elim_some]
  exact RAM.actual reach source choice _ _ g p _ back selected forward

include symm in
theorem received_raw (recv src : U) (e : Local C src) (g : Fin G) (p walk : Fin P)
    (seen : Gather.select reach (Z.venue recv).1 walk=some (Z.old src e))
    (forward : reach (Z.old src e) p=some (Z.venue src).1)
    (present : hosts (Z.venue src).2 (Z.venue src).1 g=some src)
    (choice : Fin H→Fin G→Option (Fin (P*(Q*P)))) (low : Cell (Packed.bits Q)) (lowEq : low.val=(Z.venue src).2.val)
    (issued : Packed.token (choice (Z.old src e) g)=Query.finish P Q (Query.forward P Q (Packed.token (some p)) low)
      (Query.packedRoute R (Z.old src e) (some p))) (item : Option (Fin (P*O))) :
    donated reach (rawShelf hosts field (Z.loc (Z.raw src e)).2 item) choice walk (Z.venue recv).1 g=
      field src (item.getD ((Measured.roster C R symm Z).address src e)) :=by
  rw [received_at C R symm Z recv src e g p walk seen forward choice low lowEq issued]
  simp only [rawShelf,present,Option.elim_some]
  rw [←(source_order R C symm Z src e p forward).2,finProdFinEquiv.apply_symm_apply]

end
end Hierarchy.DescentParallelBase.SourceReturn

end OAI
