import OAI.Hierarchy.DescentFallbackPacket
import OAI.Hierarchy.DescentPackedRankReadout
import OAI.Hierarchy.DescentPackedInstalledPrivate
import OAI.Hierarchy.DescentFallbackRootPresence
import OAI.Hierarchy.DescentResetPackedStencil

namespace OAI
/-! # A source packet shared by all five physical fallback fields -/
namespace Hierarchy.DescentFallbackPeriod
open DescentSIMDLookup DescentPackedLeafSelector DescentSharedBookScan DescentSharedLeafLookup
open DescentFallbackShapeTable DescentResetHostSize DescentResetCableSlots DescentPackedPrivateMenu
open scoped Classical
noncomputable section
variable {D L cap n r Ht l field : ℕ}
def rootCell (r n : ℕ) (p : Code r×Option (Fin (2^n))) := cell r (p.1.val,p.2)
def sourceCell (v : Packet D L cap n r field) (which : Bool) (p : Code r×Option (Fin (2^n)))
    (root : Fin (rows r (2^n))) (i : Fin L) (s : Fin (2*cap)) : Slot :=
  let own:=localWord v i
  let peerData:=arrival v which i s
  let prior:=peerData.elim 0 (fun j=>
    if ok : j.2/2<rows r (2^n) then score v (root,j.1.succ,⟨j.2/2,ok⟩) else 0)
  ⟨peerData.isSome,decide (own/2=rootCell r n p),decide (own%2=1),
    peerData.elim false (fun j=>decide (j.2%2=1)),prior⟩

def existsAt (v : Packet D L cap n r field) (p : Code r×Option (Fin (2^n))) : Bool :=
  (List.finRange L).any (fun i=>decide (localWord v i/2=rootCell r n p))

def key (which : Bool) (p : Code r×Option (Fin (2^n))) (v : Packet D L cap n r field) :
    Key (n:=n) r Ht (L*(2*cap)) l :=
  if existsAt v p then
    if ok : rootCell r n p<rows r (2^n) then
      let root:=⟨_,ok⟩
      let total:=score v (root,0,root)
      some (.inr (interval r p.1,optional p.2,
        DescentPackedFallbackTree.pack Ht (Nat.clog 2 total) (fun j=>
          let ix:=finProdFinEquiv.symm j
          pick Ht total (sourceCell v which p root ix.1 ix.2))))
    else none
  else none

theorem absent (which : Bool) (p : Code r×Option (Fin (2^n))) (v : Packet D L cap n r field)
    (empty : ∀i,localWord v i/2≠rootCell r n p) : key (Ht:=Ht) (l:=l) which p v=none := by
  simp [key,existsAt,List.any_eq_true,empty]

theorem present (which : Bool) (p : Code r×Option (Fin (2^n))) (v : Packet D L cap n r field)
    (seen : ∃i,localWord v i/2=rootCell r n p) (room : rootCell r n p<rows r (2^n)) :
    let root:=(⟨_,room⟩ : Fin (rows r (2^n)))
    let total:=score v (root,0,root)
    key (Ht:=Ht) (l:=l) which p v=some (.inr (interval r p.1,optional p.2,
      DescentPackedFallbackTree.pack Ht (Nat.clog 2 total) (fun j=>
        let ix:=finProdFinEquiv.symm j
        pick Ht total (sourceCell v which p root ix.1 ix.2)))) := by
  have occupied : existsAt v p=true:=by simpa [existsAt,List.any_eq_true] using seen
  simp [key,occupied,room]

end
end Hierarchy.DescentFallbackPeriod

end OAI
