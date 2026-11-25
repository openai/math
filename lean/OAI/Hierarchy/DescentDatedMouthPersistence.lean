import OAI.Hierarchy.DescentDatedOriginMouth
import OAI.Hierarchy.DescentOrdinaryOriginPersistence

namespace OAI
/-! The three newborn mouth fields are gathered from precisely the W clock that ran before
the native actor-origin pass. All source projections are recovered on that same execution. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryMouthReturn DescentPackedColony DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage.Chooser
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor w : ℕ) (A : v.ArgumentEntry) (match_ : A.Match v floor)

def originAndMouth (outBits : ℕ) (orig : Fin v.vector.lows→Refs v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity) : NativePhase w :=
  (v.originPrefix floor outBits w orig).seq (v.originPrefixMouth floor w A match_)

theorem gathered_mouth {nb mb} (outBits : ℕ)
    (allPages : References v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity)
    (orig : Fin v.vector.lows→Refs v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity)
    (V : Fin v.bornBook.args→Fin v.vector.lows→(v.mouthChart match_.newBlocks).Val nb mb)
    (chip : Fin v.bornBook.hosts→Fin v.bornBook.groups→Cell v.bornBook.chipBits) (m : Memory w)
    (room : allPages.Room w (v.vectorStart floor))
    (prior : ∀a l,Measured (v.mouthRef A match_ a l) (V a l) v.resolver.nodes (v.vector.lanes*v.vector.radix) (v.vectorStart floor) m)
    (oldFit : (A.chipBank v floor).Fits w (v.vectorStart floor)) (span : v.bornBook.rows≤(A.chipBank v floor).size)
    (old : Reads (A.chipBank v floor) chip v.bornBook.lanes m)
    (maskFit : ∀l,(mask (orig l)).Fits w (v.vectorStart floor))
    (lanes : v.bornBook.lanes=v.vector.lanes*v.vector.radix)
    (same : v.bornBook.groups=v.vector.groups*v.vector.radix)
    (space : v.originMouthEnd floor<2^w) (a : Fin v.bornBook.args) (f : Fin 3) (b : Fin v.vector.radix) :
    let L:=v.mouthChart match_.newBlocks
    let first:=allPages.phase w (v.vectorStart floor)
    let both:=v.originAndMouth floor w A match_ outBits orig
    Reads (v.originMouthBank floor match_.newBlocks a f b)
      (DescentScalarBookReshape.book (fun l h g=>(L.vals V chip (finProdFinEquiv (a,f)) l).book
        v.resolver.nodes h (g.cast same.symm)) b) v.vector.lanes (both.image (first.image m)) :=by
  intro L first both
  have fst:=allPages.any (v.vectorStart floor) m room
  have below:v.vectorStart floor≤v.routedStart floor:=v.vector_before floor
  have end_ : v.routedStart floor≤v.originPortEnd floor:=by rw [v.originPort_span];exact Nat.le_add_right ..
  have original:=v.originPrefix_run floor outBits w orig (first.image m)
    (fun l=>ProtocolRAMGeneratedWrite.fits_mono _ below (maskFit l)) ((Nat.le_add_right ..).trans_lt space)
  let mid:=(v.originPrefix floor outBits w orig).image (first.image m)
  have keep (u) (early : u<v.vectorStart floor) : mid u=m u :=
    (original.2 u (.inl (early.trans_le below))).trans (fst.2 u (.inl early))
  have seen:=reads_before _ chip m mid old keep oldFit span
  have wide : L.endAddress (v.originPortEnd floor)<2^w:=by rwa [v.mouth_translated]
  exact L.measured_issued _ _ _ mid V chip room.lanes room.radix same wide
    (L.measured_since _ _ _ V (v.vectorStart floor) m mid (below.trans end_) keep chip prior
      (bank_before oldFit (below.trans end_)) span seen lanes wide) a f b

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
