import OAI.Hierarchy.DescentPreparedPrimitiveRole

namespace OAI
/-! # One measured prior bank establishes every active depth and every zero guard of the primitive publisher -/
namespace Hierarchy.DescentPrimitiveBirth.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHostDirectory DescentIssuedRotorRoles
open DescentResetHostSize DescentSharedLeafLookup
open DescentSixParty.Chronology DescentFallbackPeriod.Projected DescentLaneGates DescentResetGates
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (z : DescentPrimitiveBirth.Layout) {D cap field w : ℕ}
local notation "R" => z.residual
local notation "N" => z.rotorBits
local notation "L" => 2^R
local notation "P" => z.placement
local notation "J" => (P).groups*(P).blocks
local notation "H" => (P).oldHosts
local notation "M" => z.sourceLanes
local notation "count" => DescentRotorWindowArchive.count D L cap

def measuredFields (matrix : Fin H→Fin J→Fin count→Cell field) (capacity depth : Fin H→Fin J→Cell field)
    (flag : DescentColonies.Block R→Fin H→Fin J→Cell field) (q : Fin z.roots) (l : Fin (R+1)) (h : Fin H) (g : Fin J) :
    z.GuardPacket D cap field:=
  let p:=rootParts R N q
  let sample : DescentColonies.Block R:=if yes:p.2.1.val<2^l.val then
    DescentRotorRootPresence.sample ⟨(l.val,p.2.1.val),mem_codes (by omega) yes⟩ else 0
  priorFields (D:=D) (r:=R) (cap:=cap) (matrix h g) (capacity h g) (depth h g) (flag sample h g)

variable {hw : ℕ} (src : RootSources D (2^z.residual) cap) (board : NonlinearExpanders.Graph z.rotorBits hw)
    (packet f Ht C batches layerBits : ℕ) (primitive : CanonicalTag (2^z.rotorBits)→Cell z.rootBits)
    (factor hubBits : ℕ) (neighbors hubs : Bank) (start cmp : ℕ)
    (pair : ℕ→Header→Fin D→Fin D→Fin 6→Expr) (bookPage : RootPage z.residual (2^z.rotorBits))
local notation "book" => src.reserved (field:=field) board packet f Ht C batches z.stop layerBits primitive
  H factor hubBits neighbors hubs start J M cmp pair bookPage

theorem observed_prepared {previous K maxAge hh ll t c oldGroups : ℕ}
    (a : Receiver D cap previous N R c H oldGroups K maxAge M hh ll t field Ht w)
    (pitch : J=2^c) (space : a.PreparedFits book) (original : Memory w)
    (matrix : Fin H→Fin J→Fin count→Cell field) (capacity level : Fin H→Fin J→Cell field)
    (flag : DescentColonies.Block R→Fin H→Fin J→Cell field)
    (mx : ∀side root i,Source (((book).good side root (.inl false)).2.reads i) (fun h g=>matrix h g i) M (a.preparedMid book space original))
    (cp : Source src.priorCap capacity M (a.preparedMid book space original))
    (dp : Source src.relativeDepth level M (a.preparedMid book space original))
    (sites : ∀x,Source (src.self x) (flag x) M (a.preparedMid book space original))
    (held : ∀side root gate i,(((book).good side root (.inr gate)).2.reads i).Fits w
      ((RootTemplates.arena (a.headerEnd book) H (2^c) M R N D).middle ((rootIndex R (2^N) (side,.inl (root,.inr gate))).val)))
    (short : M*max (field*guardInputs D L cap) (z.rootBits*z.stop)≤w/2) (pos : 0<M)
    (floor : ℕ) (later : Memory w) (past : a.preparedEnd book≤floor) (room : floor<2^w)
    (frame : ∀j,j<floor→later j=a.preparedImage book space original j) :
    z.Observed (guards (a.headerEnd book) H J M R N D) later (fun h g=>activeDepth R (level h g).val)
      (z.observedWord packet f batches layerBits primitive (z.measuredFields matrix capacity level flag)):=by
  apply z.observed_depth packet f batches layerBits primitive (z.measuredFields matrix capacity level flag)
    (a.headerEnd book) later (fun h g=>(level h g).val)
  · intro q l B yes
    let p:=rootParts R N q
    by_cases fit:p.2.1.val<2^l.val
    · let root : Code R:=⟨(l.val,p.2.1.val),mem_codes (by omega) fit⟩
      have picked:B=guardBank (a.headerEnd book) H J M R N D (p.1,.inl (root,.inr p.2.2)):=by
        simpa [guards,rootPage,p,fit,root] using yes.symm
      subst B
      have actual:=issued_original src board packet f Ht C batches z.stop layerBits primitive H factor hubBits neighbors hubs
        start J M cmp pair bookPage a pitch space original p.1 root p.2.2 matrix capacity level (flag (DescentRotorRootPresence.sample root))
        (mx p.1 root) cp dp (sites _) (held _ _ _) short pos floor later past room frame
      simpa [←pitch,observedWord,measuredFields,p,fit,root] using actual
    · simp [guards,rootPage,p,fit] at yes
  · intro q l h g
    exact congrArg Fin.val (prior_level (D:=D) (r:=R) (cap:=cap) _ _ _ _)

end
end Hierarchy.DescentPrimitiveBirth.Layout

end OAI
