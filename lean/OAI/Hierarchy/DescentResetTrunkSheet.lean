import OAI.Hierarchy.DescentResetTrunkShapeRead
import OAI.Hierarchy.DescentResetTrunkGather
import OAI.Hierarchy.DescentResetRankedCandidates

namespace OAI
/-! # The actual seven-field trunk word on every group of the reset candidate sheet -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "addresses" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


open DescentResetFieldAssembler DescentIssuedFallbackPanel DescentNextSignedWindow
local notation "rows" => blocks B
local notation "End" => (old).graph.Edge
local notation "Home" => (T).home
local notation "full" => totalLocal B
local notation "AC" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "before" => input.order.trans Fin.valEmbedding
local notation "half" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*(AC).cap)



open DescentPackedZip DescentSIMDLookup DescentResetTrunkIssue ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "Node₀" => Node (Z).V ((Z).V×DescentContacts.Endpoint (2^(Z).n)) (DescentCommonPalette.rotor (Z).graph).Site
local notation "short" t => DescentRelativeContacts.shortName (T).commonDepth ((T).code t)
local notation "high_" u => (addresses).symm ((u).1.1,(u).2)
local notation "hi_" t => DescentChosenRouter.coarseName (T).commonDepth ((T).code t)
local notation "touch" u t => ((rows).src (trunkParent B t)=u ∨ (rows).dst (trunkParent B t)=u)


local notation "rank" => (Z).rawHostRank T vertexCode


local notation "radius" => (Z).k-(T).commonDepth
local notation "depth_" => GroupStage.depthBound D n f g
local notation "shapeRank" => localRank (Z).graph radius depth_
local notation "roster_" => DescentDenseHostOrder.roster (Z).graph radius depth_


open DescentPackedColony DescentSortedRoster
local notation "rawWord" => DescentResetFieldAssembler.raw
local notation "pitch" => Fintype.card input.V*(roster_).card
local notation "description" => DescentResetTrunkPalette.description (Z).graph radius depth_


local notation "X₀" => 2^k
variable {word b M : ℕ}
local notation "PA" => B.next.placement

private theorem shape_integer_digits {H : ℕ} (ns : Fin H→Fin 3→Option (Fin H)) (h₀ : Fin H)
    (entry : Option (Fin H × Fin H × Bool))
    (wide : 4<2^b) (j : Fin 7) :
    digits (DescentResetTrunkScalar.integer ns h₀ entry) j<2^b:=by
  have pos : 1<2^b:=by omega
  have digit (t : Fin H) : DescentSortedRoster.before (DescentResetTrunkScalar.peers ns) h₀ t<2^b :=
    (Nat.le_of_lt_succ (DescentResetTrunkScalar.score_bound ns h₀ t)).trans_lt wide
  cases entry with
  | none=>simp only [DescentResetTrunkScalar.integer];fin_cases j <;> exact Nat.two_pow_pos _
  | some p=>
    rcases p with ⟨l,r,c⟩
    fin_cases j <;> first | exact pos | exact digit _ | exact (Bool.toNat_le _).trans_lt pos | exact Nat.two_pow_pos _

/-- The real descriptor's alphabet does not increase with the number of actors. -/
theorem shape_digits (ns : Fin pitch→Fin 3→Option (Fin pitch)) (h₀ : Fin pitch)
    (wide : 4<2^b) (j : Fin 7) :
    digits (DescentResetTrunkScalar.integer ns h₀ (description h₀)) j<2^b:=
  shape_integer_digits ns h₀ (description h₀) wide j

theorem physical_digits (u : Host) (j : Fin full) (f₀ : Fin 7)
    (degree : (PA).degree+1<2^b) (cap : (PA).cap<2^b) :
    digits («meta» B u (localOrigin B u j)) f₀<2^b:=
  meta_room B (fun (_ : Fin 1)=>some u.1.2) degree cap u.2 j 0 u.1.1 f₀

theorem stem_digits (u : Host) (j : Fin half) (f₀ : Fin 7)
    (degree : (PA).degree+1<2^b) (cap : (PA).cap<2^b) :
    digits (hostStem B u j) f₀<2^b:= by
  cases status : trunkLabels B u.1.2 with
  | none=>simp only [hostStem,status];fin_cases f₀ <;> exact Nat.two_pow_pos _
  | some p=>simpa only [hostStem,status] using
      physical_digits B (b:=b) (portAt B u p.right) (incomingCandidate B j) f₀ degree cap

theorem trunk_sum_room (u : Host) (degree : (PA).degree+1<2^b) (cap : (PA).cap<2^b) :
    (∑j,(face false (hostStem B u j)).toNat)<2^b:=by
  cases status : trunkLabels B u.1.2 with
  | none=>simp [hostStem,status,face,Meta.blank]
  | some p=>
    have eqn:=congrArg Meta.units (trunk_raster B u)
    have live : (hostShape B u.1.2).live=true:=by simp [hostShape,status]
    by_cases positive : 0<∑j,(face false (hostStem B u j)).toNat
    · have counts : (∑j,(face false (hostStem B u j)).toNat)=(«meta» B u (localOrigin B u (trunkCandidate B))).units:=by
        simpa [DescentResetTrunkIssue.complete,live,positive] using eqn
      rw [counts];exact physical_digits B u (trunkCandidate B) 6 degree cap
    · have zero : (∑j,(face false (hostStem B u j)).toNat)=0:=by omega
      rw [zero];exact Nat.two_pow_pos _

def relayRecord (rack : Fin pitch→Option B.next.V) (x : Fin X₀) (j : Fin half)
    (v : Fin pitch) (g₀ : Fin groups) : Meta:=(rack v).elim .blank (fun t=>hostStem B ((g₀,t),x) j)

/-- Any unused rectangular receiver produces precisely the seven zero fields.
All three uniform binary-list tables are physically emitted in the execution. -/
theorem trunk_sheet (ns : Fin pitch→Fin 3→Option (Fin pitch)) (rack : Fin pitch→Option B.next.V)
    (named : ∀v t,rack v=some t → rank t=v)
    (neighbors : ∀v,present ns (rank v)=((PA).near v).map (rank))
    (base : ℕ) (head : Expr) (stem : Fin X₀→Fin half→Expr) (m : Memory word)
    (headfit : head.Fits word base) (stemfit : ∀x j,(stem x j).Fits word base)
    (heads : Source head (fun v (_ : Fin groups)=>rawWord b (DescentResetTrunkScalar.integer ns v (description v))) M m)
    (gathered : ∀x j,Source (stem x j) (fun v g₀=>rawWord b (relayRecord B rack x j v g₀)) M m)
    (degree : (PA).degree+1<2^b) (cap : (PA).cap<2^b) (space : DescentResetTrunkIssue.endAddress base b M<2^word) :
    let last:=DescentResetTrunkIssue.memory base b M m
    (DescentResetTrunkIssue.program base b M word).Exec m last (4+10*(3*2^(DescentResetTrunkIssue.width b M))) ∧
      (∀x,(DescentResetTrunkIssue.issue base b M head (stem x)).Fits word (DescentResetTrunkIssue.endAddress base b M)) ∧
      (∀x,Source (DescentResetTrunkIssue.issue base b M head (stem x)) (fun v g₀=>rawWord b
        (actualMeta B rack x (trunkCandidate B) v g₀)) M last) ∧
      (∀i₀,i₀<base ∨ DescentResetTrunkIssue.endAddress base b M≤ i₀→last i₀=m i₀) ∧
      DescentStaticWordColumn.names (DescentResetTrunkIssue.program base b M word)=15*(3*2^(DescentResetTrunkIssue.width b M)+1) ∧ CheapCode (DescentResetTrunkIssue.program base b M word):=by
  have four : 4<2^b:=by simpa only [B.next.branch] using degree
  let shaped (_ : Fin X₀) (v : Fin pitch) (_ : Fin groups):=DescentResetTrunkScalar.integer ns v (description v)
  have small (x : Fin X₀) (j : Fin half) (v : Fin pitch) (g₀ : Fin groups) (f₀ : Fin 7):
      digits (relayRecord B rack x j v g₀) f₀<2^b:=by
    cases found : rack v with
    | none=>simp only [relayRecord,found,Option.elim_none];fin_cases f₀ <;> exact Nat.two_pow_pos _
    | some t=>simpa only [relayRecord,found,Option.elim_some] using stem_digits B ((g₀,t),x) j f₀ degree cap
  have tallies (x : Fin X₀) (v : Fin pitch) (g₀ : Fin groups) :
      (∑j,(face false (relayRecord B rack x j v g₀)).toNat)<2^b:=by
    cases found : rack v with
    | none=>simp [relayRecord,found,face,Meta.blank]
    | some t=>simpa only [relayRecord,found,Option.elim_some] using trunk_sum_room B ((g₀,t),x) degree cap
  have decoded (x : Fin X₀) (v : Fin pitch) (g₀ : Fin groups) : DescentResetTrunkIssue.complete (shaped x v g₀)
      (∑j,(face false (relayRecord B rack x j v g₀)).toNat)=actualMeta B rack x (trunkCandidate B) v g₀:=by
    cases found : rack v with
    | none=>simp [DescentResetTrunkIssue.complete,relayRecord,found,face,Meta.blank,actualMeta]
    | some t=>
      have h:=named v t found
      have sc:=trunk_scalar B t ns (neighbors t)
      rw [h] at sc
      simpa only [shaped,sc,actualMeta,found,Option.elim_some,relayRecord] using trunk_raster B ((g₀,t),x)
  have result:=DescentResetTrunkIssue.run base (fun (_ : Fin X₀)=>head) stem m shaped
    (relayRecord B rack) (fun _=>headfit) stemfit (fun _=>heads) gathered (fun _ v _=>shape_digits B ns v four) small tallies space
  exact ⟨result.1,result.2.1,fun x=>by simpa only [decoded] using result.2.2.1 x,result.2.2.2⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
