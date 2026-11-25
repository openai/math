import OAI.Hierarchy.DescentResetTrunkSheet
import OAI.Hierarchy.DescentResetTrunkGather
import OAI.Hierarchy.DescentResetRankedCandidates

namespace OAI
/-! # The final native tally on the original compact post-reset actor enumeration -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

open DescentResetFieldAssembler DescentSIMDLookup DescentPackedZip DescentResetTrunkIssue ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "groups" => S.groupCount (i+1)
local notation "half" => 2^(S.groupWidth k tail i+k-(B.terminals).commonDepth)*(2*input.placement.cap)
local notation "rawWord" => DescentResetFieldAssembler.raw
local notation "X₀" => 2^k
variable {word b M : ℕ}
local notation "PA" => B.next.placement

def compactRelay {H : ℕ} (rack : Fin H→Option B.next.V) (x : Fin X₀) (j : Fin half)
    (v : Fin H) (g₀ : Fin groups) : Meta:=(rack v).elim .blank (fun t=>hostStem B ((g₀,t),x) j)

theorem compact_sheet {H : ℕ} (rack : Fin H→Option B.next.V) (posted : Fin H→Meta)
    (geometry : ∀r v,rack r=some v→posted r=hostShape B v)
    (fieldFits : ∀r j,digits (posted r) j<2^b)
    (base : ℕ) (head : Expr) (stem : Fin X₀→Fin half→Expr) (m : Memory word)
    (headfit : head.Fits word base) (stemfit : ∀x j,(stem x j).Fits word base)
    (heads : Source head (fun v (_ : Fin groups)=>rawWord b (posted v)) M m)
    (gathered : ∀x j,Source (stem x j) (fun v g₀=>rawWord b (compactRelay B rack x j v g₀)) M m)
    (degree : (PA).degree+1<2^b) (cap : (PA).cap<2^b) (space : DescentResetTrunkIssue.endAddress base b M<2^word) :
    let last:=DescentResetTrunkIssue.memory base b M m
    (DescentResetTrunkIssue.program base b M word).Exec m last (4+10*(3*2^(DescentResetTrunkIssue.width b M))) ∧
      (∀x,(DescentResetTrunkIssue.issue base b M head (stem x)).Fits word (DescentResetTrunkIssue.endAddress base b M)) ∧
      (∀x,Source (DescentResetTrunkIssue.issue base b M head (stem x)) (fun v g₀=>rawWord b
        (actualMeta B rack x (trunkCandidate B) v g₀)) M last) ∧
      (∀i₀,i₀<base ∨ DescentResetTrunkIssue.endAddress base b M≤ i₀→last i₀=m i₀) ∧
      DescentStaticWordColumn.names (DescentResetTrunkIssue.program base b M word)=15*(3*2^(DescentResetTrunkIssue.width b M)+1) ∧ CheapCode (DescentResetTrunkIssue.program base b M word):=by
  let shaped (_ : Fin X₀) (v : Fin H) (_ : Fin groups):=posted v
  have small (x : Fin X₀) (j : Fin half) (v : Fin H) (g₀ : Fin groups) (f₀ : Fin 7):
      digits (compactRelay B rack x j v g₀) f₀<2^b:=by
    cases found : rack v with
    | none=>simp only [compactRelay,found,Option.elim_none];fin_cases f₀ <;> exact Nat.two_pow_pos _
    | some t=>simpa only [compactRelay,found,Option.elim_some] using stem_digits B ((g₀,t),x) j f₀ degree cap
  have tallies (x : Fin X₀) (v : Fin H) (g₀ : Fin groups) :
      (∑j,(face false (compactRelay B rack x j v g₀)).toNat)<2^b:=by
    cases found : rack v with
    | none=>simp [compactRelay,found,face,Meta.blank]
    | some t=>simpa only [compactRelay,found,Option.elim_some] using trunk_sum_room B ((g₀,t),x) degree cap
  have decoded (x : Fin X₀) (v : Fin H) (g₀ : Fin groups) : DescentResetTrunkIssue.complete (shaped x v g₀)
      (∑j,(face false (compactRelay B rack x j v g₀)).toNat)=actualMeta B rack x (trunkCandidate B) v g₀:=by
    cases found : rack v with
    | none=>simp [DescentResetTrunkIssue.complete,compactRelay,found,face,Meta.blank,actualMeta]
    | some t=>
      have sc:=geometry v t found
      simpa only [shaped,sc,actualMeta,found,Option.elim_some,compactRelay] using trunk_raster B ((g₀,t),x)
  have result:=DescentResetTrunkIssue.run base (fun (_ : Fin X₀)=>head) stem m shaped
    (compactRelay B rack) (fun _=>headfit) stemfit (fun _=>heads) gathered (fun _ v _=>fieldFits v) small tallies space
  exact ⟨result.1,result.2.1,fun x=>by simpa only [decoded] using result.2.2.1 x,result.2.2.2⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
