import OAI.Hierarchy.DescentIssuedMeasuredReset
import OAI.Hierarchy.DescentMeasuredInvoice

namespace OAI
/-! # From original branch measurements through the programmed optimizer to its installed geometry -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentGL DescentColonies DescentResetInvoice DescentBaseProfile
open DescentRotor DescentMixedRouter DescentFineTerminals StarKeys
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open DescentLinearLayouts Computability.VPVNP.BurstRAM PrivateRAM DescentBaseVariance DescentIntegerScale DescentGL.PhysicalTrajectory
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentMeasuredMixer DescentMeasuredWeights DescentMeasuredHeader DescentPackedExchange
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {J V : Type}
  [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G q ε J V k) (S : AtomSchedule) {i : ℕ}

variable {n h C bitsR f g cut K m : ℕ} (board : Graph n h)
local notation "grain" => A.z*G.b
local notation "full" => A.wire*grain*A.cap
local notation "positions" => (fun u => Prod.snd (A.pos u))
local notation "ht" => 2*max (terminalDepth A.degree (2^n) f g false) (terminalDepth A.degree (2^n) f g true)

theorem mutualDegree (v : V) : (A.mutual v).card≤A.degree :=
  (Finset.card_filter_le ..).trans (A.degreeBound v)

def HeaderRun {w : ℕ} (k start H Δ bits gainBits : ℕ) (L : Tape) (D : DataTape) (m : Memory w) (μ : Layout k) : Prop :=
  let tab := mixerTab (H:=H) (k:=k) (Δ:=Δ) start (origin start H k Δ)
  let base := workBase start H k Δ
  let count := H*(k+1)+H*Δ
  ∃ out : Memory w,((emit L D w start H k Δ).seq (stages w k base bits gainBits tab)).Exec m out
    (clocks L H k Δ+measuredTime w k base bits gainBits tab) ∧
    (∀j : Fin k,out (pointer k (mixerBase k base count) j.val)=((rowIndex k (rowFunctional μ j)).val:Word w)) ∧
    (∀z : Fin (2^k),out (outputBase k (mixerBase k base count)+z.val)=
      ((finFunctionFinEquiv (μ (DescentGLScoreRAM.vec z))).val:Word w)) ∧ ∀a<start,out a=m a

section Source
variable {digits : Block m≃J×Block k} (H : A.MixerHeader digits) (L : Tape) (D : DataTape)
variable {w start payloadBits gainBits : ℕ}
local notation "sh" => H.sites
local notation "count" => sh*(m+1)+sh*A.degree
local notation "b" => H.depth A f
local notation "port" => atPort H.site A.mutual A.mutualDegree
local notation "whereRow" => portRow (k:=m) H.site A.mutual A.mutualDegree b
local notation "lev" => inputLevels (k:=m) b

/-- The old resident rows, the fixed schedule's incoming metadata, and the
word and address bounds for a measured reset. The terms of the quadratic
collision estimator are produced after this state. -/
structure MeasuredMemory (flow : Port sh A.degree→Block m→ℕ) (mem : Memory w) : Prop where
  oldPointers : Fits L w sh m A.degree start
  columns : DataFits D w sh m A.degree (origin start sh m A.degree)
  below : Before D start
  endRoom : endAddress start sh m A.degree<2^w
  presentSites : sh<2^w
  presentDepth : 2*m+1<2^w
  source : contents (k:=m) (Δ:=A.degree) L (b ∘ H.site.symm) (neighborSlot (degree:=A.degree) H.site A.mutual) f full K mem
  directory : dataStatic (H:=sh) (k:=m) (Δ:=A.degree) D mem
  measured : oldLoads D (fun v=>A.resetLoad digits (H.site.symm v)) flow mem
  ports : ∀c : Contacts A.mutual,flow (port c)=A.resetFlow digits c.1 c.2.val
  widths : payloadBits≤w ∧ gainBits≤w
  values : ∀i : Fin count,
    padded whereRow (level lev (inputDepth b) (pairDepth A.mutual b)) 0 i<2^w ∧
    padded whereRow (gain lev f full K) 0 i<2^gainBits ∧
    ∀z,padded whereRow (load lev (A.measuredSiteRow digits) (A.measuredContactRow digits)) (fun _=>0) i z<2^payloadBits

end Source

theorem issued_reset_emitted (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (ready : A.StateBounds S i) (realAge : i≤S.length)
    (digits : Block m≃J×Block k) (remaining : 2^(m-k)=S.groupCount i)
    (radix : S.radix=2^k) (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (fg : f≤g) (gk : g≤k) (km : k≤ m)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tail : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ))
    (H : A.MixerHeader digits) {w start payloadBits gainBits : ℕ} (L : Tape) (D : DataTape)
    (flow : Port H.sites A.degree→Block m→ℕ) (mem : Memory w) (initial : Layout m)
    (physical : A.MeasuredMemory (start:=start) (f:=f) (K:=K) (payloadBits:=payloadBits) (gainBits:=gainBits) H L D flow mem)
    (scaleBits countBits rateBits massBits : ℕ)
    (scale : 2^f*full≤2^scaleBits)
    (members : (∑v,(inputLevels (k:=m) (H.depth A f)) v)+Fintype.card (Contacts A.mutual)≤2^countBits)
    (rateLevel : ∀v (t : Fin ((inputLevels (k:=m) (H.depth A f)) v)),4*2^((t.val+7)/8)≤2^rateBits)
    (ratePair : K^2≤2^rateBits) (mass : ∀v,(∑i,A.measuredSiteRow digits v i)≤2^massBits)
    (thin : ∀c,(∑i,A.measuredContactRow digits c i)≤2^massBits)
    (available : 3*m+(scaleBits+countBits+rateBits+2*massBits)+2≤w) :
    ∃(Z : ResetInput (W.granular A.grainCount grain (A.grainCount_fit S ready)) (q*A.wire) ε h C ht)
      (T : Z.Terminals),Z.ActorBudget T A.records A.wire A.hist f g full ∧ Z.k=m ∧ T.commonDepth=m-k ∧ Z.n=n ∧
      Fintype.card Z.V=Fintype.card V ∧ Z.unit=grain ∧ Z.width=bitsR ∧ HEq Z.graph board ∧
      ∃ frame : Z.SourceFrame T positions (filled W.graph A.pos A.block digits) A.hub g,
        HeaderRun m start H.sites A.degree payloadBits gainBits L D mem frame.basis ∧
        (∀v,Z.placement.b (frame.host v)=H.depth A f v) ∧
        ResetInput.SourceFrame.Roster Z T positions (filled W.graph A.pos A.block digits) A.hub g frame
          (H.vertex A) A.mutual n f full A.wire K (fun v w j=>(A.resetFlow digits v w j:ℝ)) A.degree (A.resetLoad digits) ∧
        Z.placement.OrderedTickets (DescentOrderedReset.grains W A.grainCount order) := by
  apply issued_reset_from_roster_mixer A S board order ready realAge digits remaining radix fixed budget fcut fg gk km
    quota ports hK positiveRotor rows menu tail H (HeaderRun m start H.sites A.degree payloadBits gainBits L D mem)
  intro geom limits inc ep hB hh
  let b := H.depth A f
  have hk (v) : b v≤ m := (geom.bounds v).2.trans (Nat.sub_le _ _)
  let sh := H.sites
  let lev := inputLevels (k:=m) b
  let dpth := inputDepth (k:=m) b
  let pair := pairDepth A.mutual b
  let loc := portRow (k:=m) H.site A.mutual A.mutualDegree b
  let tab := mixerTab (H:=sh) (k:=m) (Δ:=A.degree) start (origin start sh m A.degree)
  let initialMem := primed L D start sh m A.degree mem
  have wordRoom : origin start sh m A.degree+(sh*(m+1)+sh*A.degree)*2^m<2^w := by
    have := physical.endRoom
    unfold endAddress workBase at this
    dsimp [sh];omega
  have primedRun : (emit L D w start sh m A.degree).Exec mem (primed L D start sh m A.degree mem) (clocks L sh m A.degree) :=
    (emit_exec L D start mem physical.oldPointers physical.columns wordRoom).1
  have dk := primed_heads H.site A.mutual A.mutualDegree b hk L D start physical.oldPointers f full K
    mem physical.source physical.presentSites physical.presentDepth
  have dv := primed_values H.site A.mutual A.mutualDegree b hk L D start physical.oldPointers physical.columns
    physical.below f full K (fun v=>A.resetLoad digits (H.site.symm v)) flow
    (A.measuredSiteRow digits) (A.measuredContactRow digits)
    (fun v => congrArg (A.measuredSiteRow digits) (H.site.symm_apply_apply v))
    (fun c=>by rw [physical.ports];rfl) mem physical.source physical.presentSites physical.presentDepth
    physical.directory physical.measured
  obtain ⟨out,μ,run,price,ptr,remix,keep⟩ := sparse_result lev loc dpth pair
    (A.measuredSiteRow digits) (A.measuredContactRow digits) f full K initialMem tab initial
    (global_room start sh m A.degree physical.endRoom) available hB physical.widths
    (source_segments start sh m A.degree physical.endRoom) dk dv physical.values
    (fun l d=>mixingWeightNumerator_bound lev dpth pair (A.measuredSiteRow digits) (A.measuredContactRow digits)
      f full K l d scaleBits countBits rateBits massBits scale members rateLevel ratePair mass thin)
  have sym (v z) : z∈A.mutual v ↔ v∈A.mutual z := by simp [«mutual»,and_comm]
  refine ⟨μ,⟨out,@Procedure.Exec.then w (emit L D w start sh m A.degree)
    (stages w m (workBase start sh m A.degree) payloadBits gainBits tab) mem initialMem out
    (clocks L sh m A.degree) (measuredTime w m (workBase start sh m A.degree) payloadBits gainBits tab)
    (@primedRun) (@run),ptr,remix,?_⟩,?_⟩
  · intro a low
    exact (keep a (by unfold workBase origin;omega)).trans (primed_frame (H:=sh) (k:=m) (Δ:=A.degree) L D start mem low)
  · exact paid_of_subaverage A.mutual (A.resetLoad digits) (A.resetFlow digits) b hk sym A.degreeMin
      A.mutualDegree hB hK limits inc (ε/q) ep hh tail geom μ price

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
