import OAI.Hierarchy.DescentNamedSeedHeadData
import OAI.Hierarchy.DescentSeedHeaderEnvelope
import OAI.Hierarchy.DescentChosenExteriorHeadWidths
import OAI.Hierarchy.DescentSeedDirectoryCapacity
import OAI.Hierarchy.DescentTerminalScheduledExtraRate
import OAI.Hierarchy.DescentNamedWideOriginalInvoice

namespace OAI
/-! # Uniform initial address for the authentic dated calendar -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentPrimitivePalette
open DescentMixedRouter DescentTerminalEpochChart DescentTerminalEpochDecoder DescentResetInvoice
open DescentDatedSeedStartup DescentPackedEpochShelves DescentPackedProfileInstall DescentSeedRoot
open Catalyst Filter Computability.BorderVNP.Crossing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)
variable (t f g rate drift : ℕ)
local notation "J_" h:arg β:arg => Nat.log 2 h/(2*β)
local notation "cells_" m:arg => groupBits t m (hostRate t rate) (capRate G t g) (cutRate t f g)
local notation "S_" θ:arg β:arg h:arg M:arg => stageNumbers G t (J_ h β) f g rate M (tail θ (J_ h β))
local notation "κ" => 1+(hostRate t rate+capRate G t g)*(t+1)+8+cutRate t f g
structure SeedCut (τ β : ℕ) : Prop where
  large : 20≤β
  reserve : 2*localSocketRate G t g≤τ
  packing : 2*(localSocketRate G t g+(τ+κ+4))+Nat.clog 2 G.b*(t+1)≤β
  cohort : 2*(τ+groupRate G t f g rate+(6*(terminalDegree G t f g rate+1)+19))≤β
  route : 2*((τ+groupRate G t f g rate+4)+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2)≤β

/-- A single exponent covers arbitrary original normalized profiles mounted in
the physical header, with the terminal bin and rows chosen by the caller. -/
theorem scheduled_seed_head_rate (n degree₀ C : ℕ) (branch : G.b≤2^(capRate G t g)) :
    ∃K:ℕ,∀τ β,SeedCut G t f g rate τ β→∀ᶠ h:ℕ in atTop,
      ∀M,2^h≤M→M≤(2^h)^2→
      let S:=S_ τ β h M
      let k:=cells_ (J_ h β)
      let θ:=tail τ (J_ h β)
      let W:=NativeBranch.binLimit (k:=k) S
      let q:=headArity G S
      let p:=headGrain G S k h
      ∀ {cp pins : ℕ} (X : Approximation F cp pins) {A:Type} (steps : List (Source A))
        (H degree wire hist bins raw:ℕ),
      10*(X.size+1)≤M → Fintype.card (Vertex X)≤H → H≤hostRows M →
      steps.length≤S.length → seatBill steps≤S.length*S.batch →
      bins*W≤terminalPool X G S p q W n degree₀ C f g+W → raw≤terminalRawRows X G S p q n degree₀ C f g →
      (originalSeedHead G op drift X steps S k θ h H degree wire hist bins raw).floor G op t f g drift h≤2^(K*h) :=by
  obtain ⟨L,appendix⟩:=scheduled_extra_rate G op drift t f g rate n degree₀ C branch
  obtain ⟨D,directory⟩:=seed_directory_at G t f g rate
  let A:=max L D
  obtain ⟨K,seed⟩:=SeedHeader.common G op t f g drift A
  refine ⟨K,?_⟩
  intro τ β cut
  have large:=cut.large
  filter_upwards [seed,chosen_exterior_head_widths G t f g rate τ β cut.large cut.reserve cut.packing,
    early_native_packing G t f g rate τ β cut.large cut.reserve cut.packing,
    early_matrix_words G t f g rate τ β cut.large,appendix τ β (by omega) cut.cohort cut.route,
    eventually_ge_atTop 1] with h paid widths slices matrices extra nonzero
  intro M low high S k θ W q p cp pins X actor steps H degree wire hist bins raw fit enough padded levels seats amount reads
  let j:=headChunk G S
  let r:=headRest G S k θ
  have chosen:=widths M
  obtain ⟨shape,replicas,_,_,_⟩:=slices M
  have matrix:=(matrices M).2.2
  have counts : S.copies≤2^h:=by
    rw [replicas]
    apply Nat.pow_le_pow_right (by decide)
    rw [←shape]
    omega
  have depth : (J_ h β)≤h:=(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have siteSize : M≤4^h:=by
    calc M ≤ (2^h)^2:=high
         _ = 4^h:=by rw [←pow_mul,Nat.mul_comm h 2,pow_mul];rfl
  have src:=directory h (J_ h β) M (tail τ (J_ h β)) nonzero depth siteSize counts
  have lbound : 2^(L*h)≤2^(A*h):=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_left ..))
  have dbound : 2^(D*h)≤2^(A*h):=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right ..))
  apply paid
  refine ⟨src.1.trans (Nat.mul_le_mul_right _ (le_max_right ..)),le_rfl,depth,enough,
    padded.trans (src.2.2.1.trans dbound),?_,src.2.2.2.1.trans dbound,rfl,
    levels.trans (src.2.2.2.2.1.trans dbound),seats.trans (src.2.2.2.2.2.trans dbound),
    chosen.1,chosen.2.1,chosen.2.2,?_⟩
  · exact (show X.size+1≤M by omega).trans (src.2.1.trans dbound)
  · exact (extra M low high X j r bins raw fit shape.symm amount reads).trans lbound

/-- Counts on the exact physical chart used by the ballot machine. -/
theorem original_head_directory {cp pins : ℕ} (X : Approximation F cp pins) (S : AtomSchedule)
    {k cut frozen n stage C p : ℕ} (ordinary : OrdinaryRates G S k cut)
    (reset : ResetRates G S k (atRound S.rounds) n stage C f g cut frozen) (branch : G.b≤2^S.capGain)
    (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
    (shorten : reentryRate stage C*(1-(2-G.rate)/4)^S.rounds≤1/2) (w : ℕ) (fit : S.firstWidth G.b p<2^w) :
    let ss:=(normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout
    ss.length≤S.length ∧ seatBill ss≤S.length*S.batch :=by
  let rs:=(normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
  let o:=inputOrder X G S ordinary reset branch positive room shorten
  let ss:=(normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout
  have shape:=epochs_layout G _ _ rs o (seedChart X S.copies (S.firstWidth G.b p) w fit)
  have len : ss.length=S.height*S.rounds:=by simpa [ss,rs,o,normalizedPackedChart,packedChart,seedChart] using shape.1
  have rows : seatBill ss=epochSeats G _ _ rs:=by simpa [ss,rs,o,normalizedPackedChart,packedChart,seedChart,seatBill] using shape.2
  refine ⟨?_,rows.trans_le (seats X G S ordinary reset branch positive room shorten)⟩
  change ss.length≤(S.rounds+1)*S.height
  rw [len,Nat.add_mul,Nat.one_mul,Nat.mul_comm S.rounds]
  omega

/-- The genuine named chart and bin-count convention with its last, possibly
partial bin. The register is the first native date immediately after the scalar
header, the full seed program, its seven argument fields and the primitive bank. -/
theorem normalized_seed_floor_rate (n degree₀ C : ℕ) (branch : G.b≤2^(capRate G t g)) :
    ∃K:ℕ,∀τ β,SeedCut G t f g rate τ β→∀ᶠ h:ℕ in atTop,
      ∀M,2^h≤M→M≤(2^h)^2→
      let S:=S_ τ β h M
      let k:=cells_ (J_ h β)
      let θ:=tail τ (J_ h β)
      let W:=NativeBranch.binLimit (k:=k) S
      let q:=headArity G S
      let p:=headGrain G S k h
      ∀ {cp pins cut proofTail : ℕ} (X : Approximation F cp pins) (ordinary : OrdinaryRates G S k cut)
        (reset : ResetRates G S k (atRound S.rounds) n degree₀ C f g cut proofTail)
        (positive : 0<p) (room : 10*(X.size+1)≤M)
        (shorten : reentryRate degree₀ C*(1-(2-G.rate)/4)^S.rounds≤1/2)
        (w : ℕ) (fit : S.firstWidth G.b p<2^w) (H degree wire hist : ℕ),
      M≤H → H≤hostRows M →
      let steps:=(normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout
      let bins:=terminalBinCount X G S p q W n degree₀ C f g+1
      let raw:=terminalRawRows X G S p q n degree₀ C f g
      (originalSeedHead G op drift X steps S k θ h H degree wire hist bins raw).floor G op t f g drift h≤2^(K*h) :=by
  obtain ⟨K,cover⟩:=scheduled_seed_head_rate G op t f g rate drift n degree₀ C branch
  refine ⟨K,fun τ β paid=>(cover τ β paid).mono ?_⟩
  intro h fits M small high S k θ W q p cp pins cut proofTail X ordinary reset positive room shorten w fit H degree wire hist hosts padded
  let steps:=(normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout
  have card:=(DescentInitialHost.«initialize» X).2.1
  change Fintype.card (Vertex X)+Fintype.card (Cable X)+_≤10*(X.size+1) at card
  have source : Fintype.card (Vertex X)≤H:=by omega
  have actual:=original_head_directory G f g X S ordinary reset branch positive room shorten w fit
  apply fits M small high X steps H degree wire hist _ _ room source padded actual.1 actual.2 _ le_rfl
  rw [Nat.add_mul,Nat.one_mul,terminal_pool_eq]

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
