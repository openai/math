import OAI.Hierarchy.DescentNamedSeedEntryHeld

namespace OAI
/-! # Uniform address and input registers for the complete physical seed -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentCompiler DescentSixParty DescentSixParty.Chronology DescentSixParty.Chronology.RegisterTimeline
open DescentSeedRoot DescentWideSeedFlags DescentInitialHost DescentColonies Catalyst Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g drift h w K : ℕ) (v : SeedHeader.Input F)
local notation "l" => v.layout G t f g drift h
local notation "s" => v.width G
local notation "Z" => v.schedule.grainAt G.b v.p 0
local notation "pitch" => DescentDatedSeedStartup.Primitive.paletteLanes G op s Z h v.k
local notation "lo" => selectorBase v.circuit v.schedule.copies s h v.steps.length
local notation "menu" => fromProfiles G v.schedule board op v.k v.tail v.p f g drift v.degree h lo (v.base G h-1) v.steps
local notation "entry" => v.position G op t f g drift h

structure Ready : Prop where
  head : (entry).floor≤2^(K*h)
  space : (entry).floor<2^w
  machine : h≤w
  digits : 16*digitsNeeded s≤h
  live : 0<pitch
  printed : DescentPrimitivePalette.printedBits G s Z op*pitch≤w
  signed : DescentSignedCableCodec.width 3 256*(l).packedLanes≤w
  «fields» : (l).operandBits*(l).operandLanes≤w
  seedWidth : s<2^Nat.clog 2 (s+1)
  geometry : Geometry G v.schedule menu v.k w 0 entry

variable {radix : v.schedule.radix=2^v.k} {count : Fintype.card (DescentSeedRoot.Vertex v.circuit)≤v.hosts}
    {q ε : ℝ} {wire z₀ : ℕ} {c : (DescentInitialHost.initialGroup v.circuit v.schedule.copies (v.width G)).Choice}

theorem Ready.held (ready : v.Ready G board op t f g drift h w K)
    (o : DescentSixParty.SeedNamed.Origin v.circuit (G:=G) (S:=v.schedule) (q:=q) (fee:=ε)
      (z:=z₀) (wire:=wire) c (v.schedule.initialDigits radix)) (m : Computability.VPVNP.BurstRAM.Memory w) :
    (entry).ports.held o.source (entry).floor (DescentDatedSeedStartup.Input.completeImage G op v.circuit
      (v.schedule.initialDigits radix) count l (v.base G h-1) h Z m) :=
  initial_held G op t f g drift h v radix count (q:=q) (ε:=ε) (wire:=wire) (z₀:=z₀) (c:=c) o m ready.digits ready.live ready.machine
    ready.signed ready.«fields» ready.space
end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentDatedSeedStartup DescentInitialHost
open DescentResetInvoice DescentTerminalEpochChart DescentTerminalEpochDecoder DescentMixedRouter
open DescentPackedEpochShelves DescentPackedProfileInstall DescentSeedRoot Catalyst Filter Computability.BorderVNP.Crossing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (t f g rate drift n₀ degree₀ C : ℕ)
local notation "J_" h:arg β:arg => Nat.log 2 h/(2*β)
local notation "cells_" m:arg => groupBits t m (hostRate t rate) (capRate G t g) (cutRate t f g)
local notation "S_" θ:arg β:arg h:arg M:arg => stageNumbers G t (J_ h β) f g rate M (tail θ (J_ h β))
local notation "κ" => 1+(hostRate t rate+capRate G t g)*(t+1)+8+cutRate t f g

def seedCutoff (τ : ℕ) :=
  max 20 (max (2*(localSocketRate G t g+(τ+κ+4))+Nat.clog 2 G.b*(t+1))
   (max (2*(τ+groupRate G t f g rate+(6*(terminalDegree G t f g rate+1)+19)))
        (2*((τ+groupRate G t f g rate+4)+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2))))

private theorem seedBranchBound : G.b≤2^(capRate G t g) := by
  have size : G.b≤capRate G t g := by unfold capRate; omega
  exact size.trans Nat.lt_two_pow_self.le

/-- Original seed words and complete initial venue for every instance normalized at this payload. -/
def NormalizedEntry (K τ β h : ℕ) : Prop :=
  ∀M,2^h≤M→M≤(2^h)^2→(∃a,M=2^a)→
      let S:=S_ τ β h M
      let k:=cells_ (J_ h β)
      let θ:=tail τ (J_ h β)
      let W:=NativeBranch.binLimit (k:=k) S
      let q:=headArity G S
      let p:=headGrain G S k h
      ∀ {cp pins cut frozen : ℕ} (X : Approximation F cp pins) (ordinary : OrdinaryRates G S k cut)
        (reset : ResetRates G S k (atRound S.rounds) n₀ degree₀ C f g cut frozen)
        (positive : 0<p) (room : 10*(X.size+1)≤M)
        (shorten : reentryRate degree₀ C*(1-(2-G.rate)/4)^S.rounds≤1/2)
        (w : ℕ) (fit : S.firstWidth G.b p<2^w) (H degree wire hist : ℕ),M≤H→H≤hostRows M→K*h<w →
      let steps:=(normalizedPackedChart X G S ordinary reset (seedBranchBound G t g) positive room shorten w fit).layout
      let bins:=terminalBinCount X G S p q W n₀ degree₀ C f g+1
      let raw:=terminalRawRows X G S p q n₀ degree₀ C f g
      (originalSeedHead G op drift X steps S k θ h H degree wire hist bins raw).Ready G board op t f g drift h w K

/-- The same first register works for every assignment to the original normalized
profile. Only the sufficient payload threshold varies with the two terminal tunings. -/
theorem normalized_seed_entry (branch : G.b≤2^(capRate G t g)) :
    ∃K:ℕ,∃threshold:ℕ→ℕ,∀τ β,max 1 (2*localSocketRate G t g)≤τ→threshold τ≤β→∀ᶠ h:ℕ in atTop,
      NormalizedEntry G board op t f g rate drift n₀ degree₀ C K τ β h :=by
  obtain ⟨A,floors⟩:=normalized_seed_floor_rate G op t f g rate drift n₀ degree₀ C branch
  obtain ⟨threshold,words⟩:=selected_word_guards G op t f g rate drift (quota t)
  let K:=A+1
  refine ⟨K,fun τ=>max (seedCutoff G t f g rate τ) (threshold τ),?_⟩
  intro τ β good budget
  have chosen : SeedCut G t f g rate τ β:=by
    have cost : seedCutoff G t f g rate τ≤β:=le_trans (le_max_left ..) budget
    unfold seedCutoff at cost
    constructor <;> omega
  have pos : 0<β:=by have :=chosen.large;omega
  filter_upwards [floors τ β chosen,words τ β (by omega) (le_trans (le_max_right ..) budget),age_room β pos]
    with h head guards epochs
  intro M low high dyadic S k θ W q p cp pins cut frozen X ordinary reset positive room shorten w fit H degree wire hist hosts padded machine
  let steps:=(normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout
  let bins:=terminalBinCount X G S p q W n₀ degree₀ C f g+1
  let raw:=terminalRawRows X G S p q n₀ degree₀ C f g
  let v:=originalSeedHead G op drift X steps S k θ h H degree wire hist bins raw
  have roof:=head M low high X ordinary reset positive room shorten w fit H degree wire hist hosts padded
  have raised : v.floor G op t f g drift h≤2^(K*h):=roof.trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_succ _)))
  have native : h≤w:=(Nat.le_mul_of_pos_left _ (Nat.succ_pos A)).trans machine.le
  obtain ⟨packed,live,printed,signed,«fields»,gap⟩:=guards M degree w (v.base G h) (S.censusBits p) wire hist native
  exact ⟨raised,raised.trans_lt (Nat.pow_lt_pow_right (by decide) machine),native,packed,live,printed,signed,«fields»,gap,
    original_head_geometry G board op t f g rate drift (J_ h β) M θ h H degree wire hist bins raw X steps
      w K epochs.1 branch dyadic hosts padded raised machine⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
