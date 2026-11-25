import OAI.Hierarchy.DescentNamedEpochs
import OAI.Hierarchy.DescentOrdinaryPublicDegree
import OAI.Hierarchy.DescentOrdinaryPhysicalProgram

namespace OAI
/-! # One public ordinary procedure and clock across every original branch choice -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated
open DescentCompiler DescentSixParty DescentSixParty.Chronology ProtocolRAM

def forAge (S : AtomSchedule) (base gain k age ℓ b payload unit profile seats : ℕ) : Ordinary :=
  let calendar:=capCalendar base S.rounds gain S.height
  ⟨2^ℓ,S.groupCount age,k,b,OrdinaryLink.publicDegree S.rounds base ((calendar.drop age).head?.getD 0),
    (calendar.take age).prod*256,payload,unit,profile,seats⟩

def measuresAt (S : AtomSchedule) (base p age : ℕ) : Measures :=
  ⟨S.epochPower^S.priceExponent,S.grainAt base p age,S.firstWidth base p⟩

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

namespace Hierarchy.DescentSixParty.SeedNamed.Origin
open DescentInitialHost DescentCompiler DescentColonies Catalyst
open private carried_cap physicalCapacity from OAI.Hierarchy.DescentNamedSeedChronology
noncomputable section
variable {F : Type} [Field F] {cp pins : ℕ} {X : Approximation F cp pins}
    {G : PoweredGadget F} {S : AtomSchedule} {q fee : ℝ} {k z wire s : ℕ}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k}
    (o : Origin (S:=S) (G:=G) (q:=q) (fee:=fee) (z:=z) (wire:=wire) X c digits)
include o in
private def transported : Reached (initial_world X S.copies s (S.groupCount 0) k digits c) G q fee S k 0 z 3 wire s :=
  transport (W' := initial_world X S.copies s (S.groupCount 0) k digits c)
    o.raw (linked_world X c digits o.seed)
private theorem source_fun :
    @Origin.source F _ cp pins X G S q fee k z wire s c digits =
    @transported F _ cp pins X G S q fee k z wire s c digits := rfl

/-- Identify the two capacity projections before evaluating the concrete seed. -/
private theorem cap_fun :
    @physicalCapacity F _ G S q fee k wire s _ 0 _ ((initial X S.copies s (S.groupCount 0) k digits).state c) 0 z 3 =
    @physicalCapacity F _ G S q fee k wire s _ 0 _ (initial_world X S.copies s (S.groupCount 0) k digits c) 0 z 3 := rfl

private theorem cap_transport {P : Type} {d : ℕ} {bits : P → ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q fee S k 0 z 3 wire s) (eqn : world r = W') (h : physicalCapacity r = 256) :
    physicalCapacity (transport r eqn) = 256 := (carried_cap r eqn).trans h

/-- The original seed link supplies the initial capacity. -/
private theorem transported_cap : physicalCapacity (transported o) = 256 := by
  unfold transported
  have raw := o.seed.capacity
  apply cap_transport o.raw
  exact raw

private theorem project {P : Type} {dim : ℕ} {bits : P → ℕ} {W : MarkedWorld F dim P bits}
  (r : Reached W G q fee S k 0 z 3 wire s) : r.placement.cap = physicalCapacity r := rfl

private theorem source_cap : o.source.placement.cap = 256 := by
  have sources := congrFun (source_fun (X:=X) (G:=G) (S:=S) (q:=q) (fee:=fee) (k:=k) (z:=z)
    (wire:=wire) (s:=s) (c:=c) (digits:=digits)) o
  have fn := cap_fun (X:=X) (G:=G) (S:=S) (q:=q) (fee:=fee) (k:=k) (z:=z) (wire:=wire) (s:=s) (c:=c) (digits:=digits)
  let publicCapacity := @physicalCapacity F _ G S q fee k wire s _ 0 _ ((initial X S.copies s (S.groupCount 0) k digits).state c) 0 z 3
  have sourceCapacity := congrArg publicCapacity sources
  have sameCapacity := congrFun fn (transported o)
  exact (project o.source).trans (sourceCapacity.trans (sameCapacity.trans (transported_cap o)))
end
end Hierarchy.DescentSixParty.SeedNamed.Origin

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
      (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=GroupStage.depthBound (atRound S.rounds) n f g)
      (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice}
    (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height

include ticket before tail cut in
theorem ordinary_geometry (ℓ b payload unit profile seats : ℕ) :
    (⟨2^ℓ,S.groupCount i,k,b,(A).degree,(A).cap,payload,unit,profile,seats⟩ : Ordinary)=
      forAge S G.b g k i ℓ b payload unit profile seats := by
  have schedule : ((Path.ordinary before ticket).append tail).capFactors=calendar :=
    (congrArg Path.capFactors cut).trans br.calendar
  have degree:=ticket.public_degree_at before tail calendar schedule
  have factors : before.capFactors++[ticket.factor]++tail.capFactors=calendar := by
    rw [Path.capFactors_append] at schedule
    exact schedule
  let rest:=((Path.ordinary (Path.here (start:=prior)) ticket).append tail)
  have dated : (before.append rest).capFactors=calendar := by
    rw [Path.capFactors_append]
    unfold rest
    rw [Path.capFactors_append, ←List.append_assoc]
    exact factors
  have seedCap := Origin.source_cap br.origin
  have cap := before.capacity_prefix rest calendar dated
  rw [seedCap] at cap
  simp only [Nat.sub_zero] at cap degree
  unfold forAge
  rw [←degree,cap]

include ticket before tail cut in
theorem ordinary_code (ℓ b payload unit profile seats w floor : ℕ) (input : Operands)
    (hk : 0 < k) :
    let actual : Ordinary:=⟨2^ℓ,S.groupCount i,k,b,(A).degree,(A).cap,payload,unit,profile,seats⟩
    let public_:=forAge S G.b g k i ℓ b payload unit profile seats
    let measures : Measures:=⟨(A).wire,(A).z,(A).hist⟩
    actual.program G (A).fieldBits input measures w floor=public_.program G hk input (measuresAt S G.b p i) w floor ∧
    actual.ticks G (A).fieldBits input measures w floor=public_.ticks G hk input (measuresAt S G.b p i) w floor := by
  dsimp only
  have grain:=ticket.grain_on_cut before tail cut br.issuedGrains
  have data : (⟨(A).wire,(A).z,(A).hist⟩ : Measures)=measuresAt S G.b p i := by
    unfold measuresAt
    rw [prior.edges,prior.atoms,←ticket.quantum,grain]
  exact Ordinary.same_program _ G (A).fieldBits input _ w floor hk _
    (ordinary_geometry X G S br ticket before tail cut ℓ b payload unit profile seats) data

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
