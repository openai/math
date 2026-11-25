import OAI.Hierarchy.DescentPhysicalResetActorOutput
import OAI.Hierarchy.DescentExteriorSnapshotFields
import OAI.Hierarchy.DescentResetHubRectangle

namespace OAI
/-! # Persistent historical rank directories for the exterior replay -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentExteriorReplay DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k wire hist w : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {I W : MarkedWorld F d P bits}
  {z₀ D₀ age grain degree : ℕ} {initial : Reached I G q ε S k 0 z₀ D₀ wire hist}
  {current : Reached W G q ε S k age grain degree wire hist}

omit [Fintype P] in
theorem Path.snapshotRanks_frame (p : Path initial current) (A : Snapshots k) {lo hi : ℕ}
    {m out : Memory w} (old : p.snapshotRanks A lo m) (inc : lo≤hi) (same : ∀i<lo,out i=m i) :
    p.snapshotRanks A hi out := by
  induction p with
  | here=>trivial
  | ordinary _ _ ih=>exact ⟨ih old.1,old.2⟩
  | reset _ _ ih=>
    obtain ⟨past,B,present,fit,read⟩:=old
    exact ⟨ih past,B,present,⟨fit.1,fit.2.1,fit.2.2.trans inc⟩,
      fun v=>(Snapshots.bank_frame B out m _ lo fit.2.2 same).trans (read v)⟩

omit [Fintype P] in
/-- The ordinary private charge register may change while every earlier
rank interval remains disjoint from all writes. Only those intervals are read. -/
theorem Path.snapshotRanks_banks (p : Path initial current) (A : Snapshots k) {lo hi : ℕ}
    {m out : Memory w} (old : p.snapshotRanks A lo m) (inc : lo≤hi)
    (keep : ∀t<age,∀B,A.compact t=some B→∀i,B.base≤ i→i<B.base+B.size→ out i=m i) :
    p.snapshotRanks A hi out := by
  induction p with
  | here=>trivial
  | @ordinary _ j _ _ _ _ src prev _ _ _ _ _ _ voucher ih=>
    exact ⟨ih old.1 (fun t ht=>keep t (Nat.lt_succ_of_lt ht)),old.2⟩
  | @reset _ j _ _ _ _ _ _ _ _ _ src prev ctl batch ih=>
    obtain ⟨past,B,slot,fit,read⟩:=old
    refine ⟨ih past (fun t ht=>keep t (Nat.lt_succ_of_lt ht)),B,slot,
      ⟨fit.1,fit.2.1,fit.2.2.trans inc⟩,?_⟩
    intro v
    refine Eq.trans ?_ (read v)
    apply keep j (Nat.lt_succ_self _) B slot
    · exact Nat.le_add_right ..
    · exact Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos B.bits)) _

variable {n h C f g cut tail H : ℕ} {ctl : ResetRates G S k degree n h C f g cut tail}
  (B : ClosedReset current ctl) (p : Path initial current) (A : Snapshots k)
  {a : PhysicalReset} {floor : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
set_option quotPrecheck false
local notation "oldName" => B.frame.host.symm.toEmbedding.trans current.vertex
local notation "P₀" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "root" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A₀" => (v).actor
local notation "actorFloor" => (v).middle.stop b
local notation "actors" => (A₀).directory actorFloor
local notation "scene" => (A₀).scene actorFloor
local notation "stencil" => a.throughStencil u.shape floor u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "scanTime" => a.throughStencilTicks u.shape floor u.count u.hub u.g u.Y u.sourceRows u.oldDegree w
local notation "publication" => (((root).preparedRoots u.book u.bookFits).seq ((A₀).classifier u.actor actorFloor w)).seq ((actors).program w scene)
local notation "ticks" => ((root).preparedTicks u.book u.bookFits+(A₀).classifierTime u.actor actorFloor w)+(actors).ticks scene

omit [Fintype P] in
/-- Closes the reset step of the actual Path.snapshotRanks invariant using the
actor census at the instant it wrote its rank values on genuine raw hosts. -/
theorem Path.reset_date_ranks (ready : u.Ready) (room : z.Room) (wide : Fintype.card current.V≤H)
    {m measured census out : Memory w} (run : (PhysicalReset.date z).Runs m out)
    (scanned : (stencil).Exec m measured scanTime) (published : (publication).Exec measured census ticks)
    (slot : A.compact age=some (actors).ranks)
    (capacity : ∀x,(B.reset.rawHostRank B.terminals ((oldName).trans (Fin.castLEEmb wide)) x).val<(actors).sites)
    (ranks : ∀x,census ((actors).ranks.base+(B.reset.rawHostRank B.terminals ((oldName).trans (Fin.castLEEmb wide)) x).val)=
      ((B.reset.denseHostRank B.terminals ((oldName).trans (Fin.castLEEmb wide)) x).val:Word w))
    (past : p.snapshotRanks A floor m) : (p.reset B).snapshotRanks A (a.endAddress floor) out := by
  have outer : floor≤a.endAddress floor :=by obtain ⟨one,two,three⟩:=a.occupied floor;exact one.trans (two.trans three)
  have allPast:=p.snapshotRanks_frame A past outer (fun i hi=>PhysicalReset.date_output_below z ready room run i (Or.inl hi))
  have bank:=u.actor_rank_space ready
  have actorEnd : (v).actorEnd b≤a.endAddress floor :=by
    obtain ⟨_,_,t₃,t₄,t₅,t₆,t₇,t₈,t₉⟩:=ready.ordered
    have finalToAll := PhysicalReset.date_operand_end a floor
    omega
  refine ⟨allPast,(actors).ranks,slot,⟨bank.1,bank.2.1,bank.2.2.trans actorEnd⟩,?_⟩
  intro x
  let j : Fin (actors).sites := ⟨_,capacity x⟩
  have h₁:=(PhysicalReset.actor_rank_read z ready room run scanned published j).2
  have h₂:=h₁.trans (ranks x)
  simpa only [j,B.reset.rawHostRank_extend B.terminals oldName wide,B.reset.denseHostRank_extend B.terminals oldName wide] using h₂

end
end Hierarchy.DescentSixParty.Chronology

end OAI
