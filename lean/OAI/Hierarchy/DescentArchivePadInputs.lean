import OAI.Hierarchy.DescentDatePortArchiveRead
import OAI.Hierarchy.DescentResetPriorFieldCases
import OAI.Hierarchy.DescentPriorResetArchive

namespace OAI
/-! # Positive reset intake from the preceding stored archive -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem row_capacity (rows : ℕ) : rows≤2^Nat.clog 2 (rows+1) :=
  (Nat.le_succ rows).trans (Nat.le_pow_clog (by decide) _)

def RoleRows (p : DatePorts) := p.operandHosts*chunks p.venue.groups p.roleLanes≤2^p.archive.roles.bits

theorem initial_role_rows {F : Type} [Field F] {c p : ℕ} (G : PoweredGadget F) (op : RotorSpec)
    (X : Catalyst.Approximation F c p) (R : ℕ) (l : DescentDatedSeedStartup.Layout) (k H groups h Z : ℕ) :
    (initial G op X R l k H groups h Z).RoleRows :=by
  exact Nat.le_pow_clog (by decide) _

theorem ordinary_role_rows {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
    (hosts : v.resolver.hosts=v.paletteShape.durable.hosts) (groups : v.venue.groups=v.paletteShape.durable.groups) :
    (ordinary v floor).RoleRows :=by
  change v.resolver.hosts*chunks v.venue.groups v.palette.nextLanes≤2^Nat.clog 2 (v.paletteShape.durable.rows+1)
  rw [hosts,groups]
  exact row_capacity _

theorem reset_role_rows {w : ℕ} (a : PhysicalReset) (floor : ℕ) (u : a.DateInputs floor w)
    (hosts : a.successor.sheets.hosts=a.successor.primitive.chart.hosts)
    (groups : a.successor.venue.next.groups=a.successor.primitive.chart.groups) :
    (reset a floor u).RoleRows :=by
  let v:=a.successor
  change v.sheets.hosts*chunks v.venue.next.groups v.primitive.chart.lanes≤2^Nat.clog 2 (v.primitive.chart.rows+1)
  rw [hosts,groups]
  exact row_capacity _

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    {ports : DatePorts} {r : Reached W G q ε S k age grain degree wire hist} {B : BitDescription W}
    {number : Local B} {room : RangeRoom ports r B} {p R s Z : ℕ} {shape : WorldShape p R B} {op : RotorSpec}
    {label : NodeOrder.All B→Label G s Z op} {pointer : NodeOrder.All B→ℕ→Pointer}
    {flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ}
    {m : Memory w}

theorem ArchiveRead.pad_witness (a : ArchiveRead ports r B number room shape op label pointer flags m)
    (L : DescentResetRetainedSetup.Layout) (tokenWidth : ports.tokenBits=printedBits G s Z op)
    (sized : ports.RoleRows) :
    let raw:=ports.storage ports.venue.k L
    (∃data : raw.Values, (∀j, ports.operandHosts*chunks ports.venue.groups ports.operandLanes≤
        (ports.archive.prior raw j).size ∧ Reads (ports.archive.prior raw j) (data j) ports.operandLanes m) ∧
      (∀x,data (raw.sourceID raw.arityField x) = fun h g=>encode ports.operandBits ports.nodes
        (fun n=>((slotAt ports r B number room x n h g).elim 0
          (fun y=>(occurrences (shape.sites y.1) y.2).length):Cell ports.operandBits))) ∧
      ∀f j x,Reads (previousBank ports.rangeLayout ports.archive.arguments x (page f j))
        (data (raw.sourceID (raw.operandField f j) x)) ports.operandLanes m) ∧
    ∃roles : Fin (2^ports.venue.k)→Fin ports.operandHosts→Fin ports.venue.groups→Cell (ports.tokenBits*ports.nodes),
      (∀x,ports.operandHosts*chunks ports.venue.groups ports.roleLanes≤(ports.archive.roles.bank x.val).size ∧
        Reads (ports.archive.roles.bank x.val) (roles x) ports.roleLanes m) ∧
      ∀x h g,(roles x h g).val=(encode (printedBits G s Z op) ports.nodes (fun n=>
        (slotAt ports r B number room x n h g).elim 0 (fun y=>token G s Z op (label y)))).val:=by
  classical
  intro raw
  constructor
  · let md (f : Fin 2) (x : Fin raw.blocks) := fun h g=>if f=0 then
      encode ports.operandBits ports.nodes (fun n=>(flags x n h g:Cell ports.operandBits))
    else encode ports.operandBits ports.nodes (fun n=>
      ((slotAt ports r B number room x n h g).elim 0 (fun y=>(occurrences (shape.sites y.1) y.2).length):Cell ports.operandBits))
    choose cells read using a.operands
    let pg:=fun j x=>cells x j
    let data:raw.Values:=raw.directory md pg
    have indexed (f : Fin 7) (j : Fin raw.previousArgs) (x : Fin raw.blocks) :
        Reads (previousBank ports.rangeLayout ports.archive.arguments x (page f j))
          (data (raw.sourceID (raw.operandField f j) x)) ports.operandLanes m:=by
      change Reads _ (raw.directory md pg _) _ _
      erw [raw.directory_property md pg f j x]
      exact read x _
    let metaBank (f : Fin 2) (x : Fin raw.blocks) := metadataPage ports f x
    let argBank (j : Pages raw.previousArgs) (x : Fin raw.blocks) :=
      previousBank ports.rangeLayout ports.archive.arguments x j
    have directory (j : Fin raw.sources) :
        ports.archive.prior raw j = raw.directory metaBank argBank j := by
      cases seed : ports.archive.seed <;>
        simp only [PriorResetArchive.prior, metaBank, metadataPage, seed, Bool.false_eq_true, ite_false, ite_true] <;>
        rfl
    refine ⟨data,?_,fun x=>(raw.directory_role md pg x).2,indexed⟩
    apply raw.source_cases
    · intro f x
      have eqn : ports.archive.prior raw (raw.sourceID (if f=0 then raw.occupiedField else raw.arityField) x)=
          metadataPage ports f x:=by
        rw [directory]
        fin_cases f
        · exact (raw.directory_role metaBank argBank x).1
        · exact (raw.directory_role metaBank argBank x).2
      erw [eqn]
      have cap : raw.hosts*chunks raw.groups raw.previousLanes≤(metadataPage ports f x).size:=by
        unfold metadataPage
        split <;> exact row_capacity _
      refine ⟨cap,?_⟩
      fin_cases f
      · change Reads _ (raw.directory md pg (raw.sourceID raw.occupiedField x)) _ _
        erw [(raw.directory_role md pg x).1]
        exact a.nodeFlags x
      · change Reads _ (raw.directory md pg (raw.sourceID raw.arityField x)) _ _
        erw [(raw.directory_role md pg x).2]
        exact a.arity x
    · intro f j x
      have eqn : ports.archive.prior raw (raw.sourceID (raw.operandField f j) x)=
          previousBank ports.rangeLayout ports.archive.arguments x (page f j):=by
        rw [directory]
        exact raw.directory_property metaBank argBank f j x
      erw [eqn]
      exact ⟨row_capacity _,indexed f j x⟩
  · rw [tokenWidth]
    exact ⟨_,fun x=>⟨sized,a.primitive x⟩,fun _ _ _=>rfl⟩

theorem ArchiveRead.pad_input (a : ArchiveRead ports r B number room shape op label pointer flags m)
    (L : DescentResetRetainedSetup.Layout) (tokenWidth : ports.tokenBits=printedBits G s Z op)
    (sized : ports.RoleRows) :
    let raw:=ports.storage ports.venue.k L
    (∃data : raw.Values, ∀j, ports.operandHosts*chunks ports.venue.groups ports.operandLanes≤
        (ports.archive.prior raw j).size ∧ Reads (ports.archive.prior raw j) (data j) ports.operandLanes m) ∧
    ∃roles : Fin (2^ports.venue.k)→Fin ports.operandHosts→Fin ports.venue.groups→Cell (ports.tokenBits*ports.nodes),
      (∀x,ports.operandHosts*chunks ports.venue.groups ports.roleLanes≤(ports.archive.roles.bank x.val).size ∧
        Reads (ports.archive.roles.bank x.val) (roles x) ports.roleLanes m) ∧
      ∀x h g,(roles x h g).val=(encode (printedBits G s Z op) ports.nodes (fun n=>
        (slotAt ports r B number room x n h g).elim 0 (fun y=>token G s Z op (label y)))).val:=by
  intro raw
  obtain ⟨⟨data,stored,_,_⟩,roles⟩:=a.pad_witness L tokenWidth sized
  exact ⟨⟨data,stored⟩,roles⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
