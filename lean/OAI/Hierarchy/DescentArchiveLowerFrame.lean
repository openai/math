import OAI.Hierarchy.DescentArchivePadInputs
import OAI.Hierarchy.DescentPreviousOperandLimit

namespace OAI
/-! # All previous register values survive the lower-address frame of the next date -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
open DescentDatedAddressBook DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentPrimitivePalette DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist w : ℕ}
    (ports : DatePorts) (r : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)
local notation "argLayout" => ports.rangeLayout
local notation "Cells" => Fin ports.operandHosts→Fin ports.venue.groups→Cell (ports.operandBits*ports.nodes)

variable {p R s Z : ℕ} (shape : WorldShape p R B) (op : RotorSpec)
    (label : NodeOrder.All B→Label G s Z op) (pointer : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)

private theorem hold {a H J M w floor : ℕ} {x : Fin H→Fin J→Cell a} {b : Bank} {m dst : Memory w}
    (frame : ∀n,n<floor → dst n=m n) (fits : b.Fits w floor)
    (rows : H*chunks J M≤b.size) (h : Reads b x M m) : Reads b x M dst:=by
  intro q
  rw [frame _ (lt_of_lt_of_le (Nat.add_lt_add_left ((row H J M q).isLt.trans_le rows) _) fits.2.2)]
  exact h q

private theorem rows_le (r : ℕ) : r≤2^Nat.clog 2 (r+1):=
  (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)

/-- Transports the actual field, arity and token bit patterns through one native lower frame. -/
theorem ArchiveRead.below {m dst : Memory w} (a : ArchiveRead ports r B number room shape op label pointer flags m)
    (floor : ℕ) (fits : ports.ArchiveFits ports.venue.k floor) (space : floor<2^w)
    (sizes : ports.RoleRows) (frame : ∀n,n<floor → dst n=m n) :
    ArchiveRead ports r B number room shape op label pointer flags dst:=by
  let blank : DescentResetRetainedSetup.Layout:=⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩
  let raw:=ports.storage ports.venue.k blank
  have hi:=fits.data blank
  have banks (j : Fin raw.sources) : (ports.archive.prior raw j).Fits w floor:=
    raw.prior_registers ports.archive.seed ports.archive.nodeBase ports.archive.arguments floor w hi.1 hi.2 space j
  have arg {f : Fin 7} {j : Fin ports.argumentsPerNode} {x : Fin (2^ports.venue.k)}
      {cells : Cells} (h : Reads (previousBank argLayout ports.archive.arguments x (DescentOperandStateBanks.page f j)) cells ports.operandLanes m) :
      Reads (previousBank argLayout ports.archive.arguments x (DescentOperandStateBanks.page f j)) cells ports.operandLanes dst:=by
    have limit : (argLayout).previousLimit ports.archive.arguments≤floor:=hi.2
    exact hold frame ((argLayout).previous_fit ports.archive.arguments floor w limit space x _) (rows_le _) h
  have md (f : Fin 2) (x : Fin (2^ports.venue.k)) {cells : Cells}
      (h : Reads (metadataPage ports f x) cells ports.operandLanes m) :
      Reads (metadataPage ports f x) cells ports.operandLanes dst:=by
    let metaBank (f : Fin 2) (x : Fin raw.blocks) := metadataPage ports f x
    let argBank (j : Pages raw.previousArgs) (x : Fin raw.blocks) :=
      previousBank ports.rangeLayout ports.archive.arguments x j
    have directory (j : Fin raw.sources) :
        ports.archive.prior raw j = raw.directory metaBank argBank j := by
      cases seed : ports.archive.seed <;>
        simp only [PriorResetArchive.prior, metaBank, metadataPage, seed, Bool.false_eq_true, ite_false, ite_true] <;>
        rfl
    have eqn : ports.archive.prior raw (raw.sourceID (if f=0 then raw.occupiedField else raw.arityField) x)=
        metadataPage ports f x:=by
      rw [directory]
      fin_cases f
      · exact (raw.directory_role metaBank argBank x).1
      · exact (raw.directory_role metaBank argBank x).2
    have fit:=banks (raw.sourceID (if f=0 then raw.occupiedField else raw.arityField) x)
    rw [eqn] at fit
    apply hold frame fit _ h
    unfold metadataPage
    split <;> exact rows_le _
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x j f
    obtain ⟨cells,read,values⟩:=a.headers x j f
    exact ⟨cells,arg read,values⟩
  · intro x j f
    obtain ⟨cells,read,values⟩:=a.spans x j f
    exact ⟨cells,arg read,values⟩
  · intro x
    apply md 0 x
    exact a.nodeFlags x
  · intro x
    apply md 1 x
    exact a.arity x
  · intro x
    exact hold frame (ports.archive.roles.fits w floor x.val (x.isLt.trans_le fits.blocks) fits.roles space) sizes
      (a.primitive x)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
