import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenBoot
import OAI.Computability.BorderVNP.DiagonalCandidateOpenedMemory

/-! # Sparse-call frame words from the signed startup packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA Evaluator Packing RoutingOutputs GeometryAdvice DiagonalResidueRAM
open TeamContraction ProcessorSlots

variable {w d : ℕ}

/-- The word width and the native call-limit and task pointer are already
present on the genuine returned profile RAM, before private placement. -/
theorem BootResidence.task_header_words (t : SignedTaskArena.Layout) (a : StartupArena) (team : Fin a.teams)
    (slot : ℕ) (p : ReferencePacket w d) (D : Directory.Layout) (other : Arg → Word w) (old : Fin 81 → Word w)
    (origin raw subtotal fresh profile gates outputs width off ell : ℕ)
    (selected : p.extension = signedProfileExtension t old D origin t.cube.cables t.cube.cells raw team.val
      subtotal fresh profile gates outputs width off ell) {f : BroadcastFrame} {A : AdviceLayout}
    {mac : TeamOpcode.Macros w 8} {bits : List Bool} {bank : Bank w} {initial after : Memory w}
    {k : ℕ} {g : Fin k → Bool} :
    let B := a.operands team slot p
    let args := core (withDemandBase (t.routeBank a.frame other) a.next) origin t.cube.cables t.cube.cells
    let pub := B.bank args
    B.Fits w → ∀ {F : Pins.ProcessorFields B.layout},
      BootResidence (F:=F) a team slot p f A pub mac bits initial bank g after →
      t.before.limit<2^w → (t.tasks 0 0 0 0).tasks<2^w →
    readings after (a.frame+30)=w ∧ readings after (a.frame+14)=t.before.limit ∧
      readings after (a.frame+89)=(t.tasks 0 0 0 0).tasks := by
  intro B args pub fit F attained limit taskFit
  obtain ⟨_,_,_,_,boot,resident⟩ := attained
  have base : (pub 0).val=a.frame := B.frameBase_word args fit
  obtain ⟨ordinary,extended⟩ := resident_frames a team slot p (Pins.extendGuess g) base boot resident
  have word := congrArg Fin.val ((ordinary 30).trans (boot.core 30).symm)
  have oldWidth := boot.frame.extension.2.2
  change readings after ((pub 0).val+30)=_ at word
  have savedWidth := word.trans oldWidth
  have calls := congrArg Fin.val (ordinary 14)
  change readings after ((pub 0).val+14)=t.before.limit % 2^w at calls
  have tasks := congrArg Fin.val (extended 58)
  rw [selected] at tasks
  change readings after ((pub 0).val+89)=(t.tasks 0 0 0 0).tasks % 2^w at tasks
  rw [base] at savedWidth calls tasks
  exact ⟨savedWidth,calls.trans (Nat.mod_eq_of_lt limit),tasks.trans (Nat.mod_eq_of_lt taskFit)⟩

end PackedHistoryCircuit

namespace RoutingISA.Evaluator.SignedPrep

open Crossing _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.GroupWeights Cube.LabelIndex Cube.Tally
open CubeHeaderInstall CubeArena TeamContraction TeamContraction.JointHeader LocalRow Transmission
open VPVNP.BurstRAM
open Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical Packing.RoutingOutputs
open VPVNP.VerifierNetwork Packing.Inherited Packing.BottomReports DiagonalTallyCellReports
open DiagonalTallyAllocation ReportDirectory DiagonalResidueRAM FiniteEvaluator GeometryFrameEncoding
open scoped Classical

variable {D w R X : ℕ} {P A : Type} [Fintype P] [Fintype A] {bits : P → ℕ}
    (N : Network D P bits) (t : SignedTaskArena.Layout) (cell : N.Site → Fin t.cube.cells)
    (recv : A → Fin t.cube.cells) (size : A → ℕ) {D₀ : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w}
    {initialBase receivingBase : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {I : Type*} [Fintype I] {resides : I → Fin t.cube.cells} {keyID : I ↪ ℕ} {sizes : I → ℕ}
    {representative : ℕ → Fin (R+1)} {group : Fin t.cube.header.d → Fin (R+1)}
    (raw : Broadcast t.cube.n t.cube.header.d t.cube.header.cap)
local notation3 (prettyPrint := false) "dec" => Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
  (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j))
variable (site : CandidateSite (X:=X) t.cube D₀ pp lp raw representative
      (Prod.mk (Fin.ofNat (t.cube.n+1) (readCode (t.cube.n+1) raw.1))
        (fun (p : Sym2 (Fin t.cube.header.d)) (j : Fin (t.cube.n+1)) => readCode (t.cube.header.cap+1) (raw.2 p j)))
      group initialBase receivingBase pins fields f guess pub mac reg mem resides keyID sizes N cell recv size)
    {origin : ℕ}
local notation3 (prettyPrint := false) "frame" => (pub 0).val
local notation "table" => bases origin t.cube.cables t.cube.cells D₀.entries
local notation "ctl" => controlsBase origin t.cube.cables t.cube.cells D₀.entries (D₀.teams*D₀.sites)
omit [Fintype P] [Fintype A] in
/-- The native directory stages preserve every startup word below the
seven-word array except the published row count at offset nine. -/
theorem CandidateSite.dataInput_frame_word {gap : ℕ}
    (place : (privateLayout frame origin t.cube.cables t.cube.cells D₀.entries D₀.description gap).Image
      (readings site.geometry) D₀.entries (readings site.middle))
    (lo : frame+112≤receivingBase) (span : receivingBase≤origin)
    (j : ℕ) (small : j<112) (other : j≠9) :
    readings site.receipt.history.dataInput (frame+j)=readings site.geometry (frame+j) := by
  have addr : frame+j<t.cube.header.header := by have full := site.input.frameSpace; omega
  have prior := site.receipt.done.low (frame+j) addr
  exact congrArg Fin.val (prior.trans ((congrFun site.actual _).trans
    (PackedHistoryCircuit.directoryPublished_low (D₀.directory pp lp) place span _ (by omega) (by omega))))

omit [Fintype P] [Fintype A] in
/-- The actual pointer words in a returned startup frame still select the
same control program on the native data writer. -/
theorem CandidateSite.dataInput_open_fields {gap team offsets control live ports bundles : ℕ}
    (place : (privateLayout frame origin t.cube.cables t.cube.cells D₀.entries D₀.description gap).Image
      (readings site.geometry) D₀.entries (readings site.middle))
    (lo : frame+112≤receivingBase) (span : receivingBase≤origin)
    (fields : t.OpenFields team frame offsets control live ports bundles (readings site.geometry)) :
    t.OpenFields team frame offsets control live ports bundles (readings site.receipt.history.dataInput) := by
  apply fields.transfer t
  intro j listed
  simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
  exact site.dataInput_frame_word N t cell recv size raw place lo span j (by omega) (by omega)

omit [Fintype P] [Fintype A] in
/-- Each scalar operand of the fragment builder is unchanged by the actual
private placement, seven-word publication and returned directory prefix. -/
theorem CandidateSite.task_header_inputs {gap : ℕ}
    (place : (privateLayout frame origin t.cube.cables t.cube.cells D₀.entries D₀.description gap).Image
      (readings site.geometry) D₀.entries (readings site.middle))
    (lo : frame+112≤receivingBase) (span : receivingBase≤origin)
    (passed : readings site.geometry (frame+30)=w ∧ readings site.geometry (frame+14)=t.before.limit ∧
      readings site.geometry (frame+89)=(t.tasks 0 0 0 0).tasks) :
    readings site.receipt.history.dataInput (frame+30)=w ∧
    readings site.receipt.history.dataInput (frame+14)=t.before.limit ∧
    readings site.receipt.history.dataInput (frame+89)=(t.tasks 0 0 0 0).tasks := by
  have low := site.dataInput_frame_word N t cell recv size raw place lo span
  exact ⟨(low 30 (by decide) (by decide)).trans passed.1,(low 14 (by decide) (by decide)).trans passed.2.1,
    (low 89 (by decide) (by decide)).trans passed.2.2⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
