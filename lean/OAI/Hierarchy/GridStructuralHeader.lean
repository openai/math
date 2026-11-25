import OAI.ThreeFlat.RAM.HistoryPhysicalLibrary
import OAI.Hierarchy.GridReceiverHeader
import OAI.Hierarchy.TraceSeedDirectories
import OAI.Hierarchy.TraceReceiverAge
import OAI.ThreeFlat.Diagonal.TickWorkspace
import OAI.Hierarchy.TraceReceiverTemplate

namespace OAI
/-! # The public parameter words shared by the controller and grid receivers -/

namespace Hierarchy.GridStructuralHeader
open ThreeFlat RAM Diagonal Diagonal.PhysicalStage NavigationPass NavigationDirectory
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
open scoped Fin.CommRing
set_option quotPrecheck false


variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base d fuel : ℕ}
variable (B : Block F) (axes n cap : ℕ)
local notation "P" => (B.repeat n)
local notation "rem" => (axes-(P).charge)
local notation "ss" => ((P).directory rem axes)
local notation "edges" => ((P).finalEdges rem axes)

/-- The native compressor needs only its public stage lengths and final radix;
the raw location, input bits and current relay widths have no effect here. -/
def directory : List ℕ :=
  (TraceSeedWriter.archive B w axes 0 0 cap 0).directory ss edges (64*w)

omit [Fintype F] in
theorem directory_length :
    (directory (w:=w) B axes n cap).length=64*((B.levels+1)*n+2) := by
  unfold directory
  rw [Archive.directory_length,Program.directory_length]
  rw [TraceSeedWriter.repeat_length]

variable (M : Machine (64*w) pc regs slots) (fit : NativeTrace.Fits M S base d fuel)
variable (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (raw gateBase : ℕ)
local notation "G" => TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs slots d
local notation "dir" => (directory (w:=w) B axes n cap)
local notation "packet" => TraceReceiverTemplate.words M fit hF st (FieldCode.ofCardLe hF) raw gateBase

/-- The original and relocated directories have the same number of public
entries. The two copies carry the actual absolute addresses in the two
different executions. -/
def wordCount (directoryLength templateLength libraryLength : ℕ) :=
  directoryLength+(templateLength+(directoryLength+libraryLength))

/-- Fixed coefficient for the native finite-field library, the verifier table
and both chronological directories. The library word count grows quartically
in the fixed-word width and is absorbed in the degree-fourteen bound. -/
def libraryCoefficient := 384000*65^4+HistoryStageBody.Physical.staticSize B+130+HistoryStageBody.Physical.gridSize B

def coefficient := 128*(B.levels+3)+TraceReceiverTemplate.coefficient+libraryCoefficient B

theorem library_count :
    HistoryStageBody.Physical.libraryWords B (64*w)≤libraryCoefficient B*(w+1)^14 := by
  rw [HistoryStageBody.Physical.libraryWords_eq]
  have base : 64*w+1≤65*(w+1) := by omega
  have fourth := Nat.pow_le_pow_left base 4
  rw [mul_pow] at fourth
  have lin : w+1≤(w+1)^14 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos w) (show 1≤14 by decide)
  have high := Nat.pow_le_pow_right (Nat.succ_pos w) (show 4≤14 by decide)
  have one : 1≤(w+1)^14 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have sta := Nat.mul_le_mul_left (HistoryStageBody.Physical.staticSize B) one
  have grd := Nat.mul_le_mul_left (HistoryStageBody.Physical.gridSize B) one
  have f := fourth.trans (Nat.mul_le_mul_left (65^4) high)
  have linear := Nat.mul_le_mul_left 2 (base.trans (Nat.mul_le_mul_left 65 lin))
  rw [← Nat.mul_assoc] at linear
  change 2*(64*w+1) ≤ 130*(w+1)^14 at linear
  simp only [Nat.mul_one] at sta grd
  rw [libraryCoefficient, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.mul_assoc 384000]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.mul_le_mul_left 384000 f) sta) linear) grd


local notation "lib" => (HistoryStageBody.Physical.libraryWords B (64*w))
local notation "total" => (wordCount (dir).length (TraceReceiverTemplate.count G) lib)

def receiverPhase (w text count : ℕ) :=
  2+text+(count+1)*(64*w)+GridReceiverHeader.count w*(64*w)

def recipientBase (w : ℕ) := TickWorkspace.base (TraceAdmission.receiverAge w) 20

local notation "phase" => (receiverPhase w (SelfAdvice.textSize (64*w) pc slots) total)
local notation "compactDir" => (TraceCompactSeed.directory B w (recipientBase w) axes n cap phase)

theorem recipient_length : (compactDir).length=(dir).length := by
  rw [TraceCompactSeed.directory_length,directory_length]

/-- In order, the public words encode the controller's physical directory, the
verifier's gate and port template, the recipient's relocated directory, and
the lookup tables used for positive history records. -/
def parameters (i : Fin total) : Word (64*w) :=
  Fin.addCases (motive:=fun _ => Word (64*w))
    (fun j : Fin (dir).length => ((dir)[j.val] : Word (64*w)))
    (fun j => Fin.addCases (motive:=fun _ => Word (64*w)) packet
      (fun h => Fin.addCases (motive:=fun _ => Word (64*w))
        (fun u : Fin (dir).length => ((compactDir)[u.val]'(by
          rw [recipient_length B axes n cap M fit hF st]; exact u.isLt) : Word (64*w)))
        (HistoryStageBody.Physical.data B (64*w) (64*w)) h) j) i

/-- The word vector is already fixed by the padded architecture. Installing
the actual evaluator instructions at that architecture changes only the
self-description, including its genuine instruction bytes. -/
theorem parameters_congr (M' : Machine (64*w) pc regs slots)
    (fit' : NativeTrace.Fits M' S base d fuel) :
    parameters B axes n cap M fit hF st raw gateBase =
      parameters B axes n cap M' fit' hF st raw gateBase := rfl

theorem parameter_count (hn : n≤w) (field : Fintype.card F≤64*w) (hp : pc≤64*w)
    (hr : regs≤64*w) (hs : slots≤64*w) (hd : d≤64*w) :
    total≤
      coefficient B*(w+1)^14 := by
  have count := TraceReceiverTemplate.count_bound M fit hF st field hp hr hs hd
  unfold wordCount
  rw [directory_length]
  have lin : (w+1)≤(w+1)^14 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos w) (show 1≤14 by decide)
  have h : 64*((B.levels+1)*n+2)≤(64*(B.levels+3))*(w+1) := by
    have := Nat.mul_le_mul_left (B.levels+1) hn
    nlinarith
  have each:=h.trans (Nat.mul_le_mul_left _ lin)
  have libs:=library_count (w:=w) B
  apply (Nat.add_le_add each (Nat.add_le_add count (Nat.add_le_add each libs))).trans_eq
  unfold coefficient
  ring

@[simp] theorem first (j : Fin (dir).length) :
    parameters B axes n cap M fit hF st raw gateBase (j.castAdd _)=((dir)[j.val]:Word (64*w)) := by
  simp [parameters]

@[simp] theorem second (j : Fin (TraceReceiverTemplate.count G)) :
    parameters B axes n cap M fit hF st raw gateBase (Fin.natAdd (dir).length (j.castAdd ((dir).length+lib)))=packet j := by
  simp [parameters]

@[simp] theorem third (j : Fin (dir).length) :
    parameters B axes n cap M fit hF st raw gateBase
      (Fin.natAdd (dir).length (Fin.natAdd (TraceReceiverTemplate.count G) (j.castAdd lib))) =
        ((compactDir)[j.val]'(by rw [recipient_length B axes n cap M fit hF st];exact j.isLt):Word (64*w)) := by
  simp [parameters]

@[simp] theorem fourth (j : Fin lib) :
    parameters B axes n cap M fit hF st raw gateBase
      (Fin.natAdd (dir).length (Fin.natAdd (TraceReceiverTemplate.count G) (Fin.natAdd (dir).length j))) =
      HistoryStageBody.Physical.data B (64*w) (64*w) j := by
  simp [parameters]

/-- The body excludes precisely the selector tag at its first physical address. -/
def selectorBit (s : Fin (cap+1)→Bool) (i : ℕ) : Bool :=
  if h : i<cap then s (Fin.succ ⟨i,h⟩) else false

theorem selector_body (s : Fin (cap+1)→Bool) :
    List.ofFn (fun i : Fin cap=>selectorBit cap s i.val)=List.ofFn (fun i : Fin cap=>s i.succ) := by
  congr 1;funext i;simp [selectorBit]

end
end Hierarchy.GridStructuralHeader

end OAI
