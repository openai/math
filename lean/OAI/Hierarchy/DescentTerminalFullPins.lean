import OAI.Hierarchy.DescentTerminalCandidateHistory
import OAI.Hierarchy.DescentTerminalCandidateType
import OAI.Hierarchy.DescentTerminalPublicIdentity
import OAI.Hierarchy.DescentExteriorPackedHostPins

namespace OAI
/-! # Candidate pins for the original profile tape, all exterior proposals and the terminal chip -/
namespace Hierarchy.DescentTerminalFullPins
open DescentInitialHost DescentPackedProfileInstall DescentGL Computability.BorderVNP.Crossing
open ThreeFlat Routing Diagonal CorrectionBatch
open DescentTerminalChipPins DescentTerminalPorts DescentExteriorShelf DescentExterior
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentPackedProfileTape DescentPackedEpochFold
open DescentTerminalEpochHeader DescentPackedEpochShelves DescentSeedRoot DescentCompiler Catalyst CatalystSubstitution
open ThreeFlat.Diagonal Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F A : Type} [Field F] {cp data j r t K W q piece rows : ℕ}
variable (X : Approximation F cp data)
local notation "E" => ExteriorCount X
local notation "P" => Catalyst.Port ((2^(j+(j+r))*t)*data) (CorrectionFrame.copiesWidth (2^(j+(j+r))*t) X.width)
local notation "Old" => A ⊕ Hidden E j r t
local notation "B" => q*(W*piece)

def chip {old:Type} : DescentTerminalPaidBoot.Input K W q piece rows→Candidate old K W q piece rows :=
  Sum.elim (fun v=>.inl (.inr v)) Sum.inr

variable (R s w : ℕ) (seed : Select X R s→A) (lo C grain : ℕ) (ss : List (Source A))
local notation "lastWord" => end_ (lo+extent grain ss) C grain
local notation "front" => lastWord+17*span j r t E
local notation "All" => Candidate Old K W q piece rows
variable (publicRows codes : ℕ)
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rows publicRows

def header (outer : P→Bool) (z : All→Bool) : Memory w :=
  Root.appended front extra
    (Root.packedImage X R s w seed lo C grain ss lastWord (DescentExterior.publicRows X outer) (z ∘ history))
    (DescentTerminalPublicIdentity.back (z ∘ chip) w codes publicRows)

def pins : Fin (front+extra)×Fin (w+1)→(P⊕All)⊕Bool :=
  Root.appendPin front extra
    (Root.hostPin X R s w seed lo C grain ss history lastWord)
    (fun i=>(DescentTerminalPublicIdentity.pins K W q piece rows publicRows w codes i).map (Sum.inr ∘ chip) id)

theorem pins_read (outer : P→Bool) (z : All→Bool) (extRoom : 2^j*t ≤ w) (modeRoom : B ≤ w)
    (positive : 0<grain) (held : ∀a∈ss,DescentTerminalEpochBits.width a.C*grain ≤ w)
    (i : Fin (front+extra)×Fin (w+1)) :
    (pins X R s w seed lo C grain ss publicRows codes i).elim (Sum.elim outer z) id=
      TraceWords.bits (TraceBanks.wide (header X R s w seed lo C grain ss publicRows codes outer z i.1.val)) i.2 := by
  apply Root.appendPin_read
  · exact Root.hostPin_read X R s w seed lo C grain ss history lastWord outer z le_rfl extRoom positive held
  · intro a
    have exported:=DescentTerminalPublicIdentity.pins_read (z ∘ chip) w codes publicRows modeRoom a
    cases e : DescentTerminalPublicIdentity.pins K W q piece rows publicRows w codes a <;>
      rw [e] at exported <;> exact exported

/-- All terminal input words use the same choice as the separately retained history and public pins. -/
theorem retained_ranges (outer : P→Bool) (z : All→Bool) (m : Memory w)
    (keep : ∀u < extra,m (front+u)=header X R s w seed lo C grain ss publicRows codes outer z (front+u)) :
    (∀u < DescentTerminalPaidBoot.total K W q piece codes rows,m (front+u)=DescentTerminalPaidBoot.back (z ∘ chip) w codes u) ∧
      ∀u < DescentTerminalPrimitiveArena.pad publicRows,
        m (front+DescentTerminalPaidBoot.total K W q piece codes rows+u)=(u:Word w) := by
  apply DescentTerminalPublicIdentity.ranges (z ∘ chip) codes publicRows front m
  intro u hu
  exact (keep u hu).trans (Root.suffix_read front extra _ _ ⟨u,hu⟩)

omit [Field F] in
theorem history_assign (z : All→Bool) :
    Sum.elim (z ∘ history ∘ Sum.inl) (z ∘ history ∘ Sum.inr)=z ∘ history (old:=Old) := by
  funext v
  cases v <;> rfl

end
end Hierarchy.DescentTerminalFullPins

end OAI
