import OAI.Hierarchy.DescentWideExteriorRoot
import OAI.Hierarchy.DescentTerminalFullPins

namespace OAI
/-! # Original catalyst, history and terminal chip pins for a narrow seed in wide RAM words -/
namespace Hierarchy.DescentExteriorShelf.Root
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExterior DescentGL Computability.VPVNP.BurstRAM Computability.BorderVNP.Crossing
open ThreeFlat Routing Diagonal Catalyst CatalystSubstitution CorrectionBatch
open scoped Classical
noncomputable section
variable {F A B : Type} [Field F] {cp data j r t : ℕ}

def wideHostPin (X : Catalyst.Approximation F cp data) (R s payload w : ℕ)
    (seed : DescentSeedRoot.Select X R s → A) (lo C grain : ℕ)
    (ss : List (DescentTerminalEpochChart.Source A))
    (bind : A ⊕ Hidden (ExteriorCount X) j r t → B) (origin : ℕ)
    (i : Fin (origin+17*DescentExteriorShelf.span j r t (ExteriorCount X))×Fin (w+1)) :
    ((Catalyst.Port (2^(j+(j+r))*t*data) (CorrectionFrame.copiesWidth (2^(j+(j+r))*t) X.width))⊕B)⊕Bool :=
  (@pin A w (ExteriorCount X) j r t
      (DescentPackedProfileInstall.end_ (lo + DescentPackedEpochShelves.extent grain ss) C grain)
      origin (@widePackedPin F A _ cp data X R s payload w seed lo C grain ss) i).map
    (Sum.map (fun (p : Public (ExteriorCount X) j r t) =>
      @DescentExterior.publicPin F cp data X j r t p.1.1 p.1.2 p.2) bind) id

theorem wideHostPin_read (X : Catalyst.Approximation F cp data) (R s payload w : ℕ)
    (seed : DescentSeedRoot.Select X R s → A) (lo C grain : ℕ)
    (ss : List (DescentTerminalEpochChart.Source A))
    (bind : A ⊕ Hidden (ExteriorCount X) j r t → B) (origin : ℕ)
    (x : (Catalyst.Port (2^(j+(j+r))*t*data) (CorrectionFrame.copiesWidth (2^(j+(j+r))*t) X.width))→Bool) (z : B→Bool)
    (split : (DescentPackedProfileInstall.end_ (lo + DescentPackedEpochShelves.extent grain ss) C grain) ≤ origin)
    (arch : payload ≤ w) (space : 2^j*t ≤ w) (pos : 0 < grain)
    (room : ∀u∈ss,DescentTerminalEpochBits.width u.C*grain ≤ w)
    (i : Fin (origin+17*DescentExteriorShelf.span j r t (ExteriorCount X))×Fin (w+1)) :
    (wideHostPin (j:=j) (r:=r) (t:=t) X R s payload w seed lo C grain ss bind origin i).elim (Sum.elim x z) id =
      TraceWords.bits (TraceBanks.wide (@widePackedImage F A _ cp data (ExteriorCount X) j r t X R s payload w seed lo C grain ss origin
      (@DescentExterior.publicRows F cp data X j r t x) (z∘bind) i.1.val)) i.2 := by
  have h := @widePacked_read F A _ cp data (ExteriorCount X) j r t X R s payload w seed lo C grain ss origin
    (@DescentExterior.publicRows F cp data X j r t x) (z∘bind)
    split arch space pos room i
  refine Eq.trans ?_ h
  unfold wideHostPin
  cases @pin A w (ExteriorCount X) j r t
      (DescentPackedProfileInstall.end_ (lo + DescentPackedEpochShelves.extent grain ss) C grain)
      origin (@widePackedPin F A _ cp data X R s payload w seed lo C grain ss) i with
  | inr bit => rfl
  | inl p => cases p <;> rfl

end
end Hierarchy.DescentExteriorShelf.Root

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

variable (R s payload w : ℕ) (seed : Select X R s→A) (lo C grain : ℕ) (ss : List (Source A))
local notation "lastWord" => end_ (lo+extent grain ss) C grain
local notation "front" => lastWord+17*span j r t E
local notation "All" => Candidate Old K W q piece rows
variable (publicRows codes : ℕ)
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rows publicRows

def wideHeader (outer : P→Bool) (z : All→Bool) : Memory w :=
  Root.appended front extra
    (Root.widePackedImage X R s payload w seed lo C grain ss lastWord (DescentExterior.publicRows X outer) (z ∘ history))
    (DescentTerminalPublicIdentity.back (z ∘ chip) w codes publicRows)

def widePins : Fin (front+extra)×Fin (w+1)→(P⊕All)⊕Bool :=
  Root.appendPin front extra
    (Root.wideHostPin X R s payload w seed lo C grain ss history lastWord)
    (fun i=>(DescentTerminalPublicIdentity.pins K W q piece rows publicRows w codes i).map (Sum.inr ∘ chip) id)

theorem widePins_read (outer : P→Bool) (z : All→Bool) (arch : payload ≤ w) (extRoom : 2^j*t ≤ w) (modeRoom : B ≤ w)
    (positive : 0<grain) (held : ∀a∈ss,DescentTerminalEpochBits.width a.C*grain ≤ w)
    (i : Fin (front+extra)×Fin (w+1)) :
    (widePins X R s payload w seed lo C grain ss publicRows codes i).elim (Sum.elim outer z) id=
      TraceWords.bits (TraceBanks.wide (wideHeader X R s payload w seed lo C grain ss publicRows codes outer z i.1.val)) i.2 := by
  apply Root.appendPin_read
  · exact Root.wideHostPin_read X R s payload w seed lo C grain ss history lastWord outer z le_rfl arch extRoom positive held
  · intro a
    have exported:=DescentTerminalPublicIdentity.pins_read (z ∘ chip) w codes publicRows modeRoom a
    cases e : DescentTerminalPublicIdentity.pins K W q piece rows publicRows w codes a <;>
      rw [e] at exported <;> exact exported

/-- All terminal input words use the same choice as the separately retained history and public pins. -/
theorem wideRetained_ranges (outer : P→Bool) (z : All→Bool) (m : Memory w)
    (keep : ∀u < extra,m (front+u)=wideHeader X R s payload w seed lo C grain ss publicRows codes outer z (front+u)) :
    (∀u < DescentTerminalPaidBoot.total K W q piece codes rows,m (front+u)=DescentTerminalPaidBoot.back (z ∘ chip) w codes u) ∧
      ∀u < DescentTerminalPrimitiveArena.pad publicRows,
        m (front+DescentTerminalPaidBoot.total K W q piece codes rows+u)=(u:Word w) := by
  apply DescentTerminalPublicIdentity.ranges (z ∘ chip) codes publicRows front m
  intro u hu
  exact (keep u hu).trans (Root.suffix_read front extra _ _ ⟨u,hu⟩)

end
end Hierarchy.DescentTerminalFullPins

end OAI
