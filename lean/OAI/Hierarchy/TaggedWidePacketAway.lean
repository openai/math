import OAI.Hierarchy.TaggedWirePacketOffsite
import OAI.Hierarchy.ProbeAwayPartyBits
import OAI.Hierarchy.TaggedWidePassSites

namespace OAI
/-! # All unplaced repair rows contribute one to the physical simultaneous pass -/
noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open AdaptiveProbe Probe
open scoped Classical BigOperators
variable {F : Type} [Field F] {S N r : ℕ} {phys : Fin N → Chord S} {s : Fin S}

/-- Both real factors of the concrete signed replacement vanish from the
local product outside the strip. This includes the middle of a priced
two-radius path as well as its endpoints. -/
theorem packet_away (P : Placed F S) (R : RowRouting (Row.packet P r) phys)
    (c : Histogram (Fin P.data.terms) r) (away : s∉Set.range P.place)
    (short : ∀i,(R.install.route i).length≤2)
    (routes : ∀i,0<R.bits c i → (R.source i).1.1≠s ∧ (R.source i).1.2≠s ∧
      ∀e∈R.install.route i,(phys e).1.1≠s ∧ (phys e).1.2≠s)
    (old : State (Row.input (.packet P r)) s) (new : State (R.post c) s) :
    R.entry c s old new=1 := by
  let : Subsingleton (State (Row.output (.packet P r) c) s) := P.offers_away c away
  let : Nonempty (State (Row.output (.packet P r) c) s) := ⟨fun _=>0⟩
  unfold entry SiteMatrix.compose
  apply PassMatrix.off_routing _ _ old
  · exact fun y=>P.entry_away c away old y
  · exact fun y=>R.install_off_site (F:=F) c s short routes y new

/-- The native zero-copy row has no requested ports or installed arcs. -/
theorem skipped_away (letters : ℕ) (c : Histogram (Fin letters) 0)
    (old : State ((Row.skipped (F:=F) (S:=S) letters).input) s)
    (new : State ((skipped (F:=F) phys letters).post c) s) :
    (skipped (F:=F) phys letters).entry c s old new=1 := by
  let R := skipped (F:=F) phys letters
  let : Subsingleton (State (Row.output (Row.skipped (F:=F) (S:=S) letters) c) s) := Row.skip_state ..
  let : Nonempty (State (Row.output (Row.skipped (F:=F) (S:=S) letters) c) s) := ⟨fun _=>0⟩
  change R.entry c s old new=_
  unfold entry SiteMatrix.compose
  apply PassMatrix.off_routing _ _ old
  · exact fun y=>Row.skip_entry letters c s old y
  · exact fun y=>R.install_off_site (F:=F) c s (fun i=>nomatch i) (fun i=>nomatch i) y new

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
