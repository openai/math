import OAI.Hierarchy.TaggedWireCursorReplay
import OAI.Hierarchy.TaggedWirePhysicalTerm

namespace OAI
/-! # A complete physical trace for each original prefix-dependent branch -/

noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 800000
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope TaggedPrune Tagged ProtocolRAMEmit
open ProtocolRAM.Calendar WireTelescope.CalendarTape
open scoped Classical BigOperators

variable {h d k w R M den : ℕ} {F : Type*} {X : Type} [Field F]
variable (p : Equiv.Perm (Tagged.Row h)) {slots : Event→Slot X} {es : List Event} {startMem : X}
private abbrev initialPrefix (slots : Event → Slot X) (es : List Event) (startMem : X) :
    WireTelescope.CalendarTape.Prefix slots es startMem es startMem := .start

variable (width : ∀{tail x},WireTelescope.CalendarTape.Prefix slots es startMem tail x → Widths (siteLast h d k+1))
    (Mrow : ∀{e tail x}(t : WireTelescope.CalendarTape.Prefix slots es startMem (e::tail) x)(c:(slots e).choice x),
      SiteMatrix (State (width t)) (State (width (Prefix.advance t c))) F)
    (law : ∀{e tail x}(t : WireTelescope.CalendarTape.Prefix slots es startMem (e::tail) x)
      (v : ∀s,State (width t) s),(raw F (width t)).coeff v=
      ∑c,SiteMatrix.act (Mrow t c) (raw F (width (Prefix.advance t c))).coeff v)
    (initial : exposedWidth p d k w R=width (initialPrefix slots es startMem))
    (reported : ∀j : Path slots es startMem,Report p d k w R M den
      (width (Prefix.finish (initialPrefix slots es startMem) j)))

local notation "B" => initialPrefix slots es startMem
local notation "Σ₀" => (Prefix.cursorSlot (slot:=slots) (events:=es) (x₀:=startMem))
local notation "V₀" => Prefix.atCursor (initialPrefix slots es startMem)

include reported in
def cursorReport (j : Path (Prefix.cursorSlot (slot:=slots) (events:=es) (x₀:=startMem)) es
    (Prefix.atCursor (initialPrefix slots es startMem))) :
    Report p d k w R M den (Prefix.atWidth @width (terminal Σ₀ es V₀ j)) :=
  let t:=reported ((Prefix.histories (initialPrefix slots es startMem)).symm j)
  { t with ledger:=t.ledger.trans (congrArg (Prefix.atWidth @width) (Prefix.terminal_history (initialPrefix slots es startMem) j)).symm }

local notation "D" => cursorReport p @width reported
local notation "V" => Prefix.atWidth @width
local notation "next" => Prefix.atStep @width @Mrow
local notation "H" => Prefix.histories B
local notation "E" => family p Σ₀ es V V₀ initial next (Prefix.atStep_sum @width @Mrow @law) D

include Mrow law initial in
def actualFamily : Expansion (Exposed (F:=F) (d:=d) (k:=k) (w:=w) (R:=R) p) (Path slots es startMem)
    (fun j=>(reported j).output) where
  part j:=(E).part (H j)
  sum:=(E).sum.trans ((H).sum_comp (E).part).symm
  image j:=by
    have equal : (D (H j)).output=(reported j).output := by
      change (reported ((H).symm (H j))).output=(reported j).output
      rw [Equiv.symm_apply_apply]
    exact equal ▸ (E).image (H j)

/-- The final contraction uses one variable of its authentic width for each
reported global row. The site kernel remains available on the same trace. -/
theorem branch_words (j : Path slots es startMem)
    (v : ∀s,(Exposed (F:=F) (d:=d) (k:=k) (w:=w) (R:=R) p).Leg s) :
    (actualFamily p @width @Mrow @law initial reported).part j v=
      ∑a : ∀e,Fin (2^(D (H j)).widthAt e),∏s,kernel p Σ₀ es V V₀ initial next D (H j) s
        (v s) ((D (H j)).ports a s) :=
  term_words p Σ₀ es V V₀ initial next (Prefix.atStep_sum @width @Mrow @law) D (H j) v

theorem branch_site (j : Path slots es startMem) (s : Fin (siteLast h d k+1))
    (v : (Exposed (F:=F) (d:=d) (k:=k) (w:=w) (R:=R) p).Leg s) (a : ∀e,Fin (2^(D (H j)).widthAt e)) :
    kernel p Σ₀ es V V₀ initial next D (H j) s v ((D (H j)).ports a s)=
      ∑z : State (V V₀) s × PartyStates Σ₀ V s es V₀ (H j),
        partyWeight Σ₀ V next s es V₀ (H j) (fun y=>(D (H j)).finish s y ((D (H j)).ports a s)) z.1 z.2 *
          entry p V V₀ initial s v z.1 :=
  site_terms p Σ₀ es V V₀ initial next D (H j) s v a

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm

end
end OAI
