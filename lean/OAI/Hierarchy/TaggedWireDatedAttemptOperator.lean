import OAI.Hierarchy.TaggedWireDatedPass
import OAI.Hierarchy.TaggedWireFeedRebase

namespace OAI
/-! # An elected packet date on chronological widths with changing purchased records -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical BigOperators

theorem rebase_family {s : ℕ} {F : Type*} [Field F] {C : Type*} [Fintype C]
    {U U' : Widths s} {V V' : C→Widths s} (left : U=U') (right : ∀c,V c=V' c)
    (gate : ∀c,SiteMatrix (State U) (State (V c)) F)
    (sum : ∀x,(raw F U).coeff x=∑c,SiteMatrix.act (gate c) (raw F (V c)).coeff x)
    (x : ∀i,State U' i) :
    (raw F U').coeff x=∑c,SiteMatrix.act (rebase left (right c) (gate c)) (raw F (V' c)).coeff x := by
  subst U'
  have eqn : V=V':=funext right
  subst V'
  exact sum x
end Hierarchy.WireTelescope

namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open WireTelescope ChosenPackets AdaptiveProbe LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical BigOperators

variable {h d k n g s edges r : ℕ} {F : Type} [Field F]
    {sampler : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin s}
    (B : Mount (S:=sampler) π place edges) (inj : Function.Injective place) (pad : Chord s)
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
    (o : Data h d k≃Fin g) {letters copies : Fin n→ℕ}
    (batch : ∀j,Row F s (letters j) (copies j)) {N : ℕ} {ports : Fin N→Chord s}
    (tender : ∀j,RowRouting (batch j) ports)
local notation "G" => ordinalGoods π place o
local notation "K" => catalystGraph place
local notation "C" => BallChoices letters copies
variable (pre : PortGraph (Fin s) (Fin edges))
    (post : BallChoices letters copies→PortGraph (Fin s) (Fin edges))
    (past : Fin edges→ℕ) (next : BallChoices letters copies→Fin edges→ℕ) (goods debit : Fin g→ℕ)
    (reserve used : (Columns h d × Fin k)→ℕ) (fresh : BallChoices letters copies→(Columns h d × Fin k)→ℕ)
    (paid : BallChoices letters copies→Fin edges→ℕ) (gain final spill : BallChoices letters copies→Fin g→ℕ)
local notation "U" => ledger (π:=π) (place:=place) pre past (goods ∘ o) reserve
local notation "V" c => ledger (π:=π) (place:=place) (post c) (next c) (final c ∘ o) (fresh c)
local notation "temp" => B.actual.chordWidths past
local notation "before" => temp+(G).chordWidths goods+(K).chordWidths reserve
local notation "after₀" c => output B (B.actual.chordWidths past+B.actual.chordWidths (paid c)+
  (catalystGraph place).chordWidths (fun a => reserve a-used a))
  (afterVote o final spill c)

variable (orig : ∀e,0<past e→B.actual.tail e=pre.tail e ∧ B.actual.head e=pre.head e)
    (dest : ∀c e,0<next c e→B.actual.tail e=(post c).tail e ∧ B.actual.head e=(post c).head e)
    (bill : ∀c e,next c e=past e+paid c e+routeLoad B.ordinary (spill c ∘ o) e)
    (release : ∀c a,fresh c a=reserve a-used a)
    (source : (∑j,(batch j).input)=(ordinalGoods π place o).chordWidths debit+(catalystGraph place).chordWidths used)
    (target : ∀c : BallChoices letters copies,(∑j,(tender j).post (c j))=
      (ordinalGoods π place o).chordWidths (gain c)+B.actual.chordWidths (paid c))
    (fund : ∀i,debit i≤goods i) (fundR : ∀i,used i≤reserve i)
    (balance : ∀c i,goods i+gain c i=final c i+spill c i+debit i)

include orig in
theorem attempt_entry_width : before=U := by
  unfold ledger
  rw [ordinalGoods_width,paid_geometry B.actual pre past orig]

include dest bill release in
theorem attempt_exit_width (c : C) : (after₀ c) = (V c) := by
  have reorder (w a b d : Widths s) : w + a + b + d = w + d + b + a := by
    ac_rfl
  unfold output ledger
  rw [←paid_geometry B.actual (post c) (next c) (dest c),funext (bill c),funext (release c)]
  simp only [afterVote,chordWidths_add,chordWidths_empty,add_zero]
  exact reorder (B.actual.chordWidths past + B.actual.chordWidths (paid c))
    ((catalystGraph place).chordWidths (fun a => reserve a - used a))
    ((commodityGraph π place).chordWidths (final c ∘ o))
    (B.actual.chordWidths (routeLoad B.ordinary (spill c ∘ o)))

set_option maxHeartbeats 1200000 in
include inj pad enum orig dest bill release source target fund fundR balance in
/-- The original accepted row matrices, one clipping matrix for each result, and only the positively
occupied chronological endpoint records are used. This works with arbitrary orientations and repeated chords. -/
def datedAttemptOperator :
    {T : ∀c : C,SiteMatrix (State U) (State (V c)) F //
      ∀(x : ∀i,State U i),(raw F U).coeff x=∑c : C,
        SiteMatrix.act (A:=State U) (B:=State (V c)) (T c) (raw F (V c)).coeff x} := by
  let gates (c : C) : SiteMatrix (State before) (State (after₀ c)) F :=
    datedPass B inj pad enum o K batch tender temp goods debit reserve used paid gain final spill
      source target fund fundR balance c
  have start : before=U := attempt_entry_width B o pre past goods reserve orig
  have stop (c : C) : (after₀ c) = (V c) :=
    attempt_exit_width B o post past next reserve used fresh paid final spill dest bill release c
  exact ⟨fun c=>rebase start (stop c) (gates c),
    fun x => rebase_family start stop gates (datedPass_action B inj pad enum o K batch tender temp goods debit
      reserve used paid gain final spill source target fund fundR balance) x⟩

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer
end

end OAI
