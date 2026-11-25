import OAI.Hierarchy.TaggedWireSignedComposition
import OAI.Hierarchy.TaggedWireDatedAttemptOperator

namespace OAI
/-! # Signed packet pass with the native debit readings of each completed branch -/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open WireTelescope ChosenPackets AdaptiveProbe LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical BigOperators

variable {h d k n g s edges : ℕ} {F : Type} [Field F]
    {sampler : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin s}
    (inj : Function.Injective place) (pad : Chord s) (o : Data h d k≃Fin g)
    {letters copies : Fin n→ℕ} (row : ∀j,Row F s (letters j) (copies j))
    {N : ℕ} {ports : Fin N→Chord s} (tender : ∀j,RowRouting (row j) ports)
local notation "C" => BallChoices letters copies
local notation "G" => ordinalGoods π place o
local notation "K" => catalystGraph place
variable (one : BallChoices letters copies) (B : BallChoices letters copies→Mount (S:=sampler) π place edges)
    {r : BallChoices letters copies→ℕ} (visits : ∀c,Fin (r c)≃RouteOccurrence (B c).ordinary (Empty.elim : Empty→List (Fin edges)))
    (pre : PortGraph (Fin s) (Fin edges)) (past : Fin edges→ℕ) (next : BallChoices letters copies→Fin edges→ℕ)
    (goods : Fin g→ℕ) (debit : BallChoices letters copies→Fin g→ℕ) (reserve : (Columns h d × Fin k)→ℕ) (used fresh : BallChoices letters copies→(Columns h d × Fin k)→ℕ)
    (paid : BallChoices letters copies→Fin edges→ℕ) (gain final spill : BallChoices letters copies→Fin g→ℕ)

local notation "oldPaid" => pre.chordWidths past
local notation "supply" => oldPaid+(G).chordWidths goods+(K).chordWidths reserve
local notation "current" c => ledger (π:=π) (place:=place) (B c).actual (next c) (final c ∘ o) (fresh c)
local notation "remaining" c => fun a=>reserve a-used c a
local notation "idle" c => oldPaid+(G).chordWidths (fun i=>goods i-debit c i)+(K).chordWidths (remaining c)
local notation "stock" c => oldPaid+(B c).actual.chordWidths (paid c)+(K).chordWidths (remaining c)
local notation "T" c => afterVote o final spill c
local notation "middle" c => input (π:=π) (place:=place) (stock c) (T c)
local notation "M" => fun i j=>(tender i).entry j

variable (source : ∀c : BallChoices letters copies,(∑j,(row j).input)=(ordinalGoods π place o).chordWidths (debit c)+(catalystGraph place).chordWidths (used c))
    (target : ∀c : BallChoices letters copies,(∑j,(tender j).post (c j))=(ordinalGoods π place o).chordWidths (gain c)+(B c).actual.chordWidths (paid c))
    (fund : ∀c i,debit c i≤goods i) (fundR : ∀c a,used c a≤reserve a)
    (balance : ∀c i,goods i+gain c i=final c i+spill c i+debit c i)
    (prior : ∀c e,0<past e→pre.tail e=(B c).actual.tail e ∧ pre.head e=(B c).actual.head e)
    (bill : ∀c e,next c e=past e+paid c e+routeLoad (B c).ordinary (spill c ∘ o) e)
    (release : ∀c a,fresh c a=reserve a-used c a)

include source fund fundR in
private theorem debited_input (c : C) : (idle c)+∑j,(row j).input=supply := by
  rw [source c]
  have gword : (G).chordWidths (fun i=>goods i-debit c i)+(G).chordWidths (debit c)=(G).chordWidths goods:=by
    rw [←chordWidths_add]
    exact congrArg (G).chordWidths (funext fun i=>Nat.sub_add_cancel (fund c i))
  have pair : (K).chordWidths (remaining c)+(K).chordWidths (used c)=(K).chordWidths reserve:=by
    rw [←chordWidths_add]
    exact congrArg (K).chordWidths (funext fun i=>Nat.sub_add_cancel (fundR c i))
  rw [←gword,←pair]
  abel

local notation "old" c => debited_input o row pre past goods debit reserve used source fund fundR c

include row source fund fundR in
/-- The original widths imply one common passive tensor, even using the separate
measured ledgers of all chosen histograms and all their original completions. -/
theorem identical_remainder (c : C) : (idle one)=(idle c) :=
  add_right_cancel ((old one).trans (old c).symm)

include source target fund fundR balance in
private theorem debited_middle (c : C) : (idle one)+∑j,(tender j).post (c j)=middle c := by
  rw [identical_remainder o row one pre past goods debit reserve used source fund fundR c,target c]
  have goodsSum : (G).chordWidths (fun i=>goods i-debit c i)+(G).chordWidths (gain c)=
      (G).chordWidths (fun i=>final c i+spill c i):=by
    rw [←chordWidths_add]
    apply congrArg (G).chordWidths
    funext i
    have bound:=fund c i
    have account:=balance c i
    omega
  unfold input
  simp only [afterVote,chordWidths_empty,add_zero]
  have sumEq:=ordinalGoods_width π place o (fun i=>final c i+spill c i)
  simp only [Function.comp_def] at sumEq
  rw [←sumEq,←goodsSum]
  abel

include prior bill release in
private theorem debited_output (c : C) : output (B c) (stock c) (T c)=current c := by
  unfold output ledger
  rw [paid_geometry pre (B c).actual past (prior c),funext (bill c),funext (release c)]
  simp only [afterVote,chordWidths_add,chordWidths_empty,add_zero,Function.comp_def]
  ac_rfl

local notation "mid" => debited_middle o row tender one B pre past goods debit reserve used paid gain final spill
  source target fund fundR balance
local notation "vote" => PassMatrix.actual M (idle one) (old one) mid
local notation "edgeGate" c => matrix (F:=F) (B c) inj pad (visits c) (stock c) (T c)
local notation "stop" c => debited_output o B pre past next reserve used fresh paid final spill prior bill release c

include inj pad one visits row tender source target fund fundR balance prior bill release in
/-- Every cap transfer uses the actual native itinerary of its own completed choice. Its
signed predecessor is the same fixed family of elected row tiles for every choice. -/
def measuredAttempt :
    {gate : ∀c : C,SiteMatrix (State supply) (State (current c)) F //
       ∀x : ∀i, State supply i, (raw F supply).coeff x = ∑c : C,
         SiteMatrix.act (A := State supply) (B := State (current c)) (gate c) (raw F (current c)).coeff x} := by
  refine ⟨fun c=>SiteMatrix.compose (vote c) (rebase rfl (stop c) (edgeGate c)),?_⟩
  intro x
  refine (PassMatrix.actual_action M (idle one) (old one) mid (fun i => (tender i).entry_sum) x).trans
    (Finset.sum_congr rfl ?_)
  intro c _
  let pass : SiteMatrix (State supply) (State (middle c)) F := vote c
  let move : SiteMatrix (State (middle c)) (State (current c)) F := rebase rfl (stop c) (edgeGate c)
  have coeff : (raw F (middle c)).coeff = SiteMatrix.act move (raw F (current c)).coeff :=
    funext (rebase_action rfl (stop c) (edgeGate c) (action (B c) inj pad (visits c) (stock c) (T c)))
  exact (congrArg (fun f => SiteMatrix.act pass f x) coeff).trans
    (SiteMatrix.act_compose pass move (raw F (current c)).coeff x)

include source target fund fundR balance prior bill release in
theorem measured_factors (c : C) :
    Through (PassMatrix.matrix M (idle one) c) (edgeGate c)
      ((measuredAttempt inj pad o row tender one B visits pre past next goods debit reserve used fresh
        paid gain final spill source target fund fundR balance prior bill release).1 c) :=
  ⟨old one,mid c,stop c,rfl⟩

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer
end

end OAI
