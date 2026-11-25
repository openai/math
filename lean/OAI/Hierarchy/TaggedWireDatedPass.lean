import OAI.Hierarchy.TaggedWireCappedPass
import OAI.Hierarchy.TaggedWireRoutedPackets

namespace OAI
/-! # The signed election followed by clipping and settlement of this date's overflow -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open WireTelescope ChosenPackets AdaptiveProbe LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical BigOperators

variable {h d k n g edges r s : ℕ} {F I : Type} [Field F] [Fintype I]
    {sampler : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin s}
    (B : Mount (S:=sampler) π place edges) (inj : Function.Injective place) (pad : Chord s)
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
    (order : Data h d k≃Fin g) (K : PortGraph (Fin s) I)
    {letters copies : Fin n→ℕ} (batch : ∀j,Row F s (letters j) (copies j)) {N : ℕ}
    {ports : Fin N→Chord s} (tender : ∀j,RowRouting (batch j) ports)
local notation "G" => ordinalGoods π place order
local notation "Vote" => BallChoices letters copies
variable (past : Widths s) (goods debit : Fin g→ℕ) (reserve used : I→ℕ)
    (paid : BallChoices letters copies→Fin edges→ℕ)
    (gain final spill : BallChoices letters copies→Fin g→ℕ)
local notation "start" => past+(G).chordWidths goods+K.chordWidths reserve
local notation "remaining" => fun a=>reserve a-used a
local notation "preclip" c => past+B.actual.chordWidths (paid c)+(G).chordWidths (fun i=>final c i+spill c i)+K.chordWidths remaining
local notation "passive" => past+(G).chordWidths (fun i=>goods i-debit i)+K.chordWidths remaining

variable (source : (∑j,(batch j).input)=(ordinalGoods π place order).chordWidths debit+K.chordWidths used)
    (target : ∀c : BallChoices letters copies,(∑j,(tender j).post (c j))=
      (ordinalGoods π place order).chordWidths (gain c)+B.actual.chordWidths (paid c))
    (fund : ∀i,debit i≤goods i) (fundR : ∀i,used i≤reserve i)
    (balance : ∀c i,goods i+gain c i=final c i+spill c i+debit i)

include source fund fundR in
private theorem dated_input : passive+(∑j,(batch j).input)=start := by
  rw [source]
  have cg : (G).chordWidths (fun i=>goods i-debit i)+(G).chordWidths debit=(G).chordWidths goods:=by
    rw [←chordWidths_add]
    exact congrArg (G).chordWidths (funext fun i=>Nat.sub_add_cancel (fund i))
  have ck : K.chordWidths remaining+K.chordWidths used=K.chordWidths reserve:=by
    rw [←chordWidths_add]
    exact congrArg K.chordWidths (funext fun i=>Nat.sub_add_cancel (fundR i))
  rw [←cg,←ck]
  abel

include target fund balance in
private theorem dated_output (c : Vote) : passive+(∑j,(tender j).post (c j))=preclip c := by
  rw [target c]
  have eqn : (G).chordWidths (fun i=>goods i-debit i)+(G).chordWidths (gain c)=
      (G).chordWidths (fun i=>final c i+spill c i):=by
    rw [←chordWidths_add]
    apply congrArg (G).chordWidths
    funext i
    have fg:=fund i
    have account:=balance c i
    omega
  rw [←eqn]
  abel

local notation "M" => fun i j=>(tender i).entry j
local notation "openIn" => dated_input order K batch past goods debit reserve used source fund fundR
local notation "openOut" => dated_output B order K batch tender past goods debit reserve used paid gain final spill target fund balance
local notation "ballots" => PassMatrix.actual M passive openIn openOut

/-- The full dated goods include passive holdings. At a cap only the
current excess is routed away; every other live bit stays on its good. -/
def afterVote (c : Vote) : Transfer h d k where
  old:=fun _=>0
  active:=fun i=>final c (order i)+spill c (order i)
  held:=fun _=>0
  kept:=fun i=>final c (order i)
  spill:=fun i=>spill c (order i)
  balanced:=fun _=>by simp
local notation "clip" => afterVote order final spill
local notation "archive" => (fun c : BallChoices letters copies => B.actual.chordWidths (paid c))
local notation "unclipped" => (fun (c : BallChoices letters copies) (i : Fin g) => final c i + spill c i)
local notation "finished" c => output B (past + B.actual.chordWidths (paid c) +
  K.chordWidths (fun i => reserve i - used i)) (afterVote order final spill c)

def datedPass (c : Vote) : SiteMatrix (State start) (State (finished c)) F :=
  cappedPass B inj pad enum order K remaining past archive unclipped clip
    (fun _ _=>rfl) (fun _ _=>rfl) ballots c

theorem datedPass_action (x : ∀s,State start s) :
    (raw F start).coeff x=∑c : Vote,SiteMatrix.act
      (datedPass B inj pad enum order K batch tender past goods debit reserve used paid gain final spill
        source target fund fundR balance c) (raw F (finished c)).coeff x := by
  exact cappedPass_action B inj pad enum order K remaining past archive unclipped clip
    (fun _ _ => rfl) (fun _ _ => rfl) ballots
    (PassMatrix.actual_action M passive openIn openOut (fun j => (tender j).entry_sum)) x

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer
end

end OAI
