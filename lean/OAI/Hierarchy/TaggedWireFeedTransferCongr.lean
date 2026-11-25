import OAI.Hierarchy.TaggedWireOnlySpillCongr
import OAI.Hierarchy.TaggedWireFeedRepartition
import OAI.Hierarchy.TaggedWireFeedAction

namespace OAI
/-! # Rebase a whole feed or a physical post-vote carry onto the genuine spill mount -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope ProtocolRAMDateSpillRank ProtocolRAM.Calendar.CoreRoute
open scoped Classical BigOperators
variable {F : Type*} [Field F] {S : PurchaseSampler} {h d k K edges : ℕ}
    {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
variable (B C : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord K) (o : Orders h d k)
    (carry : Widths K) (T : Transfer h d k)

/-- The paid ports, held stock, and unspent inputs occupy the stationary block. -/
private abbrev passive (G : PortGraph (Fin K) (Data h d k)) (carry : Widths K)
    (T : Transfer h d k) := carry+G.chordWidths T.held+G.chordWidths T.kept

private theorem lift_eq {A A' : Widths K} (eqn : A=A')
    (P : SiteMatrix (State ((commodityGraph π place).chordWidths T.spill)) (State A) F)
    (Q : SiteMatrix (State ((commodityGraph π place).chordWidths T.spill)) (State A') F) (same : rebase rfl eqn P=Q) :
    rebase rfl (congrArg ((passive (commodityGraph π place) carry T)+·) eqn)
        (LedgerStep.matrix (commodityGraph π place) carry T.old T.active T.held T.kept T.spill T.balanced P)=
      LedgerStep.matrix (commodityGraph π place) carry T.old T.active T.held T.kept T.spill T.balanced Q := by
  cases eqn
  cases same
  rfl

theorem matrix_congr (sameRow : B.row=C.row) :
    ∃head : output B carry T=output C carry T,
      rebase rfl head (matrix (F:=F) B inj pad (spillEnum B o) carry T) =
        matrix (F:=F) C inj pad (spillEnum C o) carry T := by
  obtain ⟨eqn,same⟩:=B.onlySpill_congr (F:=F) C inj pad o T.spill sameRow
  exact ⟨congrArg ((passive (commodityGraph π place) carry T)+·) eqn,
    lift_eq (π:=π) (place:=place) carry T eqn _ _ same⟩

private theorem carry_at {A A' U V : Widths K} (eqn : A=A')
    (P : SiteMatrix (State U) (State A) F) (Q : SiteMatrix (State U) (State A') F)
    (same : rebase rfl eqn P=Q) (s : Fin K)
    (x x' : State (V+U) s) (y : State (V+A) s) (y' : State (V+A') s)
    (entry : HEq x x') (exit : HEq y y') :
    LedgerStep.carry Q V s x' y'=LedgerStep.carry P V s x y := by
  cases eqn
  cases same
  rw [←eq_of_heq entry,←eq_of_heq exit]
  exact congrArg (fun M=>LedgerStep.carry M V s x y) (eq_of_heq (rebase_heq rfl rfl P))

/-- Evaluating the public comparator at the held and emitted words of this
very transfer recovers its full reference matrix at both original site states.
The two heterogeneous equalities are precisely the caller's entry and exit casts. -/
theorem checked_carry (sameRow : B.row=C.row)
    (stock : Data h d k→ℕ) (sameStock : stock=T.spill) (rest : Widths K)
    (sameRest : rest=(passive (commodityGraph π place) carry T))
    (s : Fin K) (x : State (input (π:=π) (place:=place) carry T) s) (y : State (output B carry T) s)
    (xx : State (rest+(commodityGraph π place).chordWidths stock) s)
    (yy : State (rest+C.actual.chordWidths (routeLoad C.ordinary stock)) s)
    (entry : HEq (LedgerStep.repartition (commodityGraph π place) carry T.old T.active T.held T.kept T.spill T.balanced s x) xx)
    (exit : HEq y yy) :
    LedgerStep.carry (C.onlySpill (F:=F) inj pad stock (spillEnum C o)) rest s xx yy =
      matrix (F:=F) B inj pad (spillEnum B o) carry T s x y := by
  subst stock
  subst rest
  obtain ⟨eqn,same⟩:=B.onlySpill_congr (F:=F) C inj pad o T.spill sameRow
  have value := carry_at eqn _ _ same s
    (LedgerStep.repartition (commodityGraph π place) carry T.old T.active T.held T.kept T.spill T.balanced s x) xx y yy entry exit
  exact value.trans (LedgerStep.matrix_repartition (commodityGraph π place) carry T.old T.active T.held T.kept T.spill
    T.balanced _ s x y).symm

/-- The post-vote transfer keeps every terminal good and drops its zero held bank.
This is the carry width compared by the two original dated word operands. -/
theorem afterVote_rest (kept spill : Data h d k→ℕ) :
    let cap : Transfer h d k:=⟨fun _=>0,fun j=>kept j+spill j,fun _=>0,kept,spill,fun _=>by simp⟩
    carry+(commodityGraph π place).chordWidths cap.held+(commodityGraph π place).chordWidths cap.kept=carry+(commodityGraph π place).chordWidths kept := by
  intro cap
  have empty : (commodityGraph π place).chordWidths (fun _=>0)=0 := by simp [PortGraph.chordWidths,chordWidth_scaled]
  change carry+(commodityGraph π place).chordWidths (fun _=>0)+(commodityGraph π place).chordWidths kept=_
  rw [empty,add_zero]

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer
end

end OAI
