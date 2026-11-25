import OAI.Hierarchy.DescentSeedPrimitiveEncoding
import OAI.Hierarchy.DescentPrimitivePaletteAllFit
import OAI.Hierarchy.DescentPrimitivePaletteCounts
import OAI.Hierarchy.DescentPrimitivePalette
import OAI.Hierarchy.DescentNormalizedEpochs

namespace OAI
/-! # The same finite scalar labels read the actual archive at every surviving leaf -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentKernelHistory DescentRotor DescentResetGates DescentCompiler DescentEpochTagKeys
open DescentResetTrunks DescentRouterBank DescentChosenRouter DescentContactTree DescentResetAttachments Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

def Encoding.installTo {H Q U U' : Type} [Fintype H] [Fintype Q] {B : BitDescription W}
    (read : U→List (List Bool)→F) (old : Encoding U read B) (home : W.graph.Site→H) (group : Bool→W.graph.Edge→Q)
    (flag : H→Bool) {L d' : ℕ} {w : W.graph.Edge→ℕ} (same : w=W.graph.width)
    (R : Network d' (Bool×Q) (publicWidth group w)) (legacy sorted : R.Tables F) (key : W.graph.Edge↪Fin L)
    (scalar : U'→List (List Bool)→F) (r : SiteBits (U:=U') R) (valid : ReadsBits R scalar r sorted)
    (relay : U) (relayRead : read relay=equalWord) (bank : U'→U) (bankRead : ∀x,read (bank x)=scalar x) :
    Encoding U read (B.installed home group flag same R legacy sorted key scalar r valid) := by
  subst w
  refine ⟨Sum.elim old.code (Sum.elim (fun _=>relay) bank),?_⟩
  intro tag
  rcases tag with tag|tag|tag
  · exact old.correct tag
  · exact relayRead
  · exact bankRead tag

variable {q ε : ℝ} {S : AtomSchedule} {k i z D w hist n h C f g cut tail s Z p : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (op : RotorSpec) (menu : Runnable F op)

def Encoding.reset (bank : ClosedReset cap ctl) (hp : 0<p) (divides : p∣bank.reset.unit)
    (oneMenu : Chronology.resetSpec bank=op) (a : Chronology.Archive W)
    (old : Encoding (Label G s Z op) (dictionary G op menu p) a.bit) :
    Encoding (Label G s Z op) (dictionary G op menu p) (Chronology.resetArchive bank p hp divides a).bit := by
  let split:=BitDescription.granular W bank.count (z*G.b) bank.fit a.bit
  have pre : Encoding (Label G s Z op) (dictionary G op menu p) split:=⟨old.code,old.correct⟩
  let key:=DescentOrderedReset.grains W bank.count bank.order
  let hm : actualSpec bank=op := (actual_eq bank).trans oneMenu
  have fit : bank.reset.unit=bank.reset.unit/p*p := (Nat.div_mul_cancel divides).symm
  let out:=split.batchedReset bank.reset bank.terminals key _ p hp fit (Chronology.resetMenu bank)
  have num : Encoding (Label G s Z op) (dictionary G op menu p) out := by
    unfold out BitDescription.batchedReset BitDescription.fromBank
    apply Encoding.installTo (dictionary G op menu p) pre _ _ _ _ _ _ _ _ _ _ _
      (Sum.inr (Sum.inr (Sum.inl ()))) rfl (fun x=>Sum.inr (Sum.inr (Sum.inr (resetTag op bank hm x))))
    intro x
    exact gate_eq op bank menu hm x
  exact num.follow bank.reblock

variable {W₀ W₁ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ wire : ℕ}
    {first : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist} {last : Reached W₁ G q ε S k i₁ z₁ D₁ wire hist}

theorem grain_le (path : Chronology.Path first last) : z₁≤z₀ := by
  induction path with
  | here=>exact le_rfl
  | @ordinary _ _ z D z' D' _ prev _ _ _ _ _ _ ticket ih=>
    exact (show z'≤z from ticket.grainStep ▸ Nat.le_mul_of_pos_right z' G.base_pos).trans ih
  | reset prev bank ih=>exact ih

def encodePath (path : Chronology.Path first last) (hp : 0<p) (whole : path.whole p)
    (fixed : path.OnlyRotor op) (a : Chronology.Archive W₀)
    (old : Encoding (Label G s z₀ op) (dictionary G op menu p) a.bit) :
    Encoding (Label G s z₀ op) (dictionary G op menu p) (path.archive p hp a whole).bit := by
  induction path with
  | here=>exact old
  | @ordinary _ _ z D z' D' source prev u he T c norm target ticket ih=>
    have prior:=ih whole fixed
    have limit : T.z≤z₀ := ticket.quantum.trans source.grain ▸ grain_le prev
    exact (Encoding.scanned G op menu prior T he c limit).follow norm
  | reset prev bank ih=>exact Encoding.reset op menu bank hp whole.2 fixed.2 _ (ih whole.1 fixed.1)

def indexed (n : Fin (colors G s Z op)) := dictionary G op menu p ((codec (G:=G) op).read n)
theorem indexed_read {B : BitDescription W} (e : Encoding (Label G s Z op) (dictionary G op menu p) B) (t : B.Tag) :
    indexed (p:=p) op menu ((codec (G:=G) op).store (e.code t))=B.scalar t := by
  rw [indexed,Codec.read_store _ _ (all_fit op _)];exact e.correct t

end
end Hierarchy.DescentPrimitivePalette

end OAI
