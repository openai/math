import OAI.Hierarchy.DescentPrivatePeerSupport
import OAI.Hierarchy.DescentResetPeerPortfolio

namespace OAI
/-! # Private reset peer evidence on the same fixed side, root and wire axis as the native catalog -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster DescentResetPeerUnionRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex

abbrev PrivateProbe := Bool×(Z).RootTicket T×Fin capacity
def privateProbeId : PrivateProbe B↪Fin (privateCount B) := localPrivateId r (2^(Z).n) capacity

/-- Padded root codes have zero evidence before testing whether the underlying edge has any width. -/
def privateSheet (eval : PrivateProbe B→ℕ) (key : Fin (privateCount B)) : ℕ :=
  if h : ∃p,privateProbeId B p=key then eval h.choose else 0

theorem privateSheet_at (eval : PrivateProbe B→ℕ) (p : PrivateProbe B) :
    privateSheet B eval (privateProbeId B p)=eval p := by
  have exists_ : ∃q,privateProbeId B q=privateProbeId B p:=⟨p,rfl⟩
  simp only [privateSheet,dite_eq_left exists_,(privateProbeId B).injective exists_.choose_spec]

theorem privateSheet_sound (eval : PrivateProbe B→ℕ) (key : Fin (privateCount B))
    (live : privateSheet B eval key≠0) : ∃p,privateProbeId B p=key ∧ privateSheet B eval key=eval p := by
  by_cases h : ∃p,privateProbeId B p=key
  · exact ⟨h.choose,h.choose_spec,by simp [privateSheet,h]⟩
  · exact False.elim (live (by simp [privateSheet,h]))

/-- The public private-wire axis ranges over both polarities, every real root and every device wire.
This tightens the four-axis mathematical union to the very dimension used by the literal CPU. -/
theorem private_sheet_tickets {H D₀ : ℕ} (prev : Fintype.card input.V ≤ H) (peers : Fin H→Fin D₀→Option (Fin H))
    (old : Fin (Fintype.card input.V)) (here : Fin shelf) (next : Fin (H*shelf))
    (code : Block (T).commonDepth→Bool→(Z).RootTicket T→Fin capacity→ℕ)
    (read : ∀g₀ s t slot,let v:=finProdFinEquiv (old.castLE prev,here)
      (∃j : Fin (Candidates.count shelf D₀),Candidates.candidate peers v j=some next ∧ code g₀ s t slot=j.val+1) ↔
        ∃p,privateRawAt B old g₀ s t slot p ∧ rawPeer B (privateWire B p) v.val next.val) :
    let v:=finProdFinEquiv (old.castLE prev,here)
    (∃(key : Fin (privateCount B)) (g₀ : Block (T).commonDepth) (j : Fin (Candidates.count shelf D₀)),Candidates.candidate peers v j=some next ∧
       privateSheet B (fun p=>code g₀ p.1 p.2.1 p.2.2) key=j.val+1) ↔
      ∃p,rawPeer B (privateWire B p) v.val next.val := by
  intro v
  refine Iff.trans ?_ (private_ticket_union B prev peers old here next code read)
  constructor
  · rintro ⟨key,g₀,j,peer,digit⟩
    obtain ⟨p,_,read⟩:=privateSheet_sound B (fun p=>code g₀ p.1 p.2.1 p.2.2) key (by rw [digit];omega)
    exact ⟨g₀,p.1,p.2.1,p.2.2,j,peer,read.symm.trans digit⟩
  · rintro ⟨g₀,s,t,slot,j,peer,digit⟩
    exact ⟨privateProbeId B (s,t,slot),g₀,j,peer,(privateSheet_at B _ (s,t,slot)).trans digit⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
