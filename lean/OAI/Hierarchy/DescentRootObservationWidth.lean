import OAI.Hierarchy.DescentFundedRootObservation

namespace OAI
/-! # Reading the saved fallback packet at the public operand width -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentStageEdgeReceipt DescentFallbackShapeTable DescentRosterOrder DescentResetHostSize
open DescentPackedLeafSelector DescentPlainTerminal DescentPlainTerminal.Suffix DescentFallbackRankRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field slots : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ) (groups : J↪ℕ) (vertex : V↪Fin H)
variable {zz ww : ℕ} {ct : W.graph.Edge→ℕ} {cut : ∀e,W.graph.width e=ct e*(zz*G.b)}
    (Z : ResetInput (W.granular ct (zz*G.b) cut) (q*ww) ε h C Ht) (T : Z.Terminals)
    (frm : Z.SourceFrame T (fun u=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
local notation "Y" => 2^Z.n
local notation "L" => 2^(m-c)
local notation "D" => 32*Nat.clog 2 (2*A.degree)
local notation "ids" => vertex.trans Fin.valEmbedding

variable {A S ready digits native groups vertex Z T frm} {large : ℕ}
namespace RootObservation
variable (o : RootObservation A S ready digits native groups vertex Z T frm field)

/-- Cast the original chronological edge enumeration while retaining the measured memory. -/
def reorder {other : W.graph.Edge↪ℕ} (same : native=other) :
    RootObservation A S ready digits other groups vertex Z T frm field :=
  {o with markRead:=fun v hi lo j=>by rw [←same];exact o.markRead v hi lo j}

def widen (width : field≤large) : RootObservation A S ready digits native groups vertex Z T frm large :=
  {o with
    wordFits:=fun u=>(o.wordFits u).trans_le (Nat.pow_le_pow_right (by decide) width)
    signedFits:=o.signedFits.trans width
    countFits:=o.countFits.trans width}

local notation "rank" => ranks (a:=r) («Y»:=Y) («D»:=A.degree) o.chart (2^Ht) (Ht+2) o.memory
local notation:max "rows" b:arg v:arg hi:arg => DescentFallbackPeriod.inputs (field:=b) o.stencil o.peers o.marks
  (fun u j=>(rank u j).val) (vertex v) hi

/-- A real host's roster reads real predecessor hosts. Each of the four kinds
of fallback input therefore preserves its integer value when widened. -/
theorem inputs_widen (width : field≤large) (v : V) (hi : Block c)
    (j : DescentFallbackPeriod.Input A.degree L A.cap Z.n r) :
    ((rows large v hi) j).val=((rows field v hi) j).val :=by
  have powers : 2^field≤2^large := Nat.pow_le_pow_right (by decide) width
  have stable (z : ℕ) (bound : z<2^field) : (z:Cell large).val=(z:Cell field).val :=
    (Fin.val_cast_of_lt (bound.trans_le powers)).trans (Fin.val_cast_of_lt bound).symm
  rcases j with (lo|⟨p,lo⟩)|(⟨lo,slot⟩|rankIndex)
  · apply stable
    rw [o.stencilRead]
    exact (Nat.lt_succ_self _).trans (o.wordFits _)
  · simp only [DescentFallbackPeriod.inputs, o.rosterRead]
    cases hostRoster A ids v p with
    | none => rfl
    | some u =>
      have fit : o.stencil (vertex u) hi lo + 1 < 2^field := by
        rw [o.stencilRead]
        exact o.wordFits _
      change ((o.stencil (vertex u) hi lo : Cell large) + 1).val =
        ((o.stencil (vertex u) hi lo : Cell field) + 1).val
      simpa only [Nat.cast_add, Nat.cast_one] using stable _ fit
  · exact stable _ ((DescentSignedCableCodec.encode _).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) o.signedFits))
  · exact stable _ ((rank (vertex v) rankIndex).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) o.countFits))

end RootObservation
end
end Hierarchy.DescentSixParty.GroupStage

end OAI
