import OAI.Hierarchy.DescentIssuedNativeReset
import OAI.Hierarchy.DescentPackedCensusInvoice
import OAI.Hierarchy.DescentResetCutoffTable

namespace OAI
/-! # Paid field widths of the reset’s original measured data -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentGL DescentColonies DescentResetInvoice DescentBaseProfile
open DescentRotor DescentMixedRouter DescentFineTerminals StarKeys
open LinearAlgebra.SpectralBooks ThreeFlat
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k)
local notation "grain" => (A.z*G.b)
local notation "budget" => (A.wire*grain*A.cap)
local notation "pos" => (fun u => Prod.snd (A.pos u))
local notation "ix" => (StarKeys.filled W.graph A.pos A.block digits)

include ready in
/-- Works even for a host pair absent from the reported rectangle. -/
theorem reset_words_at (v u : V) (x : Block m) : A.resetFlow digits v u x≤A.resetLoad digits v x ∧
    A.resetLoad digits v x≤budget := by
  let raw:=W.countWorld A.grainCount
  let load:=W.siteUnits (fun v=>A.hub (A.pos v).2) A.records A.wire 256 A.hist
  have inc : (∑ z ∈ ({u} : Finset V), A.resetFlow digits v z x) ≤ A.resetLoad digits v x :=
    pairLoad_le raw pos ix (A.wire*grain) (A.hub ∘ pos) A.records 256 A.hist
      (by decide) (fun _ => ({u} : Finset V)) v x
  have score:=filled_mass W.graph A.pos A.block digits load v x
  refine ⟨by simpa only [Finset.sum_singleton] using inc,?_⟩
  exact (W.mass_of_counts A.grainCount grain (A.grainCount_fit S ready) pos ix (fun z=>A.hub (pos z))
    A.records A.wire 256 A.hist v x).le.trans (score.le.trans (A.small _ _))

theorem mutual_reset_flow (v u : V) (x : Block m) : A.resetFlow digits v u x=A.resetFlow digits u v x := by
  have edges (e : W.graph.Edge):=filled_edges W.graph A.pos A.block digits A.near (fun e=>(A.peers e).1) A.same e
  exact pairLoad_symm (W.countWorld A.grainCount) pos ix (A.wire*grain) (fun e _=>(edges e).1) v u x

include ready in
theorem reset_word_bits {p : ℕ} (height : 0<S.height) (age : i≤S.length) (grainAt : A.z=S.grainAt G.b p i)
    (wire : A.wire=S.epochPower^S.priceExponent) (base : G.b≤2^S.capGain) :
    (∀v x,A.resetLoad digits v x<2^(S.censusBits p)) ∧
    (∀v u x,A.resetFlow digits v u x<2^(S.censusBits p)) ∧
    ∀v u,(∑x,A.resetFlow digits v u x)<2^(m+S.censusBits p) := by
  have top:=(A.census_caps S ready height age grainAt wire base).2
  have rd:=A.reset_words_at S ready digits
  have point (v u x) : A.resetFlow digits v u x<2^(S.censusBits p):=(rd v u x).1.trans_lt ((rd v u x).2.trans_lt top)
  exact ⟨fun v x=>(rd v v x).2.trans_lt top,point,fun v u=>DescentPlainTerminal.Suffix.Cutoff.total_fits _ (point v u)⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
