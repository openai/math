import OAI.Hierarchy.DescentIssuedHostRoster
import OAI.Hierarchy.DescentStageVenuePeers

namespace OAI
/-! # Recovering the terminal Book neighbor fields from the reached venue port bank -/
namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentSortedRoster DescentGroupPeerOrder DescentColonies.DynamicSplit
open DescentPacking.PackedMatch.Local.Stage DescentPackedColony DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d k:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits}
  {G:PoweredGadget F} {q ε:ℝ} {S:AtomSchedule} {age grain D wire hist H w:ℕ}
  (r:Reached W G q ε S k age grain D wire hist) (wide:Fintype.card r.V≤H)
local notation "hosts_" => r.vertex.trans (Fin.castLEEmb wide)
local notation "order_" => (hosts_).trans Fin.valEmbedding

def terminalRoster (h:Fin H) (j:Fin r.placement.degree):Option (Fin H):=
  hostRotor hosts_ (hostRoster r.placement order_) h j

theorem terminal_roster_near (v:r.V):
    present (r.terminalRoster wide) (hosts_ v)=(r.placement.near v).map hosts_:=by
  apply Finset.ext
  intro z
  simp only [present, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  exact Chronology.original_hostRotor_rows r.placement hosts_ v z

theorem terminal_roster_indexed :
    indexed (r.terminalRoster wide)=r.terminalRoster wide:=by
  apply issued_roster r.placement hosts_ (r.terminalRoster wide)
  intro i j
  have same : j ∈ (List.ofFn (r.terminalRoster wide i)).filterMap id ↔ j ∈ present (r.terminalRoster wide) i := by
    simp only [present, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_filterMap, List.mem_ofFn, id_eq]
    constructor
    · rintro ⟨a, ⟨t, ht⟩, ha⟩
      exact ⟨t, ht.trans ha⟩
    · rintro ⟨t, ht⟩
      exact ⟨some j, ⟨t, ht⟩, rfl⟩
  rw [same]
  by_cases real:∃v,hosts_ v=i
  · obtain ⟨v,rfl⟩:=real
    rw [r.terminal_roster_near wide v,Finset.mem_map]
    constructor
    · rintro ⟨u,hit,rfl⟩
      exact ⟨v,u,rfl,rfl,(r.placement.symmetric v u).mp hit⟩
    · rintro ⟨v',u,ev,eu,hit⟩
      have eqv:v=v':=(hosts_).injective ev
      subst v'
      exact ⟨u,(r.placement.symmetric v u).mpr hit,eu.symm⟩
  · have none (t:Fin r.placement.degree):r.terminalRoster wide i t=none:=by
      unfold terminalRoster hostRotor
      rw [dite_eq_right real]
    simp only [present,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨t,yes⟩
      rw [none t] at yes
      contradiction
    · rintro ⟨v,u,ev,_,_⟩
      exact (real ⟨v,ev.symm⟩).elim

/-- The mounted chronological port table also returns the absent-neighbor
sentinel, including on blank hosts and unused positions in the sorted row. -/
theorem terminal_roster_words (i:Dated.Operands) {lanes precision floor:ℕ} {m:Memory w}
    (observed:stageVenue r wide i lanes precision floor (r.venueRoster wide) m)
    (h:Fin H) (j:Fin r.placement.degree) :
    m (i.roster.base+(h.val*r.placement.degree+j.val))=
      (target (indexed (r.terminalRoster wide) h j):Word w):=by
  rw [r.terminal_roster_indexed wide]
  rw [← Nat.add_assoc]
  exact r.roster_read wide i observed h j

/-- The room and comparison order both come from the original dated bank. -/
theorem terminal_roster_reads (i:Dated.Operands) {lanes precision floor:ℕ} {m:Memory w}
    (observed:stageVenue r wide i lanes precision floor (r.venueRoster wide) m)
    (h:Fin H) (j:Fin r.placement.degree) (z:Fin H)
    (found:indexed (r.terminalRoster wide) h j=some z):
    i.roster.read m ((h.val*r.placement.degree+j.val:ℕ):Word w)=(z.val:Word w):=by
  have idx : h.val*r.placement.degree+j.val<H*r.placement.degree:=by
    simpa only [finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (h,j)).isLt
  have enough : H*r.placement.degree≤ i.roster.size:=by
    simpa only [r.branch, Dated.Operands.ports] using observed.1.rosterRoom
  have literal:=DescentPackedZip.bank_read i.roster m (idx.trans_le enough) observed.1.roster
  have value := r.terminal_roster_words wide i observed h j
  rw [found] at value
  exact literal.trans value

end
end Hierarchy.DescentSixParty.Reached

end OAI
