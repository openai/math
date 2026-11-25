import OAI.Hierarchy.ProtocolRAMCatalystArchiveRun
import OAI.Hierarchy.ProtocolRAMCatalystArchiveSpace
import OAI.Hierarchy.ProtocolRAMCoreRouteCost
import OAI.Hierarchy.ProtocolRAMCoreCatalogueBudget

namespace OAI
/-! # Extra CPU text and native time for chronological owners and the actual route-index columns -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar CoreRoute Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical
variable {z W k attempts w q goods edges : ℕ} {S : PurchaseSampler}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "slots" => Fintype.card (Slots z D k)

/-- Padded owner rows affect the loop extent, while a closed row expression
contributes to the CPU text just once for each calendared event. -/
theorem OwnerLedger.text_bound (L : OwnerLedger) (c : Mesh) (count cost : ℕ)
    (bound : ∀e∈events c,(clamp count (L.term e)).work≤ cost) :
    listText (L.scans c count) ≤ 15+(events c).length*(11+4*cost) := by
  have estimate (ps : List Pass) (cheap : ∀p∈ps,p.term.work≤ cost) :
      (ps.map (fun p=>rowText p.term)).sum≤ps.length*(11+4*cost) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hp:=cheap p (by simp)
      have hps:=ih (fun t ht=>cheap t (List.mem_cons_of_mem p ht))
      change rowText p.term + (ps.map (fun t=>rowText t.term)).sum ≤
        (ps.length+1)*(11+4*cost)
      calc
        _ ≤ (11+4*cost)+ps.length*(11+4*cost) :=
          Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hp) 11) hps
        _ = _ := (Nat.add_comm ..).trans (Nat.succ_mul ..).symm
  apply Nat.add_le_add_left
  simpa only [OwnerLedger.scans,List.length_map] using estimate (L.scans c count) (by
    intro p hp
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hp
    exact bound e he)

theorem terminal_text_bound (C : Chart w q goods) (L : OwnerLedger) (p : Recipes) (x : Source)
    (flag : ℕ) (s : Sink slots edges) (src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive)
    (count n reserve : ℕ) :
    Native.text (terminal C L (CoreRoute.stages s.banks p x S z W k attempts) flag s src ss a count n reserve) ≤
      Native.text (paidReporter C flag s src ss a count n reserve)+listText (L.scans C.mesh count)+
        (65+4*operationBound N k attempts) := by
  have length:=CoreRoute.text_bound (S:=S) (z:=z) (W:=W) (k:=k) (attempts:=attempts) (w:=w) p x s.banks
  rw [text_passes] at length
  rw [terminal_text]
  exact Nat.add_le_add_left length _

theorem terminal_clock_eq (C : Chart w q goods) (L : OwnerLedger) (routes : List Pass)
    {r : ℕ} (s : Sink r edges) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    terminalTime C L routes s ss a count n reserve =
      paidReporterTime C s ss a count n reserve + clock (L.scans C.mesh count)+clock routes := by
  dsimp only [terminalTime,paidReporterTime]
  omega

def slotFactor (d k : ℕ) :=
  let f:=18*(d-1)+1
  (1+(f*(k*2)))*(2*f+2)+2*resourceFactor d k

/-- The native route passes enumerate all fixed ordinary and center positions.
Their padded lengths and their CPU text are independent of the permutation. -/
theorem slot_count (z d k : ℕ) (hd : 1≤d) : Fintype.card (Slots z d k)≤ slotFactor d k*2^z := by
  let f:=Stages z d
  let units:=Commodity (Fin (2^z)) f k
  let widths : units→ℕ:=Sum.elim (fun _=>2*f+1) (fun _=>2)
  have arity : Fintype.card units=(1+f*(k*2))*2^z := by
    dsimp only [units,Commodity]
    rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_prod,Fintype.card_prod]
    simp only [Fintype.card_fin,Fintype.card_bool]
    ring
  have counts : (∑ i : units,widths i)≤Fintype.card units*(2*f+2) := by
    calc
      _ ≤ ∑ _i : units, (2*f+2) := by
        apply Finset.sum_le_sum
        intro i _
        cases i <;> dsimp only [widths,Sum.elim_inl,Sum.elim_inr] <;> omega
      _ = _ := by simp
  have exactCount : Fintype.card (Slots z d k) =
      (∑i : units,widths i)+ (Fintype.card (Columns z d)*k)*2 := by
    change Fintype.card ((Σi : units,Fin (widths i)) ⊕ (Σ_ : Columns z d × Fin k,Fin 2))=_
    simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Fintype.card_prod]
  have paid:=physical_resources z d k hd
  have phase : f=18*(d-1)+1 := CoreCatalogue.total_stages z d
  rw [exactCount]
  apply (Nat.add_le_add counts (Nat.mul_le_mul_right 2 paid)).trans
  rw [arity]
  dsimp only [slotFactor]
  rw [←phase]
  exact (by ring : ((1+f*(k*2))*2^z)*(2*f+2)+(resourceFactor d k*2^z)*2 =
    ((1+f*(k*2))*(2*f+2)+2*resourceFactor d k)*2^z).le

/-- With a fixed owner expression and fixed physical width factor, the complete
extra calendar has an explicit linear-time coefficient. -/
theorem terminal_clock_growth (C : Chart w q goods) (L : OwnerLedger) (p : Recipes) (x : Source)
    (s : Sink slots edges) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive)
    (count n reserve rowFactor expression : ℕ)
    (bound : ∀e∈events C.mesh,L.rows e≤ rowFactor*2^z ∧ (clamp count (L.term e)).work≤expression) :
    let op:=operationBound (18*(D-1)+1) k attempts
    let factor:=16+fuel C.mesh*(4+rowFactor*(2*expression+4))+2*slotFactor D k*(22+2*op)
    terminalTime C L (CoreRoute.stages s.banks p x S z W k attempts) s ss a count n reserve ≤
      paidReporterTime C s ss a count n reserve+factor*2^z := by
  intro op factor
  have phase : N=18*(D-1)+1:=CoreCatalogue.total_stages z D
  have owner:=L.time_bound C.mesh count (rowFactor*2^z) expression bound
  have eventsEq : (events C.mesh).length=fuel C.mesh:=event_count C.mesh
  rw [eventsEq] at owner
  have routes:=CoreRoute.clock_bound (S:=S) (z:=z) (W:=W) (k:=k) (attempts:=attempts) p x s.banks
  have price : operationBound N k attempts=op :=
    congrArg (fun n=>operationBound n k attempts) phase
  rw [price] at routes
  have physical:=slot_count z D k (Nat.two_pow_pos _)
  have head : 16≤16*2^z := by simpa using Nat.mul_le_mul_left 16 (Nat.two_pow_pos z)
  have four : 4≤4*2^z := by simpa using Nat.mul_le_mul_left 4 (Nat.two_pow_pos z)
  have slotRoom:=Nat.mul_le_mul_right (22+2*op) (Nat.mul_le_mul_left 2 physical)
  have extra:=Nat.mul_le_mul_left (fuel C.mesh)
    (Nat.add_le_add_right four ((rowFactor*2^z)*(2*expression+4)))
  change _≤12+(2*slots)*(22+2*op) at routes
  rw [terminal_clock_eq]
  apply Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left owner _) routes)
  dsimp only [factor]
  nlinarith only [head,extra,slotRoom]

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
