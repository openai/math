import OAI.Hierarchy.ProtocolRAMCatalystSinkUpper
import OAI.Hierarchy.ProtocolRAMCatalystTerminalLayout
import OAI.Hierarchy.ProtocolRAMCoreRouteDirectory
import OAI.Hierarchy.ProtocolRAMCatalystOwnerLedger
import OAI.Hierarchy.ProtocolRAMPaidWidthUpper

namespace OAI
/-! # Exact original terminal write extent on the dyadic physical banks -/
noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Calendar Calendar.CoreRoute ProbeStage CoreBoard
open scoped Classical Fin.CommRing
variable {w n count z W k : ℕ}

private theorem passes_above (ps : List Pass) (m : Memory w) (x : ℕ)
    (bound : ∀p∈ps,p.out+p.rows≤x) : result ps m x=m x := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    exact (ih (p.apply m) (fun y hy=>bound y (List.mem_cons_of_mem p hy))).trans
      (ProtocolRAMGeneratedWrite.frame_image p.out p.rows p.term m x (.inr (bound p List.mem_cons_self)))

/-- The extra source extent is the maximum actual width of the reused sparse
scratch tape. It is independent of the values being scattered. -/
def extent (bits : ℕ) (slices : List PaidWidths.Slice) :=
  max (28*2^bits) (source bits+2*(slices.map PaidWidths.Slice.count).sum)

theorem extent_le (bits : ℕ) (slices : List PaidWidths.Slice) :
    extent bits slices≤28*2^bits+2*(slices.map PaidWidths.Slice.count).sum := by
  unfold extent source
  omega

/-- The costed original repair scatters pay for both physical scratch
words per selected row, including rows that are clipped to the padding ID. -/
theorem scratch_le_paid_clock (bank : Bank) (edges : ℕ) (slices : List PaidWidths.Slice) :
    2*(slices.map PaidWidths.Slice.count).sum≤PaidWidths.clock bank edges slices := by
  have bound : 2*(slices.map PaidWidths.Slice.count).sum≤
      (slices.map (fun s=>7+s.count*(4*(RepairHistogram.pair (s.columns bank edges)).work+20))).sum := by
    induction slices with
    | nil => simp
    | cons s rest ih =>
      simp only [List.map_cons,List.sum_cons]
      have per:=Nat.mul_le_mul_left s.count (show 2≤4*(RepairHistogram.pair (s.columns bank edges)).work+20 by omega)
      omega
  rw [PaidWidths.clock_eq]
  omega

theorem extent_le_paid_clock (bits : ℕ) (bank : Bank) (edges : ℕ) (slices : List PaidWidths.Slice) :
    extent bits slices≤28*2^bits+PaidWidths.clock bank edges slices :=
  (extent_le bits slices).trans (Nat.add_le_add_left (scratch_le_paid_clock bank edges slices) _)

theorem settled_above (c : Mesh) (A : Arena) (cat : CatalogueRows.Board) (L : OwnerLedger)
    (stock : Bank) (stride start reserveAmount : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (S : PurchaseSampler) (attempts : ℕ) (p : Recipes) (g : Source)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin cat.rows)} {center : J→List (Fin cat.rows)}
    (enum : Fin (Fintype.card (Slots z (2^W) k))≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) (m : Memory w) (slices : List PaidWidths.Slice) (x : ℕ)
    (ledger : L.arena=ownerArea (pageBits c A stock stride cat.rows (Fintype.card (Slots z (2^W) k)) count n) stride)
    (rows : ∀e∈events c,L.rows e≤ stride) :
    let r:=Fintype.card (Slots z (2^W) k)
    let bits:=pageBits c A stock stride cat.rows r count n
    let b:=settlement bits stock
    let a:=reserve start n bits
    let sink:=cat.sink r b (source bits) (table bits) (destination bits) (sinkBank start n r cat.rows)
    let owner:=result (L.scans c count) (PaidWidths.output b.width cat.rows (source bits) slices m)
    let archive:=result (Calendar.CoreRoute.stages b p g S z W k attempts) owner
    extent bits slices≤x → PaidWidths.Mounted b.width cat.rows (source bits) slices m →
      sink.output (ReserveUse.output a b reserveAmount site debit archive) enum ci cj x=m x := by
  intro r bits b a sink owner archive high mounted
  let B:=2^bits
  have cap : footprint c A stock stride cat.rows r count n<B := Nat.lt_log2_self
  unfold footprint at cap
  have top : 28*B≤x := (le_max_left ..).trans high
  have sparse : source bits+2*(slices.map PaidWidths.Slice.count).sum≤x := (le_max_right ..).trans high
  have width : b.width.base+cat.rows<x := by change 1*B+cat.rows<x; omega
  have out:=sink.above (ReserveUse.output a b reserveAmount site debit archive) enum ci cj x
    width.le (by change 9*B+2*r≤x; omega) (by change 10*B+8*cat.rows≤x; omega)
    (by change 18*B+9*cat.rows≤x; omega)
  rw [out]
  rw [ReserveUse.frame a b reserveAmount site debit archive x (.inr (by change 6*B+count≤x; omega))
    (.inr (by change 7*B+count≤x; omega)) (.inr (by change 8*B+2*n≤x; omega))]
  have route : archive x=owner x := by
    apply passes_above
    intro pass h
    simp only [Calendar.CoreRoute.stages,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl
    · change 4*B+2*r≤x
      omega
    · change 5*B+2*r≤x
      omega
  rw [route]
  have ledgerEnd : L.arena.endAddress c≤x := by
    rw [ledger]
    change 2*B+(events c).length*stride≤x
    omega
  have kept : owner x=PaidWidths.output b.width cat.rows (source bits) slices m x := by
    apply passes_above
    intro step h
    obtain ⟨e,date,rfl⟩:=List.mem_map.mp h
    have limit:=L.arena.within c e date
    have capRows:=rows e date
    have eqSize : L.arena.stride=stride:=congrArg Arena.stride ledger
    change L.arena.base c e+L.rows e≤x
    omega
  rw [kept]
  apply PaidWidths.output_above _ _ _ _ _ _ (fun s hs=>(mounted s hs).1) width
  intro s hs
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left 2
    (List.le_sum_of_mem (List.mem_map.mpr ⟨s,hs,rfl⟩))) _).trans sparse

end Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
end

end OAI
