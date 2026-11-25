import OAI.Hierarchy.ProtocolRAMCatalogueMount
import OAI.Hierarchy.ProtocolRAMCatalogueAlignment
import OAI.Hierarchy.ProtocolRAMCatalogueRows
import OAI.Hierarchy.ProtocolRAMPaidWidthCore
import OAI.Hierarchy.ProtocolRAMReserveUse

namespace OAI
/-! # The permanent and purchased edges of the physical catalogue -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.ReportSockets CoreBoard AdaptiveProbe ProtocolRAMEmit
open scoped Classical Fin.CommRing

variable {w h W k K attempts : ℕ} {S : PurchaseSampler}

variable {b : Board} {π : Equiv.Perm (Fin (2^h))} {depth M : ℕ} {marks : Marks h W k attempts}
  {rows : Fin b.rows→Row} {fixed : Fin b.rows→ℕ} {order : Fin b.coreRows≃Edges S h (2^W) k}
  {acquired : Bought S π depth marks→Fin b.boughtRows}

/-- A positive core row in the acquired-catalogue alignment has exactly its
original permanent identifier, including duplicate endpoint pairs. -/
theorem Alignment.core_name
    (proof : Alignment b S π depth marks M rows fixed (b.original S π depth marks order acquired))
    (i : {i : Fin b.rows // 0<fixed i}) (j : Fin b.coreRows) (hit : b.coreIndex j=i.val) :
    proof.ident i=.inl (order j) := by
  have eq:=(proof.original i).trans hit.symm
  cases id : proof.ident i with
  | inl e =>
    have atRow : b.coreIndex (order.symm e)=b.coreIndex j := by
      simpa only [id,Board.original,Sum.elim_inl] using eq
    have val : order.symm e=j := Fin.ext (congrArg (fun i : Fin b.rows => i.val) atRow)
    exact congrArg Sum.inl ((order.apply_symm_apply e).symm.trans (congrArg order val))
  | inr e =>
    have atRow : b.boughtIndex (acquired e)=b.coreIndex j := by
      simpa only [id,Board.original,Sum.elim_inr] using eq
    have val : b.coreRows+(acquired e).val=j.val := congrArg (fun i : Fin b.rows => i.val) atRow
    omega

/-- The genuinely reported endpoints of every positive terminal row coincide
with the graph's endpoints up to reversing that row. -/
theorem Alignment.coreMount_ends
    (proof : Alignment b S π depth marks M rows fixed (b.original S π depth marks order acquired))
    (place : Site h (2^W) k→Fin K) (m : Memory w)
    (read : ∀j : Fin b.boughtRows,Reads (rows (b.boughtIndex j)) (b.bought.view m (j.val:Word w))
      (b.idBase+(b.boughtIndex j).val))
    (i : {i : Fin b.rows // 0<fixed i}) :
    let A:=(b.coreMount π place order m).actual
    let left:=reportedSite place (rows i.val).endpoint
    let right:=reportedSite place (rows i.val).opposite
    (A.tail i.val=left ∧ A.head i.val=right) ∨ (A.tail i.val=right ∧ A.head i.val=left) := by
  intro A left right
  rcases b.split_index i.val with ⟨j,hit⟩|⟨j,hit⟩
  · have name:=proof.core_name i j hit
    have located:=proof.joins i
    dsimp only at located
    rw [name] at located
    rcases located with fwd|rev
    · left
      dsimp only [A,left,right]
      rw [←hit] at fwd ⊢
      constructor <;> simp only [Board.coreMount,Board.byKind_core,fwd.1,fwd.2,actualEnds,reportedSite_number]
    · right
      dsimp only [A,left,right]
      rw [←hit] at rev ⊢
      constructor <;> simp only [Board.coreMount,Board.byKind_core,rev.1,rev.2,actualEnds,reportedSite_number]
  · left
    dsimp only [A,left,right]
    rw [←hit]
    constructor <;> simp only [Board.coreMount,Board.byKind_bought,(read j).leftField,(read j).rightField]

/-- On the physical site numbering the decoded words are the output sites
used by the signed terminal matrix. -/
theorem Alignment.coreMount_sites
    (proof : Alignment b S π depth marks M rows fixed (b.original S π depth marks order acquired))
    (m : Memory w)
    (read : ∀j : Fin b.boughtRows,Reads (rows (b.boughtIndex j)) (b.bought.view m (j.val:Word w))
      (b.idBase+(b.boughtIndex j).val))
    (i : {i : Fin b.rows // 0<fixed i})
    (fits : (rows i.val).endpoint≤ siteLast h (2^W) k ∧ (rows i.val).opposite≤ siteLast h (2^W) k) :
    let A:=(b.coreMount π (siteNumber h (2^W) k) order m).actual
    (A.tail i.val=(rows i.val).leftSite fits ∧ A.head i.val=(rows i.val).rightSite fits) ∨
      (A.tail i.val=(rows i.val).rightSite fits ∧ A.head i.val=(rows i.val).leftSite fits) := by
  have left : reportedSite (siteNumber h (2^W) k) (rows i.val).endpoint=(rows i.val).leftSite fits := by
    simp only [reportedSite,dite_eq_left (Nat.lt_succ_of_le fits.1),Equiv.apply_symm_apply,Row.leftSite]
  have right : reportedSite (siteNumber h (2^W) k) (rows i.val).opposite=(rows i.val).rightSite fits := by
    simp only [reportedSite,dite_eq_left (Nat.lt_succ_of_le fits.2),Equiv.apply_symm_apply,Row.rightSite]
  simpa only [left,right] using proof.coreMount_ends (siteNumber h (2^W) k) m read i

/-- The geometric edge of the authentic catalogue name agrees with its
mounted edge even if the terminal row reversed the two sites. -/
theorem Alignment.coreMount_original
    (proof : Alignment b S π depth marks M rows fixed (b.original S π depth marks order acquired))
    (place : Site h (2^W) k→Fin K) (m : Memory w)
    (read : ∀j : Fin b.boughtRows,Reads (rows (b.boughtIndex j)) (b.bought.view m (j.val:Word w))
      (b.idBase+(b.boughtIndex j).val))
    (i : {i : Fin b.rows // 0<fixed i}) :
    let A:=(b.coreMount π place order m).actual
    let endpoints:=actualEnds S π depth marks (proof.ident i)
    (A.tail i.val=place endpoints.1 ∧ A.head i.val=place endpoints.2) ∨
      (A.tail i.val=place endpoints.2 ∧ A.head i.val=place endpoints.1) := by
  have observed:=proof.coreMount_ends place m read i
  dsimp only at observed
  rcases proof.joins i with fwd|rev
  · simpa only [fwd.1,fwd.2,reportedSite_number] using observed
  · simpa only [rev.1,rev.2,reportedSite_number] using observed.symm

/-- Specialization to the genuine terminal scanner. The acquired rows come
from both native endpoint reads of the paid catalogue's own bought branch. -/
theorem Alignment.terminal_coreMount_sites {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}
    {core : I→List (Fin b.rows)} {center : J→List (Fin b.rows)}
    (banks : RouteSettlement.Banks) (source table destination : ℕ) (owners : Bank) (m : Memory w)
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (proof : Alignment b S π depth marks M
      ((b.sink r banks source table destination owners).terminalRows m enum ci cj)
      fixed (b.original S π depth marks order acquired))
    (room : b.idBase+b.rows<2^w) (wide : 1<2^w)
    (reads : ∀f : Fin 7,f≠4→(b.geometry f).Fits w banks.width.base) (space : banks.width.base+b.rows≤ source)
    (i : {i : Fin b.rows // 0<fixed i}) :
    let row:=(b.sink r banks source table destination owners).terminalRows m enum ci cj i.val
    ∀fits : row.endpoint≤ siteLast h (2^W) k ∧ row.opposite≤ siteLast h (2^W) k,
    let A:=(b.coreMount π (siteNumber h (2^W) k) order m).actual
    (A.tail i.val=row.leftSite fits ∧ A.head i.val=row.rightSite fits) ∨
      (A.tail i.val=row.rightSite fits ∧ A.head i.val=row.leftSite fits) :=
  fun fits=>proof.coreMount_sites m
    (fun j=>b.bought_reads banks source table destination owners m enum ci cj j room wide reads space) i fits

/-- The terminal serializer reads its six static words at checkout even
after the width, route and reserve scans have filled their own windows. -/
theorem Board.bought_reads_checkout (b : Board) {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}
    {core : I→List (Fin b.rows)} {center : J→List (Fin b.rows)}
    (banks : RouteSettlement.Banks) (src table dst : ℕ) (owners : Bank) (checkout closing : Memory w)
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (i : Fin b.boughtRows) (room : b.idBase+b.rows<2^w) (wide : 1<2^w)
    (reads : ∀f : Fin 7,f≠4→(b.geometry f).Fits w banks.width.base)
    (space : banks.width.base+b.rows≤ src) {cut : ℕ}
    (geo : ∀f : Fin 7,f≠4→(b.geometry f).Fits w cut) (retained : ∀x,x<cut→closing x=checkout x) :
    Reads ((b.sink r banks src table dst owners).terminalRows closing enum ci cj (b.boughtIndex i))
      (b.bought.view checkout (i.val:Word w)) (b.idBase+(b.boughtIndex i).val) := by
  apply Reads.of_fields
  intro f hf
  have seen := (b.sink r banks src table dst owners).terminal_field closing enum ci cj (b.boughtIndex i) f hf
    (reads f hf) space
  have same:=eval_below (b.geometry f) ((b.boughtIndex i).val:Word w) checkout closing (geo f hf) retained
  exact seen.trans ((congrArg Fin.val same).trans (b.bought_read checkout i room wide f))

/-- The permanent socket descriptor has the same six checkout words at terminal reporting. -/
theorem Board.core_reads_checkout (b : Board) {I J : Type*} [Fintype I] [Fintype J] {r : ℕ}
    {core : I→List (Fin b.rows)} {center : J→List (Fin b.rows)}
    (banks : RouteSettlement.Banks) (src table dst : ℕ) (owners : Bank) (checkout closing : Memory w)
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (i : Fin b.coreRows) (room : b.idBase+b.rows<2^w)
    (reads : ∀f : Fin 7,f≠4→(b.geometry f).Fits w banks.width.base)
    (space : banks.width.base+b.rows≤ src) {cut : ℕ}
    (geo : ∀f : Fin 7,f≠4→(b.geometry f).Fits w cut) (retained : ∀x,x<cut→closing x=checkout x) :
    Reads ((b.sink r banks src table dst owners).terminalRows closing enum ci cj (b.coreIndex i))
      (b.core.view checkout (i.val:Word w)) (b.idBase+(b.coreIndex i).val) := by
  apply Reads.of_fields
  intro f hf
  have seen := (b.sink r banks src table dst owners).terminal_field closing enum ci cj (b.coreIndex i) f hf
    (reads f hf) space
  have same:=eval_below (b.geometry f) ((b.coreIndex i).val:Word w) checkout closing (geo f hf) retained
  exact seen.trans ((congrArg Fin.val same).trans (b.core_read checkout i room f))

/-- The actual terminal scan sequence preserves the geometry input window
below each of its four kinds of outputs. -/
theorem checkout_frame (banks : RouteSettlement.Banks) (edges src : ℕ) (slices : List PaidWidths.Slice)
    (ownerScans routes : List Pass) (a : ReserveUse.Archive) (reserve : ℕ) {n count : ℕ}
    (site : Fin n→Fin count) (debit : Fin n→ℕ) (checkout : Memory w) (cut : ℕ)
    (fits : ∀u∈slices,u.Fits banks.width edges src w) (width : cut≤banks.width.base)
    (old : ∀p∈ownerScans,cut≤p.out) (route : ∀p∈routes,cut≤p.out)
    (res : cut≤banks.reserved.base) (used : cut≤banks.used.base) (scratch : cut≤a.scratch) :
    let data:=PaidWidths.output banks.width edges src slices checkout
    let closing:=ReserveUse.output a banks reserve site debit (result routes (result ownerScans data))
    ∀x,x<cut→closing x=checkout x := by
  intro data closing x hx
  exact (ReserveUse.frame _ _ _ _ _ _ x (.inl (hx.trans_le res)) (.inl (hx.trans_le used))
    (.inl (hx.trans_le scratch))).trans ((result_below routes _ x (fun p hp=>hx.trans_le (route p hp))).trans
    ((result_below ownerScans _ x (fun p hp=>hx.trans_le (old p hp))).trans
    (PaidWidths.frame _ _ _ _ _ x fits (hx.trans_le width))))

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
