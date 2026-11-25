import OAI.Computability.BorderVNP.DiagonalSignedOpaquePointerRange
import OAI.Computability.BorderVNP.CubeRouteDataLayouts
import OAI.Computability.BorderVNP.DiagonalSignedOpaqueReportRetention

/-! # The signed source operand after a real native report on the selected packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.SignedFields

open Crossing Packing Packing.Inherited CellSparse Packet CellAddresses CellAddressPhysical
open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork RoutingISA

variable {σ Orig Port : Type} [Fintype σ] [Fintype Port]
    {s m n d k w entries D : ℕ} {bits : Port → ℕ} (a : SignedTaskArena.Layout)
    (F : Fields s m n a.cube.cells d k w σ) (boxes : Fin s → List (Source.Box Orig)) (entry : Fin entries → Fin s)
    (N : Network D Port bits) (cell : N.Site → Fin a.cube.cells) (state : N.Site → Site)
    (sites : N.Site ↪ Fin s) (edge : N.Edge ↪ Fin m) (port : Port ↪ Fin n)
    (x : σ → Bool) (physical : Represents N cell (fun v => (state v).size) sites edge port F x)
    (sizeFit : ∀ c, guessedSize N cell c+siteSize N cell c (fun v => (state v).size)+suppliedSize N cell c<2^w)
    (host : Fin entries → N.Site) (hosts : ∀ i, entry i=sites (host i))
    (old : ℕ → ℕ) (owners : ∀ i, old i.val=(cell (host i)).val)

open VPVNP.BurstRAM RoutingISA.Evaluator DiagonalTallyCellReports CellSparse.Packet.Source

include physical sizeFit hosts owners in
/-- The emitted original-site operand still points to the verifier body after
a complete native signed report. The selected quadratic gap absorbs every
charged report in this cell and every other cell uses its own stride. -/
theorem returned_pointer_body {order desc gadgets digits : ℕ} (hn : 1≤order)
    (wordFit : a.cube.stop < 2^w)
    (capacity : ∀ c, suppliedSize N cell c+order^2+
      (∑ j : Fin entries, if cell (host j)=c then desc else 0) ≤ a.cube.cellStride)
    (i : Fin entries) {frameBase ctl : ℕ} {axis : Fin (a.cube.n+1)}
    {l : ReportLayout} {reports : List (ReportCell l)} {q : ReportCursor} {mount : ℕ}
    {mem : Memory w} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : RoutingISA.Bank w}
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter frameBase ctl axis) l reports q)
    (seed : PreparedReportInput pub mem reports q mount) (r : Returns prepareCellReports pub mac reg mem)
    (tails : ∀ row∈reports, row.number=(cell (host i)).val → row.supplied=suppliedSize N cell (cell (host i)) ∧
      row.supplied+row.tailWidth≤TeamScales.width order (1/4))
    (hdr : ℕ) (fs : List Factor) :
    let slot := value (fun j => (frame F boxes entry a.cube.cellBank a.cube.cellStride (order^2) desc gadgets digits).eval x (.inr i,j))
    Delivered (description:=desc) (readings mem) slot hdr fs →
      Delivered (description:=desc) (readings r.val.2.2) slot hdr fs := by
  intro slot arrived
  let c := cell (host i)
  let bank := (a.cube.cellWriter frameBase ctl axis).bank c.val
  let start := slot-bank
  have limits := pointer_report_gap a F boxes entry N cell state sites edge port x physical sizeFit host hosts old owners
    (order^2) desc gadgets digits wordFit capacity i
  have low (t : ℕ) (ht : t≤order^2) : bank+suppliedSize N cell c+t ≤ slot := by
    simpa only [bank,CellBanks.Layout.bank,CubeArena.Layout.cellWriter,Nat.mul_comm c.val a.cube.cellStride] using limits.1 t ht
  have top : slot+desc≤bank+a.cube.cellStride := by
    simpa only [bank,CellBanks.Layout.bank,CubeArena.Layout.cellWriter,Nat.mul_comm c.val a.cube.cellStride] using limits.2.1
  have baseWord := low 0 (Nat.zero_le _)
  have address : bank+start=slot := by dsimp only [start]; omega
  have quart : TeamScales.width order (1/4) ≤ order := Nat.floor_le_of_le (by
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1:ℝ) ≤ (order:ℝ)) (by norm_num : (1/4:ℝ)≤1))
  have budget : order≤order^2 := by nlinarith
  have reserved (row : ReportCell l) (member : row∈reports) (same : row.number=c.val) :
      row.supplied+row.tailWidth ≤ start := by
    obtain ⟨width,charge⟩ := tails row member same
    change row.supplied=suppliedSize N cell c at width
    have enough := low row.tailWidth (by omega)
    omega
  have read : Delivered (description:=desc) (readings mem) (bank+start) hdr fs := address ▸ arrived
  have save := returned_opaque alloc seed r c start hdr fs (by change start+desc≤a.cube.cellStride; omega) reserved read
  change Delivered (description:=desc) (readings r.val.2.2) (bank+start) hdr fs at save
  rwa [address] at save

end CellPacketGeometry.History.Native.SignedFields

end BorderVNP
end Computability
end OAI
