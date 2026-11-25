import OAI.Hierarchy.DescentReachedCountPageLayout
import OAI.Hierarchy.DescentScalarRoleCounts
import OAI.Hierarchy.DescentPackedColumnHardware
import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! Snapshots of the dated atom populations and their sorted donor count vector. -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedColony DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

namespace Layout
variable (L : Layout)

def pages (i : Fin (L.donors*2)) : ROM.Page :=
  let j : Fin L.donors × Fin 2 := finProdFinEquiv.symm i
  ROM.binary (Gather.setField (d:=L.bits) (j.1 : Fin L.donors)) L.lanes j.2

def table (j : Fin L.donors) := ROM.joined L.pages L.romBits L.romBase (fun s=>finProdFinEquiv (j,s))

theorem page_eq (j : Fin L.donors) (s : Fin 2) :
    L.pages (finProdFinEquiv (j,s))=ROM.binary (Gather.setField (d:=L.bits) j) L.lanes s := by
  simp [pages]

theorem page_bound (p : Fin (L.donors*2)) : (L.pages p).bits≤L.romBits := by
  obtain ⟨⟨j,s⟩,rfl⟩:=finProdFinEquiv.surjective p
  rw [L.page_eq]
  fin_cases s
  · exact Nat.mul_le_mul_right L.lanes (Nat.le_add_right ..)
  · exact le_rfl

def copies (operand : ℕ→Expr) := DescentPackedFlowBatch.passes L.base L.rows L.span operand 0 L.blocks
def gather (P : Ports L.paths) := Gather.assembly L.table (direct P L.book L.hosts)
def program (w : ℕ) (P : Ports L.paths) (operand : ℕ→Expr) :=
  ((ProtocolRAM.program w (L.copies operand)).seq (ROM.mount L.pages L.romBits w L.romBase)).seq
    (scan w L.outBase L.rows (L.gather P))
def ticks (P : Ports L.paths) (operand : ℕ→Expr) :=
  (ProtocolRAM.clock (L.copies operand)+(4+10*L.tableWords))+(4+L.rows*(2*(L.gather P).work+4))
def snap {w} (operand : ℕ→Expr) (m : Memory w) := ProtocolRAM.result (L.copies operand) m
def installed {w} (operand : ℕ→Expr) (m : Memory w) := ROM.after L.pages L.romBits L.romBase (L.snap operand m)
def output {w} (P : Ports L.paths) (operand : ℕ→Expr) (m : Memory w) :=
  image L.outBase L.rows (L.gather P) (L.installed operand m)

theorem span_room : L.rows≤L.span := Nat.le_pow_clog (by decide) _
theorem result_fits {w floor} (room : L.roof<2^w) (after_ : L.roof≤floor) : L.result.Fits w floor :=
  ⟨Nat.two_pow_pos _,(Nat.le_add_left L.span _).trans_lt room,after_⟩
theorem expr_fits {w floor} (room : L.roof<2^w) (after_ : L.roof≤floor) : L.expr.Fits w floor :=
  ⟨L.result_fits room after_,trivial⟩

theorem gather_work (P : Ports L.paths) : (L.gather P).work ≤ 1+L.donors*(45+11) := by
  have each (j : Fin L.donors) : (direct P L.book L.hosts j).work≤45 := by
    simp only [direct,peerExpr,neighborID,Expr.work]; decide
  have bound (xs : List (Fin L.donors)) :
      (Gather.collect L.table (direct P L.book L.hosts) xs).work ≤ 1+xs.length*(45+11) := by
    induction xs with
    | nil=>rfl
    | cons i xs ih=>
      have head:=each i
      simp only [Gather.collect,Tables.read,Expr.work,List.length_cons,Nat.succ_mul]
      omega
  simpa only [gather,Gather.assembly,List.length_finRange] using bound (List.finRange L.donors)

end Layout
end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts

end OAI
