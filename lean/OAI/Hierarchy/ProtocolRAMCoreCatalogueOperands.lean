import OAI.Hierarchy.ProtocolRAMCoreCatalogueHeader
import OAI.Hierarchy.ProtocolRAMPurchaseCTShape
import OAI.Hierarchy.ProbeStageRegularization

namespace OAI
/-! # Native CT operands of a positive core catalogue row -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard PurchaseCT
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
variable {h W k R w K : ℕ} {S : PurchaseSampler}

def prefixRead (bits : ℕ) (address : Expr) : Expr := .lookup ⟨0,bits⟩ address
def pointed (base R bits : ℕ) (f : Fin 10) := prefixRead bits (field base R f)
def globalGroup (base R bits : ℕ) :=
  prefixRead bits (.op .add (field base R 6) (pointed base R bits 3))

theorem prefixRead_at (bits : ℕ) (address : Expr) (m : Memory w) (row : Word w) {a : ℕ}
    (atAddr : address.eval m row=(a:Word w)) (small : a<2^bits) (wide : 2^bits≤2^w) :
    (prefixRead bits address).eval m row=m a := by
  simp only [prefixRead,Expr.eval,Bank.read,atAddr,Bank.size,Fin.val_cast_of_lt (small.trans_le wide),
    Nat.mod_eq_of_lt small,Nat.zero_add]

/-- All three per-record CT fields, using the single public group encoding. -/
def Geometry (π : Equiv.Perm (Fin (2^h))) (m : Memory w) (d : ℕ) : Prop :=
  ∀ t : StageAt h d, (allocation t 0 0 0 0).CTLoaded (banks t) (advisedStage h d π t)
    (groupNumber t).toEmbedding m

/-- A native execution on permutation input produces this exact geometry while
preserving every word in the caller's higher-address immutable tapes. -/
theorem geometry_run {d : ℕ} (hd : 1≤ d) (π : Equiv.Perm (Fin (2^h)))
    (raw : Memory (Native.wordBits h d Native.copies))
    (input : ∀ r : Fin (2^h), raw r.val=((π r).val:Word _)) :
    let start := Native.inputTape h d _ raw
    let finish := Native.images h d start (rounds d)
    (Native.subdivisionProgram h d).Exec start finish (Native.subdivisionConstant d*2^h) ∧
      Geometry π finish d ∧ ∀a, Native.heapEnd h d Native.copies≤ a → finish a=raw a := by
  obtain ⟨run,_,_,frame,_⟩ := Native.execute_subdivision hd π raw input
  obtain ⟨_,done⟩ := Native.native_linear_run hd π raw input (Native.physical_ordinal hd π)
  exact ⟨run,fun t => resident_numbered π t 0 0 0 0 _ done,frame⟩

private theorem bank_cell (b : Bank) (m : Memory w) (i : ℕ) (room : i<2^w) (fits : i< b.size) :
    m (b.base+i)=b.read m (i:Word w) := by
  simp [Bank.read,Fin.val_cast_of_lt room,Nat.mod_eq_of_lt fits]

/- The arbitrary catalogue order only selects a format row. Runtime input is
read twice for the group, once from the occupied CT row and then from the
public local-to-global directory. -/
theorem operands (order : Fin R ≃ Edges S h (2^W) k) (base bits attempts groupStart M : ℕ)
    (groups : Fin K ≃ AllGroups h (2^W)) (π : Equiv.Perm (Fin (2^h))) (m : Memory w)
    (header : Header order base attempts groupStart M m) (geom : Geometry π m (2^W))
    (directory : ReportGroupROM.Resident groupStart groups groupNumber m)
    (rowsFit : R≤2^w) (tileFit : 2^h≤2^w) (wide : 2^bits≤2^w)
    (ctEnd : Native.heapEnd h (2^W) Native.copies≤2^bits)
    (groupEnd : groupStart+ReportGroupROM.words h (2^W)≤2^bits)
    (r : Fin R) (t : StageAt h (2^W)) (p : Fin (2^h)) (l : AdaptiveProbe.ColumnLayer k)
    (rowEq : order r=.inr ((p,t),l)) :
    let a := advisedStage h (2^W) π t
    (globalGroup base R bits).eval m (r.val:Word w)=((groups.symm ⟨t,a.group p⟩).val:Word w) ∧
      (pointed base R bits 4).eval m (r.val:Word w)=((a.input p).val:Word w) ∧
      (pointed base R bits 5).eval m (r.val:Word w)=((a.output p).val:Word w) ∧
      (field base R 7).eval m (r.val:Word w)=(sideTag k attempts l false:Word w) ∧
      (field base R 8).eval m (r.val:Word w)=(sideTag k attempts l true:Word w) := by
  let a := advisedStage h (2^W) π t
  let group := (groupNumber t (a.group p)).val
  have hd : 1≤2^W := Nat.two_pow_pos _
  have fields (f : Fin 10) := (header.read rowsFit f r).trans
    (congrArg (fun e => (recordWord attempts groupStart M e f:Word w)) rowEq)
  have addr (j : Fin 3) (f : Fin 10)
      (stored : (field base R f).eval m (r.val:Word w)=
        (((Native.stageBank h (2^W) (stageNumber t) j).base+p.val:ℕ):Word w)) :
      (pointed base R bits f).eval m (r.val:Word w)=
        (Native.stageBank h (2^W) (stageNumber t) j).read m (p.val:Word w) := by
    let b := Native.stageBank h (2^W) (stageNumber t) j
    have sz : b.size=2^h := by simp [b,Bank.size,Native.stageBank_bits]
    have inside : p.val< b.size := by rw [sz]; exact p.isLt
    have limit := (Native.stageBank_end h (2^W) (stageNumber t) j).trans ctEnd
    exact (prefixRead_at bits _ m _ stored ((Nat.add_lt_add_left inside b.base).trans_le limit) wide).trans
      (bank_cell b m p.val (p.isLt.trans_le tileFit) inside)
  have groupRead : (pointed base R bits 3).eval m (r.val:Word w)=(group:Word w) :=
    (addr 0 3 (fields 3)).trans ((geom t).group p)
  let b := ReportGroupROM.bank groupStart h (2^W) t
  have grSmall : group< b.size := (groupNumber t (a.group p)).isLt.trans_le (ReportGroupROM.size t hd)
  have grBound := Nat.mul_le_mul_right (ReportGroupROM.stride h (2^W)) t.isLt
  rw [Nat.succ_mul] at grBound
  have grAddr : b.base+group<2^bits := by
    change group< ReportGroupROM.stride h (2^W) at grSmall
    change groupStart+t.val*ReportGroupROM.stride h (2^W)+group<2^bits
    unfold ReportGroupROM.words at groupEnd
    omega
  have baseRead : (field base R 6).eval m (r.val:Word w)=(b.base:Word w) := fields 6
  have physical : (globalGroup base R bits).eval m (r.val:Word w)=m (b.base+group) := by
    refine prefixRead_at bits _ _ _ ?_ grAddr wide
    simp only [Expr.eval,RowOp.opcode,BinaryOp.eval,baseRead,groupRead,Nat.cast_add]
  have groupWord : group<2^w := (Nat.lt_of_le_of_lt (Nat.le_add_left group b.base) grAddr).trans_le wide
  refine ⟨physical.trans ((bank_cell b m group groupWord grSmall).trans (directory t (a.group p))),
    (addr 1 4 (fields 4)).trans ((geom t).input p),
    (addr 2 5 (fields 5)).trans ((geom t).output p), fields 7, fields 8⟩

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
