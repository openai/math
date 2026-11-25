import OAI.Hierarchy.ProtocolRAMStaticPorts
import OAI.Hierarchy.TaggedWirePaidOperands
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # The two normalized fixed-slot base banks over the entire original paid-edge board -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Slot
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProbeStage.CoreBoard.HistoryRoles RoleProgram
open scoped Fin.CommRing

variable {w H : ℕ}

/-- In each acquired or retained row select the same socket used by the actual
sorted physical site labels and use its immutable slot as the port operand. -/
def ordered (L : RoleProgram.Chart) (b : Board) (core bought : Bool → Socket) (side : Bool) : Expr :=
  (normalized L (paidInputs b core bought) side).slot

def orientation (L : RoleProgram.Chart) (raw : Bool → Socket) (m : Memory w) (i : Word w) (side : Bool) :=
  if (socketSite L (raw false)).eval m i < (socketSite L (raw true)).eval m i then side else !side

theorem ordered_at (L : RoleProgram.Chart) (b : Board) (core bought : Bool → Socket)
    (m : Memory w) (i : Word w) (side : Bool) :
    (ordered L b core bought side).eval m i =
    let raw := paidInputs b core bought
    (raw (orientation L raw m i side)).slot.eval m i := by
  dsimp only
  unfold ordered normalized zipSocket sortedRead orientation
  by_cases lt : (socketSite L (paidInputs b core bought false)).eval m i <
      (socketSite L (paidInputs b core bought true)).eval m i <;>
    cases side <;> simp [Expr.eval,Comparison.test,lt]

theorem at_core (L : RoleProgram.Chart) (b : Board) (core bought : Bool → Socket)
    (m : Memory w) (i : Fin b.coreRows) (room : b.rows < 2^w) (side : Bool) :
    (ordered L b core bought side).eval m ((b.coreIndex i).val:Word w)=
      (core (orientation L (paidInputs b core bought) m (i.val:Word w) side)).slot.eval m (i.val:Word w) := by
  rw [ordered_at]
  exact b.select_core m _ _ i room

theorem at_bought (L : RoleProgram.Chart) (b : Board) (core bought : Bool → Socket)
    (m : Memory w) (i : Fin b.boughtRows) (room : b.rows < 2^w) (side : Bool) :
    (ordered L b core bought side).eval m ((b.boughtIndex i).val:Word w)=
      (bought (orientation L (paidInputs b core bought) m ((b.boughtIndex i).val:Word w) side)).slot.eval
        m (i.val:Word w) := by
  rw [ordered_at]
  exact b.select_bought m _ _ i room

def pair (w : ℕ) (L : RoleProgram.Chart) (b : Board) (out lanes : ℕ) (core bought : Bool → Socket) :=
  (ProtocolRAMStaticPorts.program w out b.rows lanes (ordered L b core bought false)).seq
    (ProtocolRAMStaticPorts.program w (out+b.rows) b.rows lanes (ordered L b core bought true))

def clock (L : RoleProgram.Chart) (b : Board) (lanes : ℕ) (core bought : Bool → Socket) :=
  ProtocolRAMStaticPorts.work b.rows lanes (ordered L b core bought false)+
    ProtocolRAMStaticPorts.work b.rows lanes (ordered L b core bought true)

def result (out lanes : ℕ) {n H : ℕ} (port : Bool → Fin n → Fin H) (m : Memory w) :=
  ProtocolRAMStaticPorts.image (out+n) lanes (port true) (ProtocolRAMStaticPorts.image out lanes (port false) m)

theorem read (out lanes : ℕ) {n : ℕ} (port : Bool → Fin n → Fin H) (m : Memory w)
    (side : Bool) (i : Fin n) :
    result out lanes port m (out+side.toNat*n+i.val)=(((port side i).val*lanes:ℕ):Word w) := by
  cases side
  · rw [show out+false.toNat*n+i.val=out+i.val by simp]
    unfold result
    rw [ProtocolRAMStaticPorts.frame _ _ _ _ _ (.inl (by have := i.isLt;omega))]
    exact ProtocolRAMStaticPorts.read _ _ _ _ _
  · rw [show out+true.toNat*n+i.val=out+n+i.val by simp]
    exact ProtocolRAMStaticPorts.read _ _ _ _ _

theorem frame (out lanes : ℕ) {n : ℕ} (port : Bool → Fin n → Fin H) (m : Memory w)
    (a : ℕ) (ha : a < out ∨ out+2*n ≤ a) : result out lanes port m a=m a :=
  (ProtocolRAMStaticPorts.frame _ _ _ _ a (by omega)).trans
    (ProtocolRAMStaticPorts.frame _ _ _ _ a (by omega))

/-- The two measured scans read exactly the normalized slot terms on immutable
input. Their actual writes occupy disjoint adjacent arrays indexed by the old row. -/
theorem run_fitted (L : RoleProgram.Chart) (b : Board) (out lanes : ℕ) (core bought : Bool → Socket)
    (port : Bool → Fin b.rows → Fin H) (m : Memory w)
    (safe : ∀side,(ordered L b core bought side).Fits w out) (room : out+2*b.rows < 2^w)
    (old : ∀(side : Bool) (i : Fin b.coreRows),(core (orientation L (paidInputs b core bought) m (i.val:Word w) side)).slot.eval m (i.val:Word w)=
      ((port side (b.coreIndex i)).val:Word w))
    (new : ∀(side : Bool) (i : Fin b.boughtRows),(bought (orientation L (paidInputs b core bought) m ((b.boughtIndex i).val:Word w) side)).slot.eval
      m (i.val:Word w)=((port side (b.boughtIndex i)).val:Word w)) :
    (pair w L b out lanes core bought).Exec m (result out lanes port m) (clock L b lanes core bought) := by
  have words : b.rows < 2^w := by omega
  have operand (side : Bool) (i : Fin b.rows) :
      (ordered L b core bought side).eval m (i.val:Word w)=((port side i).val:Word w) := by
    by_cases lo : i.val < b.coreRows
    · let j : Fin b.coreRows := ⟨i.val,lo⟩
      have eq : b.coreIndex j=i := Fin.ext rfl
      rw [←eq]
      exact (at_core L b core bought m j words side).trans (old side j)
    · have ht:=i.isLt
      unfold Board.rows at ht
      let j : Fin b.boughtRows := ⟨i.val-b.coreRows,by omega⟩
      have eq : b.boughtIndex j=i := Fin.ext (by change b.coreRows+(i.val-b.coreRows)=i.val;omega)
      rw [←eq]
      exact (at_bought L b core bought m j words side).trans (new side j)
  let mid := ProtocolRAMStaticPorts.image out lanes (port false) m
  have step₁ : (ProtocolRAMStaticPorts.program w out b.rows lanes (ordered L b core bought false)).Exec m mid
      (ProtocolRAMStaticPorts.work b.rows lanes (ordered L b core bought false)) :=
    ProtocolRAMStaticPorts.run out lanes (port false) _ m (safe false) (by omega) (operand false)
  have step₂ : (ProtocolRAMStaticPorts.program w (out+b.rows) b.rows lanes (ordered L b core bought true)).Exec
      mid (result out lanes port m) (ProtocolRAMStaticPorts.work b.rows lanes (ordered L b core bought true)) := by
    apply ProtocolRAMStaticPorts.run (out+b.rows) lanes (port true) _ mid
      (ProtocolRAMGeneratedWrite.fits_mono _ (by omega) (safe true)) (by omega)
    intro i
    exact (eval_below _ (i.val:Word w) m mid (safe true)
      (fun a ha=>ProtocolRAMStaticPorts.frame _ _ _ _ a (.inl ha))).trans (operand true i)
  intro P R K mach pc reg pub exit installed vals cfg original entry same
  exact Procedure.Exec.then step₁ step₂ mach pc reg pub exit installed vals cfg original entry same

/-- Dormant rows may contain any machine word as a socket index.  This bank
records every actual word, without asking for a port-capacity bound. -/
def raw (L : RoleProgram.Chart) (b : Board) (core bought : Bool → Socket) (m : Memory w)
    (side : Bool) (i : Fin b.rows) : Fin (2^w) :=
  (ordered L b core bought side).eval m (i.val:Word w)

theorem run (L : RoleProgram.Chart) (b : Board) (out lanes : ℕ) (core bought : Bool → Socket)
    (m : Memory w) (safe : ∀side,(ordered L b core bought side).Fits w out) (room : out+2*b.rows < 2^w) :
    (pair w L b out lanes core bought).Exec m (result out lanes (raw L b core bought m) m)
      (clock L b lanes core bought) := by
  apply run_fitted
  · exact safe
  · exact room
  · intro side i
    rw [Fin.cast_val_eq_self]
    exact (at_core L b core bought m i (by omega) side).symm
  · intro side i
    rw [Fin.cast_val_eq_self]
    exact (at_bought L b core bought m i (by omega) side).symm

/-- Only the indicated row needs to be a physical live port. All other rows
can evaluate to arbitrary words. -/
theorem read_live (L : RoleProgram.Chart) (b : Board) (out lanes : ℕ) (core bought : Bool → Socket)
    (m : Memory w) (side : Bool) (i : Fin b.rows) (port : Fin H)
    (live : (ordered L b core bought side).eval m (i.val:Word w)=(port.val:Word w)) :
    result out lanes (raw L b core bought m) m (out+side.toNat*b.rows+i.val)=
      ((port.val*lanes:ℕ):Word w) := by
  rw [read,Nat.cast_mul,Nat.cast_mul,Fin.cast_val_eq_self]
  exact congrArg (fun x : Word w => x*(lanes:Word w)) live

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Slot

end
end OAI
