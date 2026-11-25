import OAI.Hierarchy.DescentOrdinaryRefsShape
import OAI.Hierarchy.DescentPackedNodeDigit
import OAI.Hierarchy.DescentScalarBookROMPages
import OAI.Hierarchy.DescentHaloWalkRAM
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! The three compactor operators, per-node field insertion, and old node digits share one fixed installation. -/
namespace Hierarchy.DescentOrdinaryRefsROM
open DescentOrdinaryAtomFieldRAM DescentSIMDLookup DescentPackedZip DescentHaloWalkRAM
open DescentPacking.PackedMatch.Local Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

namespace Chart
variable (C : Chart)
def pages : Fin C.count → ROM.Page :=
  ROM.receiver (D:=C.donors) (K:=C.oldNodes) (cap:=C.capacity) (b:=C.bits) (n:=C.nameBits)
    (m:=C.countBits) (K':=C.newNodes) (M:=C.lanes)
def chart (j : Fin (3+C.nodes)) := ROM.joined C.pages C.width C.tableBase (ROM.pairIndex j)
def control (j : Fin 3) := C.chart (Fin.castAdd C.nodes j)
def tables : TablesAt := ⟨C.control 0,C.control 1,C.control 2⟩
def gates (j : Fin C.nodes) := C.chart (Fin.natAdd 3 j)
def dictionary := ScalarOperand.chart C.base C.bits C.oldNodes C.lanes
def digitPages := ScalarOperand.pages C.bits C.oldNodes C.lanes
def program (w : ℕ) :=
  (ROM.mount C.digitPages C.digitBits w C.base).seq (ROM.mount C.pages C.width w C.tableBase)
def output {w : ℕ} (m : Memory w) :=
  ROM.after C.pages C.width C.tableBase (ROM.after C.digitPages C.digitBits C.base m)

private theorem pair_page (j : Fin (3+C.nodes)) (i : Fin 2) :
    let controls := ![ROM.binary (DescentPackedActorMask.target C.nameBits C.actors) C.lanes,
      ROM.binary (DescentPackedActorMask.occupied C.donors C.oldNodes C.capacity C.countBits) C.lanes,
      ROM.binary (DescentPackedLocalAtoms.pack C.bits C.nodes C.newNodes) C.lanes]
    let fields := fun v : Fin C.nodes => ROM.binary (Gather.setField (d:=C.bits) v) C.lanes
    C.pages (ROM.pairIndex j i) =
      Fin.addCases (motive:=fun _ => Fin 2 → ROM.Page) controls fields j i := by
  intro controls fields
  let pageAt (p : Fin (3+C.nodes) × Fin 2) :=
    Fin.addCases (motive:=fun _ => Fin 2 → ROM.Page) controls fields p.1 p.2
  exact congrArg pageAt (finProdFinEquiv.symm_apply_apply (j,i))

theorem any {w : ℕ} (m : Memory w) (room : C.endAddress<2^w) :
    (C.program w).Exec m (C.output m) ((4+10*C.digitSize)+(4+10*C.tableSize)) ∧
    CheapCode (C.program w) ∧
    DescentStaticWordColumn.names (C.program w)=15*(C.digitSize+1)+15*(C.tableSize+1) ∧
    ∀a,a<C.base ∨ C.endAddress≤ a → C.output m a=m a := by
  have sep : C.base≤C.tableBase:=Nat.le_add_right ..
  have top : C.tableBase≤C.endAddress:=Nat.le_add_right ..
  have d:=ROM.run C.digitPages C.digitBits C.base m (top.trans_lt room)
  have t:=ROM.run C.pages C.width C.tableBase (ROM.after C.digitPages C.digitBits C.base m) room
  refine ⟨Procedure.Exec.then d.1 t.1,cheap_seq (ROM.cheap _ _ _ _) (ROM.cheap _ _ _ _),?_,?_⟩
  · exact (DescentStaticWordColumn.names_seq ..).trans (congrArg₂ (·+·) d.2 t.2)
  · intro a outside
    exact (ROM.frame C.pages C.width C.tableBase _ a (outside.imp_left (fun h=>h.trans_le sep))).trans
      (ROM.frame C.digitPages C.digitBits C.base m a (outside.imp_right (fun h=>top.trans h)))

private theorem control_page (j : Fin 3) (i : Fin 2) :
    C.pages (ROM.pairIndex (Fin.castAdd C.nodes j) i)=
    (![ROM.binary (DescentPackedActorMask.target C.nameBits C.actors) C.lanes,
       ROM.binary (DescentPackedActorMask.occupied C.donors C.oldNodes C.capacity C.countBits) C.lanes,
       ROM.binary (DescentPackedLocalAtoms.pack C.bits C.nodes C.newNodes) C.lanes] j) i := by
  simpa only [Fin.addCases_left] using C.pair_page (Fin.castAdd C.nodes j) i

private theorem gate_page (j : Fin C.nodes) (i : Fin 2) :
    C.pages (ROM.pairIndex (Fin.natAdd 3 j) i)=ROM.binary (Gather.setField (d:=C.bits) j) C.lanes i := by
  simpa only [Fin.addCases_right] using C.pair_page (Fin.natAdd 3 j) i

theorem width_bound : C.width≤C.keyBits*C.lanes := le_rfl

theorem page_width (pg : Fin C.count) : (C.pages pg).bits≤C.width := by
  have binary {a b c : ℕ} (f : Cell a→Cell b→Cell c) (side : Fin 2) :
      (ROM.binary f C.lanes side).bits ≤ (a+b)*C.lanes := by
    fin_cases side
    · exact Nat.mul_le_mul_right _ (Nat.le_add_right a b)
    · exact le_rfl
  have target : C.nameBits+C.nameBits*C.actors≤C.keyBits:=Nat.le_max_left ..
  have occupancy : 1*C.actors+C.countBits*C.donors≤C.keyBits:=
    (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  have emit : 1*C.nodes+C.bits*C.nodes≤C.keyBits:=
    ((Nat.le_max_left ..).trans (Nat.le_max_right ..)).trans (Nat.le_max_right ..)
  have field : C.bits*C.nodes+C.bits≤C.keyBits:=
    ((Nat.le_max_right ..).trans (Nat.le_max_right ..)).trans (Nat.le_max_right ..)
  have bound : ∀j : Fin (3+C.nodes),∀side : Fin 2,(C.pages (ROM.pairIndex j side)).bits≤C.keyBits*C.lanes := by
    refine Fin.addCases ?_ ?_
    · intro j side
      rw [C.control_page]
      fin_cases j
      · exact (binary _ side).trans (Nat.mul_le_mul_right _ target)
      · exact (binary _ side).trans (Nat.mul_le_mul_right _ occupancy)
      · exact (binary _ side).trans (Nat.mul_le_mul_right _ emit)
    · intro j side
      rw [C.gate_page]
      exact (binary _ side).trans (Nat.mul_le_mul_right _ field)
  obtain ⟨⟨j,side⟩,rfl⟩:=(finProdFinEquiv (m:=3+C.nodes) (n:=2)).surjective pg
  exact bound j side

theorem cells_le (w : ℕ) (old : C.digitBits≤w/2) (keys : C.keyBits*C.lanes≤w/2) :
    C.digitSize+C.tableSize≤(C.oldNodes+C.count)*2^(w/2) := by
  rw [Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) old))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (C.width_bound.trans keys)))

structure Issued {w : ℕ} (m : Memory w) : Prop where
  targets : Static C.tables.targets (DescentPackedActorMask.target C.nameBits C.actors) C.lanes m
  actors : Static C.tables.actors (DescentPackedActorMask.occupied C.donors C.oldNodes C.capacity C.countBits) C.lanes m
  fields : ∀j,Static (C.gates j) (Gather.setField (d:=C.bits) j) C.lanes m
  emit : Static C.tables.emitted (DescentPackedLocalAtoms.pack C.bits C.nodes C.newNodes) C.lanes m
  dictionary : ∀j (x:Cell C.digitBits),m ((C.dictionary j).base+x.val)=
    ((DescentSIMDLookup.table (M:=C.lanes) (ScalarOperand.take (a:=C.bits) j) x).val:Word w)

theorem issued {w : ℕ} (m : Memory w) : C.Issued (C.output m) := by
  let prior:=ROM.after C.digitPages C.digitBits C.base m
  have binary {a b c : ℕ} (j : Fin (3+C.nodes)) (f : Cell a→Cell b→Cell c)
      (defn : ∀i,C.pages (ROM.pairIndex j i)=ROM.binary f C.lanes i) :
      Static (C.chart j) f C.lanes (C.output m) :=
    ROM.binary_mounted f C.lanes C.pages C.width C.tableBase prior C.page_width (ROM.pairIndex j) defn
  refine ⟨binary _ _ (C.control_page 0),binary _ _ (C.control_page 1),
    fun j=>binary _ _ (C.gate_page j),binary _ _ (C.control_page 2),?_⟩
  intro j x
  have full : j.val*2^C.digitBits+x.val<C.digitSize :=
    (Nat.add_lt_add_left x.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ j.isLt)
  have low : (C.dictionary j).base+x.val<C.tableBase := by
    change C.base+j.val*2^C.digitBits+x.val<C.base+C.digitSize;omega
  exact (ROM.frame C.pages C.width C.tableBase prior _ (Or.inl low)).trans
    (ROM.read C.digitPages C.digitBits C.base m j le_rfl x)

structure Rooms (w out : ℕ) : Prop where
  dictionary : ∀j,(C.dictionary j).Fits w out ∧ (C.dictionary j).bits=C.digitBits
  targets : ∀e₁ e₂ : Expr,e₁.Fits w out→e₂.Fits w out→Fits C.tables.targets e₁ e₂
    C.nameBits (C.nameBits*C.actors) C.lanes out w
  actors : ∀e₁ e₂ : Expr,e₁.Fits w out→e₂.Fits w out→Fits C.tables.actors e₁ e₂
    (1*C.actors) (C.countBits*C.donors) C.lanes out w
  fields : ∀e : Fin C.nodes→Expr,(∀j,(e j).Fits w out)→Gather.Bounds (w:=w) (d:=C.bits) (M:=C.lanes) C.gates e out
  emit : ∀e₁ e₂ : Expr,e₁.Fits w out→e₂.Fits w out→Fits C.tables.emitted e₁ e₂
    (1*C.nodes) (C.bits*C.nodes) C.lanes out w

theorem rooms {out w : ℕ} (early : C.endAddress≤out) (room : out<2^w) : C.Rooms w out := by
  have banks (i : Fin C.count) := ROM.bank_room C.pages C.width C.tableBase out i (C.page_width i) early room
  have binary {a b c : ℕ} (j : Fin (3+C.nodes)) (f : Cell a→Cell b→Cell c)
      (defn : ∀i,C.pages (ROM.pairIndex j i)=ROM.binary f C.lanes i)
      (e₁ e₂ : Expr) (left : e₁.Fits w out) (right : e₂.Fits w out) :
      Fits (C.chart j) e₁ e₂ a b C.lanes out w := by
    refine ⟨left,right,banks _,banks _,?_,?_⟩
    · exact congrArg ROM.Page.bits (defn 0)
    · exact congrArg ROM.Page.bits (defn 1)
  refine ⟨?_,binary _ _ (C.control_page 0),binary _ _ (C.control_page 1),?_,binary _ _ (C.control_page 2)⟩
  · intro j
    exact ⟨ROM.bank_room C.digitPages C.digitBits C.base out j le_rfl
      ((show C.tableBase≤C.endAddress from Nat.le_add_right ..).trans early) room,rfl⟩
  · intro e fit j
    have ht:=binary _ _ (C.gate_page j) (.lit 0) (e j) trivial (fit j)
    exact ⟨fit j,ht.shift,ht.apply,ht.shiftBits,ht.applyBits⟩

end Chart
end
end Hierarchy.DescentOrdinaryRefsROM

end OAI
