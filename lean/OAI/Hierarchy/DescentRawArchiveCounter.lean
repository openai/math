import OAI.Hierarchy.DescentRawGeometryStore
import OAI.Hierarchy.DescentIssuedEdgeCounter

namespace OAI
/-! # Carry the private-bit register across the actual issued native field publisher -/

namespace Hierarchy.DescentSixParty.Chronology
open DescentStageEdgeReceipt DescentKernelHistory DescentPacking DescentHistoryOrder
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentOrdinaryRawRows
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k i z D wire hist z' D' : ℕ}
variable {a : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
variable {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
variable {b : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink a he T c n b)
set_option quotPrecheck false
local notation "sc" => (BitDescription.scannedRows he T)
local notation "raw" => rawGraph he T c
local notation "live" => (Fintype.card W.graph.Edge+10*Fintype.card (sc).pairs)
local notation "ix" => rawOrdinal he T c a.order ticket.pair
local notation "owner" => rawOwner he T c n ((sc).state c) (originalId _)
local notation "wordAt" => truth W.graph G (sc).pick T.z ((sc).profile c) owner W.core

/-- The counter consumes only the first three of the five resident columns; the actual
staging bank names, zero padding, number of real rows and owners come from the same normalization. -/
theorem OrdinaryLink.measured_counter {bw cap : ℕ} (m : Memory bw) (B : DescentPrivateEdgeCounter.Banks)
    (room : DescentPrivateEdgeCounter.Room B bw cap)
    (enough : live≤cap) (names : Fintype.card n.result.graph.Site≤2^bw)
    (leftSize : cap≤B.leftID.size) (rightSize : cap≤B.rightID.size) (widthSize : cap≤B.width.size)
    (field : Column→ℕ)
    (leftBank : B.leftID.base=field .src) (rightBank : B.rightID.base=field .dst)
    (widthBank : B.width.base=field .width)
    (words : ∀f e,m (field f+MarkedWorld.edgeNumber W (dense a.order) ticket.pair e)=(wordAt f e:Computability.VPVNP.BurstRAM.Word bw))
    (zero : ∀f j,live≤j→j<cap→m (field f+j)=0) :
    ∃post,(DescentPrivateEdgeCounter.program B bw cap).Exec m post (DescentPrivateEdgeCounter.cost B cap) ∧
      post B.out=m B.oldTotal+(ordinaryFee ticket:Computability.VPVNP.BurstRAM.Word bw) ∧
      ∀j,j<B.flags ∨ B.out+1≤j→post j=m j := by
  let cell (f : Column) (j : ℕ) : ℕ := if hj : j<live then wordAt f ((ix).symm ⟨j,hj⟩) else 0
  have trueCell (f : Column) (e : (raw).Edge) : cell f (MarkedWorld.edgeNumber W (dense a.order) ticket.pair e)=wordAt f e := by
    change cell f (ix e).val=_
    dsimp only [cell]
    rw [dite_eq_left (ix e).isLt]
    exact congrArg (wordAt f) ((ix).symm_apply_apply e)
  have inRange (f : Column) (j : Fin cap) : m (field f+j.val)=(cell f j.val:Computability.VPVNP.BurstRAM.Word bw) := by
    by_cases hi : j.val<live
    · let row : Fin live := ⟨j.val,hi⟩
      let v := (ix).symm row
      have ord : (ix v).val = j.val := congrArg Fin.val ((ix).apply_symm_apply row)
      have r := words f v
      change m (field f+(ix v).val)=_ at r
      rw [ord] at r
      simpa only [cell,dite_eq_left hi] using r
    · simpa only [cell,dite_eq_right hi,Nat.cast_zero] using zero f j.val (Nat.le_of_not_gt hi) j.isLt
  have wide : cap<2^bw := by have:=room.flagsFit;have:=room.sumFit;have:=room.finish;omega
  have getter (v : Bank) (f : Column) (base : v.base=field f) (fit : cap≤v.size) (j : Fin cap) :
      v.read m (j.val:Computability.VPVNP.BurstRAM.Word bw)=(cell f j.val:Computability.VPVNP.BurstRAM.Word bw) := by
    simpa [Bank.read,base,Fin.val_cast_of_lt (j.isLt.trans wide),Nat.mod_eq_of_lt (j.isLt.trans_le fit)] using inRange f j
  have idRoom (u : (raw).Site) : owner u<2^bw := by
    apply lt_of_lt_of_le _ names
    exact (Fintype.equivFin n.result.graph.Site _).isLt
  have endRoom (f : Column) (choice : f=.src ∨ f=.dst) (j : Fin cap) : cell f j<2^bw := by
    rcases choice with rfl|rfl <;> unfold cell <;> split
    · apply idRoom
    · positivity
    · apply idRoom
    · positivity
  have load : DescentPrivateEdgeCounter.Loaded B m (fun j : Fin cap=>cell .src j=cell .dst j) (fun j=>cell .width j) := by
    refine ⟨?_,getter B.width .width widthBank widthSize⟩
    intro j
    rw [getter B.leftID .src leftBank leftSize,getter B.rightID .dst rightBank rightSize]
    constructor
    · intro eq
      simpa [Fin.val_cast_of_lt (endRoom .src (.inl rfl) j),Fin.val_cast_of_lt (endRoom .dst (.inr rfl) j)] using congrArg Fin.val eq
    · exact congrArg (fun a : ℕ=>(a:Computability.VPVNP.BurstRAM.Word bw))
  have calcStep:=ticket.counter_read B m (cell .src) (cell .dst) (cell .width) room load enough
    (fun j hj _=>by simp only [cell,dite_eq_right (Nat.not_lt.mpr hj)]) (trueCell .src) (trueCell .dst) (trueCell .width)
  exact ⟨_,calcStep.1,calcStep.2,DescentPrivateEdgeCounter.frame B m _ _ room⟩

/-- One branch-independent native procedure emits all five raw columns and updates
the preceding private-bit account, using the actual compact matching and full active counts. -/
theorem OrdinaryLink.physical_expansion {bw oc pc : ℕ} (m : Memory bw) (banks : Sources)
    (lens : Padded.Counts) (base : ℕ) (counter : DescentPrivateEdgeCounter.Banks)
    (site : W.graph.Site↪ℕ) (codes : (sc).pairs→ℕ)
    (rawSpace : Five.Bounds banks lens G.b bw base oc pc)
    (source : Inputs W.graph G banks (sc).pick T.z ((sc).profile c) owner (dense a.order) site W.core ticket.pair codes m)
    (oldFit : Fintype.card W.graph.Edge≤oc) (pairFit : Fintype.card (sc).pairs≤pc)
    (oldCount : m lens.old=(Fintype.card W.graph.Edge:Computability.VPVNP.BurstRAM.Word bw)) (pairCount : m lens.pairs=(Fintype.card (sc).pairs:Computability.VPVNP.BurstRAM.Word bw))
    (space : DescentPrivateEdgeCounter.Room counter bw (Five.capacity oc pc)) (oldBefore : counter.oldTotal<base)
    (names : Fintype.card n.result.graph.Site≤2^bw)
    (leftSize : Five.capacity oc pc≤counter.leftID.size) (rightSize : Five.capacity oc pc≤counter.rightID.size)
    (widthSize : Five.capacity oc pc≤counter.width.size)
    (leftBank : counter.leftID.base=(Five.output base oc pc (Five.index .src)).base)
    (rightBank : counter.rightID.base=(Five.output base oc pc (Five.index .dst)).base)
    (widthBank : counter.width.base=(Five.output base oc pc (Five.index .width)).base)
    (beforeCounter : base+5*Five.capacity oc pc≤counter.flags) :
    let cap:=Five.capacity oc pc
    let field:=fun f=>(Five.output base oc pc (Five.index f)).base
    ∃post,((Five.program banks lens G.b bw base oc pc 5).seq (DescentPrivateEdgeCounter.program counter bw cap)).Exec m post
      (Five.steps banks lens G.b base oc pc 5+DescentPrivateEdgeCounter.cost counter cap) ∧
      post counter.out=m counter.oldTotal+(ordinaryFee ticket:Computability.VPVNP.BurstRAM.Word bw) ∧
      (∀j,j<base→post j=m j) ∧
      (∀f e,post (field f+MarkedWorld.edgeNumber W (dense a.order) ticket.pair e)=(wordAt f e:Computability.VPVNP.BurstRAM.Word bw)) ∧
      (∀f j,live≤j→j<cap→post (field f+j)=0) := by
  let cap:=Five.capacity oc pc
  let field:=fun f=>(Five.output base oc pc (Five.index f)).base
  have enough : live≤cap := by dsimp [cap,Five.capacity];omega
  have wide : 1<2^bw := by have:=space.held;have:=space.flagsFit;have:=space.sumFit;have:=space.finish;omega
  obtain ⟨stage,first,kept,words,pad⟩:=Five.geometry W G banks (sc).pick T.z ((sc).profile c) owner (dense a.order)
    site ticket.pair codes m lens base oc pc rawSpace source wide oldFit pairFit oldCount pairCount
  obtain ⟨post,last,amount,stay⟩:=ticket.measured_counter stage counter space enough names leftSize rightSize widthSize field
    leftBank rightBank widthBank words pad
  have lower (f : Column) (j : ℕ) (small : j<cap) : field f+j<counter.flags := by
    have le:=Nat.mul_le_mul_right cap (show Five.index f+1≤5 from Five.index_lt f)
    rw [Nat.succ_mul] at le
    dsimp [field,Five.output]
    change base+Five.index f*cap+j<counter.flags
    change base+5*cap≤counter.flags at beforeCounter
    omega
  refine ⟨post,Procedure.Exec.then first last,amount.trans (congrArg (·+(ordinaryFee ticket:Computability.VPVNP.BurstRAM.Word bw)) (kept _ oldBefore)),
    fun j hj=>(stay _ (.inl (by omega))).trans (kept _ hj),?_,?_⟩
  · intro f e
    have good:=lower f (ix e).val ((ix e).isLt.trans_le enough)
    exact (stay _ (.inl good)).trans (words _ e)
  · exact fun f j lo hi=>(stay _ (.inl (lower f j hi))).trans (pad _ j lo hi)

end
end Hierarchy.DescentSixParty.Chronology

end OAI
