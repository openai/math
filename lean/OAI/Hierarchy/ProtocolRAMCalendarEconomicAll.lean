import OAI.Hierarchy.ProtocolRAMCalendarEconomicTail
import OAI.Hierarchy.ProtocolRAMCalendarEconomicPrices
import OAI.Hierarchy.ProtocolRAMCalendarChargePages

namespace OAI
/-! # Simultaneous readback of the subdivision, all price tables, both packet charges and the empty reserve -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets BoughtSockets CatalogueRows StripChart
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {z W k attempts R K H jobs phases X Y steps : ℕ} {S : PurchaseSampler}

set_option cleanup.letToHave false in
set_option maxHeartbeats 1000000 in
theorem economic_start_all (E : EconomicHeader phases X Y steps) (ord : E.Ordered)
    (P : MenuROM.Charges) (empty : Bank) (firstCharge : P.payload.base=E.stop)
    (secondCharge : P.purchase.base=P.payload.stop) (reserveBase : empty.base=P.stop)
    (order : Fin R≃Edges S z (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (N depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (rest : Boot.Tape z (2^W))
    (markets : Fin jobs→Market z (2^W) k) {size : ℕ} (layout : Boot.Layout markets size) (v : Directory attempts)
    (positive : 0<phases) (room : empty.base+empty.size<2^Native.wordBits z (2^W) Native.copies)
    (before : ∀i,empty.base+empty.size≤Boot.low (markets i)) (within : empty.base+empty.size≤ size)
    (first : 2^z≤joint.initial) (afterHeap : Native.heapEnd z (2^W) Native.copies≤joint.initial)
    (afterScore : JointHeader.stop joint z N k phases≤E.ports.base)
    (lowBase : stop S z W k attempts depth K packed.groups H R≤joint.initial) :
    let tail:=reserveWords empty rest
    let input:=E.scalar.words (E.vectorMemory (P.words tail))
    let source:=low order M groups packed depth input
    let words:=JointHeader.words joint z (2^W) N k phase π (fun _=>0) (E.ports.words source)
    let mid:=Boot.booted markets size words
    (Native.subdivisionProgram z (2^W)).Exec (Boot.initial markets size words) mid (Native.subdivisionConstant (2^W)*2^z) ∧
      Boot.Receipt markets π (Computability.VPVNP.RAMMemory.initialMemory size words) mid ∧
      Seen order M groups packed v depth π mid ∧ E.Resident mid ∧ P.Resident mid ∧
      InitialPrices joint z N k phase (fun _=>0) mid ∧ (∀u,empty.read mid u=0) := by
  intro tail input source words mid
  let final:=empty.base+empty.size
  have belowTotal : P.stop≤final:=reserveBase.ge.trans (Nat.le_add_right ..)
  have paidEnd : P.payload.stop≤P.stop:=secondCharge.ge.trans (Nat.le_add_right ..)
  have original : E.stop≤P.payload.stop:=firstCharge.ge.trans (Nat.le_add_right ..)
  have last:=original.trans (paidEnd.trans belowTotal)
  have addr : joint.initial≤JointHeader.stop joint z N k phases :=
    (Nat.le_add_right ..).trans ((JointHeader.order joint z N k).trans (Nat.le_add_right ..))
  have core:=lowBase.trans (addr.trans afterScore)
  have heap:=afterHeap.trans (addr.trans afterScore)
  have above : ∀m x,E.scalar.base≤x→low order M groups packed depth m x=m x := by
    intro m x hx
    exact low_above order M groups packed depth m x (core.trans ((Nat.le_add_right ..).trans (ord.scalarBase.le.trans hx)))
  have start:=economic_start E ord order M groups packed joint N depth phase π (fun _=>0) (P.words tail)
    markets layout v positive (last.trans_lt room) (fun i=>last.trans (before i)) (last.trans within)
    first afterScore heap lowBase core
  have sums : P.payload.entries<2^Native.wordBits z (2^W) Native.copies :=
    (P.payload.entries_lt_stop (by decide)).trans_le (paidEnd.trans (belowTotal.trans room.le))
  have sums' : P.purchase.entries<2^Native.wordBits z (2^W) Native.copies :=
    (P.purchase.entries_lt_stop (by decide)).trans_le (belowTotal.trans room.le)
  have scalarEnd : E.scalar.stop ≤ E.stop := by
    have p:=EconomicHeader.Ordered.menu_bounds E ord
    obtain ⟨a,b,c,d,_,f,g⟩:=ord
    have l : E.ports.base≤E.ports.stop:=Nat.le_add_right ..
    have m : E.scalar.base≤E.scalar.stop:=Nat.le_add_right ..
    have n : E.payload.base≤E.payload.stop:=Nat.le_add_right ..
    have o : E.bought.base≤E.bought.stop:=Nat.le_add_right ..
    have q : E.payloadTree.base≤E.payloadTree.stop:=Nat.le_add_right ..
    have r : E.boughtTree.base≤E.stop:=Nat.le_add_right ..
    omega
  have portEnd : E.ports.stop ≤ E.stop := ord.scalarBase.le.trans ((Nat.le_add_right ..).trans scalarEnd)
  have p₁ : E.ports.base ≤ E.stop := (Nat.le_add_right ..).trans portEnd
  have preserved (x : ℕ) (lo : E.stop ≤ x) (hi : x<final) : mid x = P.words tail x := by
    have base := p₁.trans lo
    have kept : mid x = Computability.VPVNP.RAMMemory.initialMemory size words x := start.2.1.kept x (heap.trans base) (fun i reach =>
      Nat.not_lt_of_ge reach.1 (hi.trans_le (before i)))
    rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le within)] at kept
    exact kept.trans ((JointHeader.tail_words joint phase π (fun _=>0) (E.ports.words source) x first
      (afterScore.trans base)).trans ((E.ports.frame source x (.inr (portEnd.trans lo))).trans
        ((above input x ((Nat.le_add_right ..).trans (scalarEnd.trans lo))).trans (E.tail_words ord _ x lo))))
  have raw := DiscrepancyROM.resident_both P.payload P.purchase tail secondCharge.ge sums.le sums'.le
  have bill : P.Resident mid :=
    ⟨raw.1.frame (fun x lo hi => preserved x (firstCharge.ge.trans lo) (hi.trans_le (paidEnd.trans belowTotal))),
     raw.2.frame (fun x lo hi => preserved x (original.trans (secondCharge.ge.trans lo)) (hi.trans_le belowTotal))⟩
  have lowPrices:=afterScore.trans (p₁.trans last)
  have prices:=start_prices joint phase π (fun _=>0) (E.ports.words source) markets layout Nat.one_le_two_pow
    first afterHeap (lowPrices.trans within) (fun i=>lowPrices.trans (before i))
  refine ⟨start.1,start.2.1,start.2.2.1,start.2.2.2,bill,prices,?_⟩
  intro u
  let x := empty.base+u.val%empty.size
  have lo : empty.base ≤ x := Nat.le_add_right ..
  have hi : x < final := Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _
  change mid x = 0
  exact (preserved x (original.trans (paidEnd.trans (reserveBase.ge.trans lo))) hi).trans
    ((P.purchase.outside _ (.inr (reserveBase.ge.trans lo))).trans
      ((P.payload.outside _ (.inr (paidEnd.trans (reserveBase.ge.trans lo)))).trans (reserveWords_read empty rest u)))

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
