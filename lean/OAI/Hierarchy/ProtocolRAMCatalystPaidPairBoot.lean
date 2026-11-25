import OAI.Hierarchy.ProtocolRAMCatalystMasterGap
import OAI.Hierarchy.ProtocolRAMCatalystSlabLayout
import OAI.Hierarchy.ProtocolRAMPaidPairDirectory

namespace OAI
/-! # Installing the original sparse route directories in the charged master boot -/
noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Calendar.CoreRoute Calendar.StripChart Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets
open BoughtSockets AdaptiveProbe CatalogueRows
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {z W k n attempts R K H jobs phases X Y steps size : ℕ} {S : PurchaseSampler}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "r" => Fintype.card (Slots z D k)

theorem paid_pair_master (E : EconomicHeader phases X Y steps) (ord : E.Ordered)
    (P : MenuROM.Charges) (empty : Bank) (firstCharge : P.payload.base=E.stop)
    (secondCharge : P.purchase.base=P.payload.stop) (reserveBase : empty.base=P.stop)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D) (v : Fin jobs→Market z D k)
    (layout : Boot.Layout v size) (sockets : BoughtSockets.Directory attempts)
    (space : StaticSpace a p owners n r edges (Native.wordBits z D Native.copies))
    (positive : 0<phases)
    (tail : empty.base+empty.size≤a.kind.base) (wide : owners.base+owners.size<2^(Native.wordBits z D Native.copies))
    (tapeFit : owners.base+owners.size≤ size) (marketFit : ∀j,owners.base+owners.size≤Boot.low (v j))
    (first : 2^z≤joint.initial) (scoreEnd : JointHeader.stop joint z scores k phases≤E.ports.base)
    (afterHeap : Native.heapEnd z D Native.copies≤joint.initial)
    (board : CoreRoute.stop S z W k attempts depth K dir.groups H R≤joint.initial) (base : ℕ) (afterE : empty.base+empty.size≤base)
    (pairEnd : Slab.staticStart base r≤a.kind.base) :
    let occ:=Slab.pairOwners base r
    let tag:=Slab.pairParity base r
    let paired:=PaidPairDirectory.mount occ tag r raw
    let words:=chargedMasterWords E P empty order M groups dir joint scores depth phase π a id amt p o ci cj owners edges paired
    let mid:=Boot.booted v size words
    E.Resident mid ∧ PaidPairDirectory.Reads occ tag r mid ∧
      ∀{q goods : ℕ} (C : Chart (Native.wordBits z D Native.copies) q goods) (arena : Arena) (flag : ℕ),
        a.kind.base≤arena.first → arena.first≤flag → (∀e x,x<arena.base C.mesh e→protected C x e) →
        mounted C (events C.mesh) mid →
        PaidPairDirectory.Reads occ tag r (checkedOut C flag mid) := by
  intro occ tag paired words mid
  have boot := master_start_all E ord P empty firstCharge secondCharge reserveBase order M groups dir joint scores depth phase
    π a id amt p o ci cj owners edges paired v layout sockets space positive tail wide tapeFit marketFit first scoreEnd afterHeap board
  obtain ⟨_,receipt,_,resident,_⟩ := boot
  have covered : 2*r≤2^((2*r).log2+1) := (Nat.lt_log2_self (n:=2*r)).le
  have separate : occ.base+2*r≤tag.base := Nat.add_le_add_left covered base
  have bounds (x : ℕ) (inPage : PaidPairDirectory.occupied occ tag r x) : base≤x ∧ x<a.kind.base := by
    change base+2^((2*r).log2+1)+2^((2*r).log2+1)≤a.kind.base at pairEnd
    rcases inPage with ⟨lo,hi⟩ | ⟨lo,hi⟩
    · change base≤x at lo
      change x<base+2*r at hi
      omega
    · change base+2^((2*r).log2+1)≤x at lo
      change x<base+2^((2*r).log2+1)+2*r at hi
      omega
  have hStatic : a.kind.base≤owners.base+owners.size := by
    have h1:=space.reserveOrder
    have h2:=space.routeStart
    have h3:=space.kindEnd
    have h4:=space.modeEnd
    have h5:=space.operandEnd
    omega
  have hHeap : Native.heapEnd z D Native.copies≤base := by
    have atJoint : joint.initial≤JointHeader.stop joint z scores k phases :=
      (Nat.le_add_right ..).trans ((JointHeader.order joint z scores k).trans (Nat.le_add_right ..))
    have endP:=(economic_ports_end E ord)
    have startP : E.ports.base≤E.ports.stop := Nat.le_add_right ..
    have belowP : E.stop≤empty.base+empty.size := by
      have paid1 : P.payload.base≤P.payload.stop := Nat.le_add_right ..
      have paid2 : P.purchase.base≤P.stop := Nat.le_add_right ..
      omega
    exact afterHeap.trans (atJoint.trans (scoreEnd.trans (startP.trans (endP.trans (belowP.trans afterE)))))
  have read : PaidPairDirectory.Reads occ tag r mid := by
    apply (PaidPairDirectory.read_mount occ tag r raw separate).transfer
    intro x member
    obtain ⟨lo,hi⟩:=bounds x member
    have endAt:=hi.trans_le hStatic
    have live:=receipt.kept x (hHeap.trans lo) (fun i hit=>(endAt.trans_le (marketFit i)).not_ge hit.1)
    rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (endAt.trans_le tapeFit)] at live
    exact live.trans (chargedMasterWords_gap E ord P empty firstCharge secondCharge reserveBase order M groups dir
      joint scores depth phase π a id amt p o ci cj owners edges paired space tail first scoreEnd board x (afterE.trans lo) hi)
  refine ⟨resident,read,?_⟩
  intro q goods C arena flag stop flagLo free ready
  apply PaidPairDirectory.checked_reads C flag mid read ready
  · intro x active ev _
    exact free ev x (((bounds x active).2.trans_le stop).trans_le (Nat.le_add_right ..))
  · intro active
    exact ((bounds flag active).2.trans_le stop).not_ge flagLo

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
