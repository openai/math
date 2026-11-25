import OAI.Hierarchy.ProtocolRAMCatalystArchiveMasterAll

namespace OAI
/-! # Original paid quotient/parity banks below the signed archive remain raw -/
noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Calendar.CoreRoute Calendar.StripChart Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets
open BoughtSockets AdaptiveProbe CatalogueRows
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

variable {z W k w n edges : ℕ}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "r" => Fintype.card (Slots z D k)

variable {attempts R K H jobs phases X Y steps size : ℕ} {S : PurchaseSampler}

theorem chargedMasterWords_gap (E : EconomicHeader phases X Y steps) (ord : E.Ordered)
    (P : MenuROM.Charges) (empty : Bank) (firstCharge : P.payload.base=E.stop)
    (secondCharge : P.purchase.base=P.payload.stop) (reserveBase : empty.base=P.stop)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D)
    (space : StaticSpace a p owners n r edges (Native.wordBits z D Native.copies))
    (_tail : empty.base+empty.size≤a.kind.base) (first : 2^z≤joint.initial)
    (scoreEnd : JointHeader.stop joint z scores k phases≤E.ports.base)
    (board : CoreRoute.stop S z W k attempts depth K dir.groups H R≤joint.initial)
    (x : ℕ) (above : empty.base+empty.size≤x) (below : x<a.kind.base) :
    chargedMasterWords E P empty order M groups dir joint scores depth phase π a id amt p o ci cj owners edges raw x=raw x := by
  let extra:=staticWords a id amt p o ci cj owners edges raw
  let charged:=P.words (reserveWords empty extra)
  let econ:=E.scalar.words (E.vectorMemory charged)
  let service:=recipes p o ci cj (ownerAdvice owners edges raw)
  have atJoint : joint.initial≤JointHeader.stop joint z scores k phases :=
    (Nat.le_add_right ..).trans ((JointHeader.order joint z scores k).trans (Nat.le_add_right ..))
  have paidEnd : P.payload.stop≤P.stop:=secondCharge.ge.trans (Nat.le_add_right ..)
  have original : E.stop≤P.payload.stop:=firstCharge.ge.trans (Nat.le_add_right ..)
  have tailEnd : P.stop≤empty.base+empty.size:=reserveBase.ge.trans (Nat.le_add_right ..)
  have A:=space.reserveOrder
  have B:=space.routeStart
  have C:=space.kindEnd
  have F:=space.modeEnd
  have G:=space.operandEnd
  have econEnd:=original.trans (paidEnd.trans (tailEnd.trans above))
  have portEnd:=(economic_ports_end E ord).trans econEnd
  have portStart : E.ports.base≤x:=(Nat.le_add_right ..).trans portEnd
  have live : charged x=extra x :=
    ((P.purchase.outside _ (.inr (tailEnd.trans above))).trans
      (P.payload.outside _ (.inr (paidEnd.trans (tailEnd.trans above))))).trans
        (ite_eq_right (fun inside=>inside.2.not_ge above))
  change JointHeader.words joint z D scores k phase π (fun _=>0)
    (E.ports.words (CoreRoute.low order M groups dir depth econ)) x=raw x
  rw [JointHeader.tail_words _ _ _ _ _ _ first (scoreEnd.trans portStart),E.ports.frame _ x (.inr portEnd),
    CoreRoute.low_above order M groups dir depth econ x (board.trans (atJoint.trans (scoreEnd.trans portStart)))]
  have economicWord : econ x=extra x := (E.tail_words ord charged x econEnd).trans live
  rw [economicWord]
  change mount a id amt service x=raw x
  rw [frame a id amt service x (by omega) (by omega)]
  have recFrame : service x=ownerAdvice owners edges raw x := by
    apply recipes_frame
    intro f
    cases f <;> simp only [which] <;> omega
  exact recFrame.trans (ite_eq_right (fun inside=>by omega))

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
