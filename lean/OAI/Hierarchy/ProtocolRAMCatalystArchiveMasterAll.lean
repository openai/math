import OAI.Hierarchy.ProtocolRAMCatalystArchiveMaster
import OAI.Hierarchy.ProtocolRAMCalendarEconomicAll

namespace OAI
/-! # Common subdivision for prices, selector charges, zero reserve and terminal archive -/

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

def chargedMasterWords (E : EconomicHeader phases X Y steps) (P : MenuROM.Charges) (empty : Bank)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D) : Boot.Tape z D :=
  let extra:=staticWords a id amt p o ci cj owners edges raw
  let econ:=E.scalar.words (E.vectorMemory (P.words (reserveWords empty extra)))
  JointHeader.words joint z D scores k phase π (fun _=>0) (E.ports.words (CoreRoute.low order M groups dir depth econ))

theorem chargedMasterWords_authentic (E : EconomicHeader phases X Y steps) (P : MenuROM.Charges) (empty : Bank)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D) (first : 2^z≤joint.initial) :
    ∀i : Fin (2^z),
      chargedMasterWords E P empty order M groups dir joint scores depth phase π a id amt p o ci cj owners edges raw i.val=
        ((π i).val:Word _) :=
  JointHeader.authentic («N»:=scores) (k:=k) joint phase π (fun _=>0) _ first

theorem chargedMasterWords_rowOnly {count payload : ℕ} (c : Mesh) (history : Attempt→Entry count payload)
    (rows : Attempt→ℕ) (same : ∀t,(history t).rows=rows t) (idBase amountBase : Event→ℕ)
    (E : EconomicHeader phases X Y steps) (P : MenuROM.Charges) (empty : Bank)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D) :
    chargedMasterWords E P empty order M groups dir joint scores depth phase π a
      (sourceAt c history idBase) (sourceAt c history amountBase) p o ci cj owners edges raw =
    chargedMasterWords E P empty order M groups dir joint scores depth phase π a
      (rowOnly c rows idBase) (rowOnly c rows amountBase) p o ci cj owners edges raw := by
  simp only [chargedMasterWords,staticWords,mount_eq_rowOnly c history rows same idBase amountBase]


theorem chargedMasterWords_above (E : EconomicHeader phases X Y steps) (ord : E.Ordered)
    (P : MenuROM.Charges) (empty : Bank) (firstCharge : P.payload.base=E.stop)
    (secondCharge : P.purchase.base=P.payload.stop) (reserveBase : empty.base=P.stop)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D)
    (space : StaticSpace a p owners n r edges (Native.wordBits z D Native.copies))
    (tail : empty.base+empty.size≤a.kind.base) (first : 2^z≤joint.initial)
    (scoreEnd : JointHeader.stop joint z scores k phases≤E.ports.base)
    (board : CoreRoute.stop S z W k attempts depth K dir.groups H R≤joint.initial)
    (x : ℕ) (high : owners.base+owners.size≤x) :
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
  have above : empty.base+empty.size≤x := by omega
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
    have size:=space.recipeSize f
    cases f <;> simp only [which] at size ⊢ <;> omega
  have caps:=space.ownerSize
  exact recFrame.trans (ite_eq_right (fun inside=>by omega))

theorem master_start_all (E : EconomicHeader phases X Y steps) (ord : E.Ordered)
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
    (board : CoreRoute.stop S z W k attempts depth K dir.groups H R≤joint.initial) :
    let words:=chargedMasterWords E P empty order M groups dir joint scores depth phase π a id amt p o ci cj owners edges raw
    let mid:=Boot.booted v size words
    (Native.subdivisionProgram z D).Exec (Boot.initial v size words) mid (Native.subdivisionConstant D*2^z) ∧
      Boot.Receipt v π (Computability.VPVNP.RAMMemory.initialMemory size words) mid ∧
      Seen order M groups dir sockets depth π mid ∧ E.Resident mid ∧ P.Resident mid ∧
      InitialPrices joint z scores k phase (fun _=>0) mid ∧ (∀u,empty.read mid u=0) ∧
      StaticAt a id amt p o ci cj owners edges raw mid ∧
      ∀{q goods : ℕ} (C : Chart (Native.wordBits z D Native.copies) q goods) (arena : Arena) (flag : ℕ),
        owners.base+owners.size≤arena.first → (flag<a.kind.base ∨ owners.base+owners.size≤flag) →
        (∀e x,x<arena.base C.mesh e → protected C x e) → mounted C (events C.mesh) mid →
        StaticAt a id amt p o ci cj owners edges raw (checkedOut C flag mid) := by
  intro words mid
  let extra:=staticWords a id amt p o ci cj owners edges raw
  let charged:=P.words (reserveWords empty extra)
  let econ:=E.scalar.words (E.vectorMemory charged)
  let lowData:=CoreRoute.low order M groups dir depth econ
  have reserveOrder:=space.reserveOrder
  have routeStart:=space.routeStart
  have kindEnd:=space.kindEnd
  have modeEnd:=space.modeEnd
  have operandEnd:=space.operandEnd
  have upper : empty.base+empty.size≤owners.base+owners.size := by omega
  have paidEnd : P.payload.stop≤P.stop:=secondCharge.ge.trans (Nat.le_add_right ..)
  have original : E.stop≤P.payload.stop:=firstCharge.ge.trans (Nat.le_add_right ..)
  have tailEnd : P.stop≤empty.base+empty.size:=reserveBase.ge.trans (Nat.le_add_right ..)
  have econEnd : E.stop≤a.kind.base:=original.trans (paidEnd.trans (tailEnd.trans tail))
  have atJoint : joint.initial≤JointHeader.stop joint z scores k phases :=
    (Nat.le_add_right ..).trans ((JointHeader.order joint z scores k).trans (Nat.le_add_right ..))
  have ports:=board.trans (atJoint.trans scoreEnd)
  have heap:=afterHeap.trans (atJoint.trans scoreEnd)
  have portStop:=economic_ports_end E ord
  have portStart : E.ports.base≤E.stop:=(Nat.le_add_right ..).trans portStop
  obtain ⟨ran,boot,seen,economic,charges,prices,zero⟩:=economic_start_all E ord P empty
    firstCharge secondCharge reserveBase order M groups dir joint scores depth phase π extra v layout sockets
    positive (upper.trans_lt wide) (fun j=>upper.trans (marketFit j)) (upper.trans tapeFit)
    first afterHeap scoreEnd board
  have same (x : ℕ) (lo : a.kind.base≤x) (hi : x<owners.base+owners.size) : mid x=extra x := by
    have old:=boot.kept x (heap.trans (portStart.trans (econEnd.trans lo)))
      (fun j hit=>(hi.trans_le (marketFit j)).not_ge hit.1)
    rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le tapeFit)] at old
    change mid x=JointHeader.words joint z D scores k phase π (fun _=>0) (E.ports.words lowData) x at old
    rw [JointHeader.tail_words _ _ _ _ _ _ first (scoreEnd.trans (portStart.trans (econEnd.trans lo))),
      E.ports.frame _ x (.inr (portStop.trans (econEnd.trans lo)))] at old
    have lowWord : lowData x=econ x := CoreRoute.low_above order M groups dir depth econ x
      (ports.trans (portStart.trans (econEnd.trans lo)))
    have economicWord : econ x=charged x := E.tail_words ord charged x (econEnd.trans lo)
    have upperCharge:=tailEnd.trans (tail.trans lo)
    have eqPaid : charged x=reserveWords empty extra x :=
      (P.purchase.outside _ (.inr upperCharge)).trans (P.payload.outside _ (.inr (paidEnd.trans upperCharge)))
    exact (((old.trans lowWord).trans economicWord).trans eqPaid).trans
      (ite_eq_right (fun inside=>inside.2.not_ge (tail.trans lo)))
  refine ⟨ran,boot,seen,economic,charges,prices,zero,staticAt a id amt p o ci cj owners edges raw mid space same,?_⟩
  intro q goods C arena flag top aside floor active
  apply staticAt a id amt p o ci cj owners edges raw _ space
  intro x lo hi
  have off : x<flag ∨ flag+1≤x := by rcases aside with h|h <;> omega
  rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ off]
  exact (run_frame C _ _ x active (fun e _=>floor e x ((hi.trans_le top).trans_le (Nat.le_add_right ..)))).trans
    (same _ lo hi)

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
