import OAI.Hierarchy.ProtocolRAMCatalystLayoutTypes
import OAI.Hierarchy.ProtocolRAMCatalystArchiveBoot
import OAI.Hierarchy.ProtocolRAMCoreRouteMount
import OAI.Hierarchy.ProtocolRAMCalendarEconomicStart
import OAI.Hierarchy.ProtocolRAMCalendarEconomicTail
import OAI.Hierarchy.ProtocolRAMPacked

namespace OAI
/-! # One original permutation header for routing, economic controls and the reserve ledger -/

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

def staticWords (a : ReserveUse.Archive) (id amt : Fin n→ℕ) (p : Recipes) (o : Orders z D k)
    (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Memory w) : Memory w :=
  mount a id amt (recipes p o ci cj (ownerAdvice owners edges raw))

structure StaticAt (a : ReserveUse.Archive) (id amt : Fin n→ℕ) (p : Recipes) (o : Orders z D k)
    (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw out : Memory w) : Prop where
  kept : ∀u,u<2*n → out (a.kind.base+u)=mount a id amt raw (a.kind.base+u) ∧
    out (a.pointer.base+u)=mount a id amt raw (a.pointer.base+u)
  route : Installed p o ci cj out
  sinkOwners : Owners owners edges out

/-- Reinterpret the already installed public tape at the ordinal of the actual
execution. Every address and every byte stays the same. -/
theorem StaticAt.issued {count payload : ℕ} (c : Mesh) (history : Attempt→Entry count payload)
    (rows : Attempt→ℕ) (same : ∀t,(history t).rows=rows t) (idBase amountBase : Event→ℕ)
    {a : ReserveUse.Archive} {p : Recipes} {o : Orders z D k} {ci : Commodity (Fin (2^z)) N k→ℕ}
    {cj : Columns z D×Fin k→ℕ} {owners : Bank} {edges : ℕ} {raw out : Memory w}
    (fixed : StaticAt a (rowOnly c rows idBase) (rowOnly c rows amountBase) p o ci cj owners edges raw out) :
    StaticAt a (sourceAt c history idBase) (sourceAt c history amountBase) p o ci cj owners edges raw out := by
  refine ⟨?_,fixed.route,fixed.sinkOwners⟩
  intro u hu
  rw [mount_eq_rowOnly c history rows same idBase amountBase a raw]
  exact fixed.kept u (by simpa only [recordCount_rowOnly c history rows same] using hu)

theorem staticAt (a : ReserveUse.Archive) (id amt : Fin n→ℕ) (p : Recipes) (o : Orders z D k)
    (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw out : Memory w) (space : StaticSpace a p owners n r edges w)
    (same : ∀x,a.kind.base≤x→x<owners.base+owners.size →
      out x=staticWords a id amt p o ci cj owners edges raw x) :
    StaticAt a id amt p o ci cj owners edges raw out := by
  let packed:=ownerAdvice owners edges raw
  let schedule:=recipes p o ci cj packed
  have A:=space.reserveOrder
  have B:=space.routeStart
  have C:=space.kindEnd
  have F:=space.modeEnd
  have G:=space.operandEnd
  have border (f : CoreRoute.Field) :
      p.kind.base≤(which p f).base ∧ (which p f).base+(which p f).size≤owners.base := by
    cases f <;> dsimp only [which] <;> omega
  have upper (x : ℕ) (lo : p.kind.base≤x) (hi : x<owners.base+owners.size) : out x=schedule x :=
    (same x (by omega) hi).trans (frame a id amt schedule x (by omega) (by omega))
  have get (f : CoreRoute.Field) (q : Word w) :
      (which p f).read out q=(which p f).read schedule q := by
    have bound:=border f
    have rem : q.val%(which p f).size<(which p f).size:=Nat.mod_lt _ (Nat.two_pow_pos _)
    exact upper ((which p f).base+q.val%(which p f).size) (by omega) (by omega)
  have kindCap:=space.recipeSize .kind
  have modeCap:=space.recipeSize .mode
  change 2*r≤p.kind.size at kindCap
  change 2*r≤p.mode.size at modeCap
  have ready:=recipes_installed p o ci cj packed space.recipeSize space.recipeWords
    (by omega) (by omega)
  refine ⟨?_,?_,?_⟩
  · intro u hu
    have kin : a.kind.base≤a.kind.base+u ∧ a.kind.base+u<a.kind.base+2*n := by omega
    have ptr : a.pointer.base≤a.pointer.base+u ∧ a.pointer.base+u<a.pointer.base+2*n := by omega
    have separate : ¬(a.kind.base≤a.pointer.base+u ∧ a.pointer.base+u<a.kind.base+2*n) := by omega
    rw [same (a.kind.base+u) (by omega) (by omega),same (a.pointer.base+u) (by omega) (by omega)]
    simp only [staticWords,mount,ite_eq_left kin,ite_eq_right separate,ite_eq_left ptr,and_self]
  · intro i
    exact ⟨(get .kind _).trans (ready i).1,(get .kind _).trans (ready i).2.1,
      (get .mode _).trans (ready i).2.2.1,(get .operand _).trans (ready i).2.2.2.1,
      (get .operand _).trans (ready i).2.2.2.2⟩
  · intro i j
    let q:Word w:=(8*i.val+j.val:ℕ)
    let x:=owners.base+q.val%owners.size
    have lo : owners.base≤x:=Nat.le_add_right ..
    have hi : x<owners.base+owners.size:=Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _
    have shelf : schedule x=packed x := by
      apply recipes_frame
      intro f
      have bounds:=border f
      have slots:=space.recipeSize f
      omega
    exact ((upper x (by omega) hi).trans shelf).trans
      (ownerAdvice_correct owners edges raw space.ownerWords space.ownerSize i j)

theorem economic_ports_end {p x y steps : ℕ} (E : EconomicHeader p x y steps) (ord : E.Ordered) :
    E.ports.stop≤E.stop := by
  have pt : E.payloadTree.stop≤E.stop:=ord.boughtTreeBase.le.trans (Nat.le_add_right ..)
  have ms : E.menus.stop≤E.stop:=ord.payloadTreeBase.le.trans ((Nat.le_add_right ..).trans pt)
  have bs : E.bought.stop≤E.stop:=ord.menusBase.le.trans ((EconomicHeader.Ordered.menu_bounds E ord).trans ms)
  have os : E.payload.stop≤E.stop:=ord.boughtBase.le.trans ((Nat.le_add_right ..).trans bs)
  have ss : E.scalar.stop≤E.stop:=ord.payloadBase.le.trans ((Nat.le_add_right ..).trans os)
  exact ord.scalarBase.le.trans ((Nat.le_add_right ..).trans ss)

variable {attempts R K H jobs phases X Y steps size : ℕ} {S : PurchaseSampler}

def masterWords (E : EconomicHeader phases X Y steps)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D) : Boot.Tape z D :=
  let extra:=staticWords a id amt p o ci cj owners edges raw
  let econ:=E.scalar.words (E.vectorMemory extra)
  JointHeader.words joint z D scores k phase π stock (E.ports.words (CoreRoute.low order M groups dir depth econ))

theorem master_authentic (E : EconomicHeader phases X Y steps)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D) (first : 2^z≤joint.initial) :
    ∀i : Fin (2^z),
      masterWords E order M groups dir joint scores depth phase π stock a id amt p o ci cj owners edges raw i.val=
        ((π i).val:Word _) :=
  JointHeader.authentic («N»:=scores) (k:=k) joint phase π stock _ first

theorem masterWords_rowOnly {count payload : ℕ} (c : Mesh) (history : Attempt→Entry count payload)
    (rows : Attempt→ℕ) (same : ∀t,(history t).rows=rows t) (idBase amountBase : Event→ℕ)
    (E : EconomicHeader phases X Y steps)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (a : ReserveUse.Archive)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D) :
    masterWords E order M groups dir joint scores depth phase π stock a
      (sourceAt c history idBase) (sourceAt c history amountBase) p o ci cj owners edges raw =
    masterWords E order M groups dir joint scores depth phase π stock a
      (rowOnly c rows idBase) (rowOnly c rows amountBase) p o ci cj owners edges raw := by
  simp only [masterWords,staticWords,mount_eq_rowOnly c history rows same idBase amountBase]

/-- A single actual subdivision installs the core/bought route readback, economic
account, two reserve-pointer columns, three fixed route recipes and packed
owners. The latter six banks are also physically readable at calendar checkout. -/
theorem master_start (E : EconomicHeader phases X Y steps) (ord : E.Ordered)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D) (v : Fin jobs→Market z D k)
    (layout : Boot.Layout v size) (sockets : BoughtSockets.Directory attempts)
    (space : StaticSpace a p owners n r edges (Native.wordBits z D Native.copies))
    (positive : 0<phases)
    (tail : E.stop≤a.kind.base) (wide : owners.base+owners.size<2^(Native.wordBits z D Native.copies))
    (tapeFit : owners.base+owners.size≤ size) (marketFit : ∀j,owners.base+owners.size≤Boot.low (v j))
    (first : 2^z≤joint.initial) (scoreEnd : JointHeader.stop joint z scores k phases≤E.ports.base)
    (heap : Native.heapEnd z D Native.copies≤E.ports.base)
    (board : CoreRoute.stop S z W k attempts depth K dir.groups H R≤joint.initial)
    (ports : CoreRoute.stop S z W k attempts depth K dir.groups H R≤E.ports.base) :
    let words:=masterWords E order M groups dir joint scores depth phase π stock a id amt p o ci cj owners edges raw
    let mid:=Boot.booted v size words
    (Native.subdivisionProgram z D).Exec (Boot.initial v size words) mid (Native.subdivisionConstant D*2^z) ∧
      Boot.Receipt v π (Computability.VPVNP.RAMMemory.initialMemory size words) mid ∧
      Seen order M groups dir sockets depth π mid ∧ E.Resident mid ∧ StaticAt a id amt p o ci cj owners edges raw mid ∧
      ∀{q goods : ℕ} (C : Chart (Native.wordBits z D Native.copies) q goods) (arena : Arena) (flag : ℕ),
        owners.base+owners.size≤arena.first → (flag<a.kind.base ∨ owners.base+owners.size≤flag) →
        (∀e x,x<arena.base C.mesh e → protected C x e) → mounted C (events C.mesh) mid →
        StaticAt a id amt p o ci cj owners edges raw (checkedOut C flag mid) := by
  intro words mid
  let extra:=staticWords a id amt p o ci cj owners edges raw
  let econ:=E.scalar.words (E.vectorMemory extra)
  let lowData:=CoreRoute.low order M groups dir depth econ
  have reserveOrder:=space.reserveOrder
  have routeStart:=space.routeStart
  have kindEnd:=space.kindEnd
  have modeEnd:=space.modeEnd
  have operandEnd:=space.operandEnd
  have upper : E.stop≤owners.base+owners.size := by omega
  have portStop:=economic_ports_end E ord
  have portStart : E.ports.base≤E.stop:=(Nat.le_add_right ..).trans portStop
  obtain ⟨ran,boot,seen,economic⟩:=economic_start E ord order M groups dir joint scores depth phase π stock extra
    v layout sockets positive (upper.trans_lt wide) (fun j=>upper.trans (marketFit j)) (upper.trans tapeFit)
    first scoreEnd heap board ports
  have same (x : ℕ) (lo : a.kind.base≤x) (hi : x<owners.base+owners.size) : mid x=extra x := by
    have old:=boot.kept x (heap.trans (portStart.trans (tail.trans lo)))
      (fun j hit=>(hi.trans_le (marketFit j)).not_ge hit.1)
    rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le tapeFit)] at old
    change mid x=JointHeader.words joint z D scores k phase π stock (E.ports.words lowData) x at old
    rw [JointHeader.tail_words _ _ _ _ _ _ first (scoreEnd.trans (portStart.trans (tail.trans lo))),
      E.ports.frame _ x (.inr (portStop.trans (tail.trans lo)))] at old
    calc
      mid x = lowData x := old
      _ = econ x := CoreRoute.low_above order M groups dir depth econ x
        (ports.trans (portStart.trans (tail.trans lo)))
      _ = extra x := E.tail_words ord extra x (tail.trans lo)
  refine ⟨ran,boot,seen,economic,staticAt a id amt p o ci cj owners edges raw mid space same,?_⟩
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
