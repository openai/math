import OAI.Hierarchy.DescentDonorNativeParts
import OAI.Hierarchy.DescentOrdinaryBornDigits

namespace OAI
/-! # The first marked donor issues all eight actual newborn supply counts -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentKernelHistory.BitDescription
open DescentRawCablePanel DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
    (group : J≃Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "groups" => group.toEmbedding
local notation "K" => 2^(k+1)
local notation "r" => 2^k
local notation "p" => 2*A.cap
local notation "names" => cableNames k rank
local notation "peers" => rotor A rank
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "C" => ScanColonies he A.stage
local notation "panel" => terrain (short:=short) A native S ready names win peers
local notation "real" => spread groups hosts panel
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ)
local notation "s" => shape r A.degree p profile
local notation "fieldsAt" => Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real)
local notation "seat" => slot he A groups hosts hm
variable (b : ℕ) (m : Memory w) (sumSize : (shape (2^k) A.degree (2*A.cap) profile).outputBits*M≤w)
    (stored : ∀i : Fin ((2^(k+1)*H)*chunks G M),
      m (b+i.val)=((topologyWords (M:=M) (shape (2^k) A.degree (2*A.cap) profile)
        (Gather.flat (Gather.descriptorInputs («K»:=2^(k+1)) (shape (2^k) A.degree (2*A.cap) profile) A.cap
          (spread group.toEmbedding hosts (terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank))))) i).val:Word w))
local notation "old" => colorPick W.graph W.core home color A.cap
local notation "nativeC" => normBits A.cap gadget.b gadget.C gadget.k
local notation "PairSet" => NativePair W.graph W.core home color A.cap
variable (choice : (A.stage.result he).Choice) (dest : ℕ) (issuedMem : Memory w)
local notation "selected" => (scannedRows he A.stage).profile choice


variable (roster : Fin H→Fin A.degree→Option (Fin H))
    (mounted : ∀(z : J×V) j,roster (hosts z.2) j=(rotor A rank z j).map (fun other=>hosts other.2))
    (hub : V→Bool) (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e)=scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "flag" => fun j=>if hv : ∃v,hosts v=j then hub hv.choose else false
local notation "P₀" => coloredPack W.graph W.core home color A.cap
local notation "key" => nativeKey W.graph W.core home color A.cap addr same lay
local notation "here" => fun h x=>resolved A.cap profile (panel h) lay x
local notation "adj" => fun h v x=>(peers h v).elim (0,0,0) (fun other=>here other x)
local notation "source" => DescentSharedCableNames.Stage.home A
local notation "S₀" => DescentSharedCableNames.Stage.outgoing A native S ready


open DescentOrdinaryBorn

include coord named fit winner df edgeOrder sumSize stored mounted same in
theorem issued_birth_donor
    (birth : ∀c : C,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=SixBirths.slot (seat c).2 j q
        SixBirths.atom A.stage.z (digit ((s).digit+1) ip.val (issuedMem (dest+(seat c).1.val)).val) ip.val=
          some (A.stage.z,DescentTerminalEpochFlags.encode (selected ⟨c,e⟩),q.val))


    (q : DescentSharedCableNames.Stage.Positive A) (slots bytes age : ℕ) (i : PairSet) (own : old (i,0)=q.val) :
    let u:=W.graph.src q.val
    let h:=A.pos u
    let s':=shapeOf (short:=short) A bytes
    let raw:=DepotRAM.chip s' A.cap profile gadget.b slots
      (nativeParts (short:=short) A native S ready rank win group hosts hm profile dest issuedMem roster hub lay bytes (hosts h.2) (group h.1))
    let donor:=chipDonor s' raw (finProdFinEquiv (A.block u,S₀ q))
    donor.first=true ∧ (∀e,(donor.supplyUnits e).val=((selected i).val e).val+gadget.k) ∧
    ∀grain z arg bits : ℕ,∀party : Fin 6,∀f : Fin 7,
      component bits (pointerAt gadget.b grain z donor party arg) f=
        field (actual gadget grain) bits f arg z (DescentPacking.PackedMatch.LayoutSum.profileCode gadget.C (selected i)).val party := by
  intro u h fmt raw donor
  have pd:=printed_seat A native S ready rank win he group hosts hm coord named fit winner df edgeOrder profile b m
    sumSize stored choice dest issuedMem roster mounted hub same lay birth q slots bytes age
  have rd : donor=measuredDonor (hCode:=age) A S ready old lay P₀ key (fun z=>hub z.2)
        slots selected (relative old lay P₀ key) q:=donor_at fmt raw _ _ pd
  have fi : DescentRawCablePanel.first old q.val=some i:=own ▸ first_pick old i
  have yes : donor.first=true:=by simp [rd,measuredDonor,fi]; rfl
  have numbers (e : Fin 8) : (donor.supplyUnits e).val=((selected i).val e).val+gadget.k:=by
    simp [rd,measuredDonor,fi,normalized]
    rfl
  refine ⟨yes,numbers,?_⟩
  intro grain z arg bits party f
  apply component_first (actual gadget grain) _ _ _ _ _ _ yes _ f
  intro e
  simpa only [actual,profile_read] using numbers e


include coord named fit winner df edgeOrder sumSize stored mounted same in
/-- Full rectangular field read, including unused actors, absent donors, and every
word past the genuine arity of an otherwise occupied birth node. -/
theorem issued_birth_mouths
    (birth : ∀c : C,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=SixBirths.slot (seat c).2 j q
        SixBirths.atom A.stage.z (digit ((s).digit+1) ip.val (issuedMem (dest+(seat c).1.val)).val) ip.val=
          some (A.stage.z,DescentTerminalEpochFlags.encode (selected ⟨c,e⟩),q.val))
    (slots bytes age : ℕ) (v : Fin H) (g : Fin G) (x : Fin r) (t : Fin A.cap) (grain z arg : ℕ) (party : Fin 6) :
    let fmt:=shapeOf (short:=short) A bytes
    let raw:=DepotRAM.chip fmt A.cap profile gadget.b slots
      (nativeParts (short:=short) A native S ready rank win group hosts hm profile dest issuedMem roster hub lay bytes v g)
    let xt:=finProdFinEquiv (x,t)
    let address:=(v,finProdFinEquiv (finProdFinEquiv (g,x),t))
    let owners:=oldSlot A S ready native hosts group
    let selectedAt : Option PairSet:=if h : ∃q,owners q=address then DescentRawCablePanel.first old h.choose.val else none
    pointerAt gadget.b grain z (chipDonor fmt raw xt) party arg =
      selectedAt.bind (fun i=>mouth (actual gadget grain) z
        (DescentPacking.PackedMatch.LayoutSum.profileCode gadget.C (selected i)).val party arg) := by
  intro fmt raw xt address owners selectedAt
  have received:=all_seats A native S ready rank win he group hosts hm coord named fit winner df edgeOrder profile b m
    sumSize stored choice dest issuedMem roster mounted hub same lay birth slots bytes age v g x t
  have rd:=donor_at fmt raw xt _ received
  rw [rd]
  by_cases occupied : ∃q,owners q=address
  · let e:=occupied.choose
    have actualRow : physicalRows (a:=bytes) («s»:=3) (hCode:=age) A S ready native hosts group old lay P₀ key (fun z=>hub z.2)
        slots selected (relative old lay P₀ key) v address.2=measuredDonor (hCode:=age) A S ready old lay
        P₀ key (fun z=>hub z.2) slots selected (relative old lay P₀ key) e := by
      unfold physicalRows
      erw [dite_eq_left occupied]
    have chosenAt : selectedAt = DescentRawCablePanel.first old e.val := by
      unfold selectedAt
      erw [dite_eq_left occupied]
      rfl
    rw [actualRow,chosenAt]
    cases picked : DescentRawCablePanel.first old e.val with
    | none =>
      simp [pointerAt,measuredDonor,picked]
      rfl
    | some i =>
      apply pointer_first (actual gadget grain) _ _ _ _ _
      · simp [measuredDonor,picked]
      · intro j
        simp [measuredDonor,picked,normalized,actual,profile_read]
  · have absent : selectedAt=none:=by simp [selectedAt,occupied]
    rw [absent]
    unfold physicalRows
    erw [dite_eq_right occupied]
    rfl

include coord named fit winner df edgeOrder sumSize stored mounted same in
theorem issued_birth_rows
    (birth : ∀c : C,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=SixBirths.slot (seat c).2 j q
        SixBirths.atom A.stage.z (digit ((s).digit+1) ip.val (issuedMem (dest+(seat c).1.val)).val) ip.val=
          some (A.stage.z,DescentTerminalEpochFlags.encode (selected ⟨c,e⟩),q.val))
    (slots bytes age : ℕ) (v : Fin H) (g : Fin G) (x : Fin r) (t : Fin A.cap) (grain z arg bits : ℕ) (party : Fin 6) (f : Fin 7) :
    let fmt:=shapeOf (short:=short) A bytes
    let raw:=DepotRAM.chip fmt A.cap profile gadget.b slots
      (nativeParts (short:=short) A native S ready rank win group hosts hm profile dest issuedMem roster hub lay bytes v g)
    let xt:=finProdFinEquiv (x,t)
    let address:=(v,finProdFinEquiv (finProdFinEquiv (g,x),t))
    let owners:=oldSlot A S ready native hosts group
    let selectedAt : Option PairSet:=if h : ∃q,owners q=address then DescentRawCablePanel.first old h.choose.val else none
    component bits (pointerAt gadget.b grain z (chipDonor fmt raw xt) party arg) f =
      selectedAt.elim 0 (fun i=>field (actual gadget grain) bits f arg z
        (DescentPacking.PackedMatch.LayoutSum.profileCode gadget.C (selected i)).val party) := by
  intro fmt raw xt address owners selectedAt
  have origin:=issued_birth_mouths A native S ready rank win he group hosts hm coord named fit winner df edgeOrder
    profile b m sumSize stored choice dest issuedMem roster mounted hub same lay birth slots bytes age v g x t grain z arg party
  change pointerAt gadget.b grain z (chipDonor fmt raw xt) party arg=selectedAt.bind _ at origin
  rw [origin]
  cases selectedAt <;> rfl

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
