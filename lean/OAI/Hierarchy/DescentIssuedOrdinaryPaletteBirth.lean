import OAI.Hierarchy.DescentOrdinaryPaletteBirth
import OAI.Hierarchy.DescentOrdinaryBornDonor

namespace OAI
/-! # The issued marked donor's newborn word is its genuine global coefficient token -/
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


open DescentOrdinaryBorn DescentOrdinaryPaletteBirth DescentPrimitivePalette

include coord named fit winner df edgeOrder sumSize stored mounted same in
theorem issued_palette_birth
    (birth : ∀c : C,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=SixBirths.slot (seat c).2 j q
        SixBirths.atom A.stage.z (digit ((s).digit+1) ip.val (issuedMem (dest+(seat c).1.val)).val) ip.val=
          some (A.stage.z,DescentTerminalEpochFlags.encode (selected ⟨c,e⟩),q.val))


    (q : DescentSharedCableNames.Stage.Positive A) (slots bytes age : ℕ) (i : PairSet) (own : old (i,0)=q.val)
    (seed Z : ℕ) (op : RotorSpec) (z : ℕ) (under : z≤Z) (party : Fin 6) :
    let u:=W.graph.src q.val
    let h:=A.pos u
    let s':=shapeOf (short:=short) A bytes
    let raw:=DepotRAM.chip s' A.cap profile gadget.b slots
      (nativeParts (short:=short) A native S ready rank win group hosts hm profile dest issuedMem roster hub lay bytes (hosts h.2) (group h.1))
    let donor:=chipDonor s' raw (finProdFinEquiv (A.block u,S₀ q))
    DescentOrdinaryPaletteBirth.word gadget seed Z op z donor party=
      DescentPrimitivePalette.token gadget seed Z op (.inr (.inl (⟨z,Nat.lt_succ_of_le under⟩,selected i,party))) :=by
  intro u h fmt raw donor
  have saved:=issued_birth_donor A native S ready rank win he group hosts hm coord named fit winner df edgeOrder profile b m
    sumSize stored choice dest issuedMem roster mounted hub same lay birth q slots bytes age i own
  exact word_genuine gadget seed Z op z donor party (selected i) under saved.1 saved.2.1

include coord named fit winner df edgeOrder sumSize stored mounted same in
theorem issued_palette_rows
    (birth : ∀c : C,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=SixBirths.slot (seat c).2 j q
        SixBirths.atom A.stage.z (digit ((s).digit+1) ip.val (issuedMem (dest+(seat c).1.val)).val) ip.val=
          some (A.stage.z,DescentTerminalEpochFlags.encode (selected ⟨c,e⟩),q.val))
    (slots bytes age : ℕ) (v : Fin H) (g : Fin G) (x : Fin r) (t : Fin A.cap) (seed Z : ℕ) (op : RotorSpec) (z : ℕ) (under : z≤Z) (party : Fin 6) :
    let fmt:=shapeOf (short:=short) A bytes
    let raw:=DepotRAM.chip fmt A.cap profile gadget.b slots
      (nativeParts (short:=short) A native S ready rank win group hosts hm profile dest issuedMem roster hub lay bytes v g)
    let xt:=finProdFinEquiv (x,t)
    let address:=(v,finProdFinEquiv (finProdFinEquiv (g,x),t))
    let owners:=oldSlot A S ready native hosts group
    let selectedAt : Option PairSet:=if h : ∃q,owners q=address then DescentRawCablePanel.first old h.choose.val else none
    DescentOrdinaryPaletteBirth.word gadget seed Z op z (chipDonor fmt raw xt) party =
      selectedAt.elim 0 (fun i=>DescentPrimitivePalette.token gadget seed Z op
        (.inr (.inl (⟨z,Nat.lt_succ_of_le under⟩,selected i,party)))) :=by
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
      simp [DescentOrdinaryPaletteBirth.word,measuredDonor,picked]
      rfl
    | some i =>
      apply word_genuine gadget seed Z op z _ party (selected i) under
      · simp [measuredDonor,picked]
      · intro j
        simp [measuredDonor,picked,normalized]
  · have absent : selectedAt=none:=by simp [selectedAt,occupied]
    rw [absent]
    unfold physicalRows
    erw [dite_eq_right occupied]
    rfl

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
