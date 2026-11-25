import OAI.Hierarchy.DescentDonorFlatWords

namespace OAI
/-! # Every occupied register of the public donor window has its real physical coefficients -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentKernelHistory.BitDescription
open DescentRawCablePanel DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1000000
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


def shapeOf (a : ℕ) : DepotRAM.Shape := ⟨r,A.degree,A.cap,short,a,nativeC⟩

def physicalSigned (v : Fin H) (g : Fin G) (x : Fin r) (t : Fin p) : Cell (DescentSignedCableCodec.width A.degree A.cap) :=
  if hv : ∃u,hosts u=v then DescentSignedCableCodec.encode
    (DescentSharedCableNames.Stage.signedPanel A native S ready names ((group.symm g,hv.choose),x) t)
  else 0

theorem physical_signed_read (z : J×V) (x : Fin r) (t : Fin p) :
    physicalSigned A native S ready rank group hosts (hosts z.2) (group z.1) x t=DescentSignedCableCodec.encode
      (DescentSharedCableNames.Stage.signedPanel A native S ready names (z,x) t) := by
  have yes : ∃u,hosts u=hosts z.2:=⟨_,rfl⟩
  simp [physicalSigned]

def ordinalChart (h : Fin H) (j : Fin (breadth A.degree)) : Fin (breadth A.degree+1) :=
  ⟨observedRank roster h j,Nat.lt_succ_of_lt (Ranks.bound (Rebase.terminal roster) _ _)⟩
def hubChart (h : Fin H) (j : Fin (breadth A.degree)) : Fin (breadth A.degree+1) :=
  ⟨(observedHub roster h flag j).toNat,by
    have good : 0<breadth A.degree:=by unfold breadth;positivity
    cases observedHub roster h flag j <;> simp; omega⟩

def ownerWord (h : Fin H) (g : Fin G) :=
  Owners.render r A.degree p short A.cap profile (Owners.register lay (real h g))

def nativeParts (bytes : ℕ) (h : Fin H) (g : Fin G) : DepotRAM.Parts (shapeOf (short:=short) A bytes) :=
  let records:=physicalSigned A native S ready rank group hosts h g
  let old_:=Owners.registers (ownerWord (short:=short) A native S ready rank win group hosts profile lay) roster h g
  let fresh:=numericSupply s A.cap profile nativeC gadget.C gadget.k A.z hm (real h g) h g
  DepotRAM.operands _ lay (real h g) records old_ (ordinalChart A roster h) (hubChart (A:=A) (roster:=roster) (hosts:=hosts) (hub:=hub) h)
    (fun x t=>fresh x t K (topologyWords (M:=M) s fieldsAt) (fun j=>SixBirths.cut (SixBirths.width s M) (issuedMem (dest+j.val)).val))

private theorem oldRead (h : J×V) (x : Fin r) :
    Owners.addressed (ownerWord (short:=short) A native S ready rank win group hosts profile lay (hosts h.2) (group h.1)) x=here h x := by
  have hit : real (hosts h.2) (group h.1) = panel h := spread_hit groups hosts panel h
  rw [ownerWord,hit]
  exact Owners.addressed_read ..

private theorem noOwner (x : Fin r) :
    Owners.addressed («r»:=r) (D:=A.degree) (d:=short) 0 x=(0,0,0) := by
  have zero (a n : ℕ) : (encode a n).symm 0=(fun _=>0) := by
    apply (encode a n).symm_apply_eq.mpr
    symm;apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin n=>(0:Cell a))).val=0
    simp
  simp [Owners.addressed,zero]

include mounted in
private theorem peerRead (h : J×V) (i : Fin A.degree) (x : Fin r) :
    Owners.addressed ((Owners.registers (ownerWord (short:=short) A native S ready rank win group hosts profile lay)
      roster (hosts h.2) (group h.1)) i.succ) x=adj h i x := by
  simp only [Owners.registers,Fin.cases_succ,mounted]
  cases path_:peers h i with
  | none=>simp [noOwner]
  | some v=>
    have same_:=groups_preserved A rank path_
    simp only [Option.map_some,Option.elim_some]
    rw [←same_,oldRead]

include coord named fit winner df edgeOrder sumSize stored mounted in
theorem printed_seat
    (birth : ∀c : C,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=SixBirths.slot (seat c).2 j q
        SixBirths.atom A.stage.z (digit ((s).digit+1) ip.val (issuedMem (dest+(seat c).1.val)).val) ip.val=
          some (A.stage.z,DescentTerminalEpochFlags.encode (selected ⟨c,e⟩),q.val))


    (q : DescentSharedCableNames.Stage.Positive A) (slots bytes age : ℕ) :
    let u:=W.graph.src q.val
    let h:=A.pos u
    let s':=shapeOf (short:=short) A bytes
    (encode (bundleBits 3 bytes nativeC) (r*A.cap)).symm
      (DepotRAM.chip s' A.cap profile gadget.b slots
        (nativeParts A native S ready rank win group hosts hm profile dest issuedMem roster hub lay bytes (hosts h.2) (group h.1)))
      (finProdFinEquiv (A.block u,S₀ q))=
      packDonor (measuredDonor (hCode:=age) A S ready old lay P₀ key (fun z=>hub z.2) slots selected (relative old lay P₀ key) q) := by
  intro u h fmt
  have rr (z : J×V) (t) (y : J×V) (yes:peers z t=some y):roster (hosts z.2) t=some (hosts y.2) := by rw [mounted,yes];rfl
  have licensed:=depot_at A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder profile b m sumSize stored choice dest issuedMem
    roster rr hub same lay birth q slots bytes age
  let registers := Owners.registers (ownerWord (short:=short) A native S ready rank win group hosts profile lay) roster (hosts h.2) (group h.1)
  let fresh := numericSupply s A.cap profile nativeC gadget.C gadget.k A.z hm (real (hosts h.2) (group h.1)) (hosts h.2) (group h.1)
  refine (DepotRAM.printed_parts (shapeOf (short:=short) A bytes) A.cap profile gadget.b slots lay
    (real (hosts h.2) (group h.1)) (physicalSigned A native S ready rank group hosts (hosts h.2) (group h.1)) registers
    (ordinalChart A roster (hosts h.2)) (hubChart (A:=A) (roster:=roster) (hosts:=hosts) (hub:=hub) (hosts h.2))
    (fun x t => fresh x t K (topologyWords (M:=M) s fieldsAt)
      (fun j=>SixBirths.cut (SixBirths.width s M) (issuedMem (dest+j.val)).val))
    (A.block u) (S₀ q)).trans ?_
  dsimp only [registers,fresh,shapeOf]
  have own (x : Fin r) : Owners.addressed (Owners.registers (ownerWord (short:=short) A native S ready rank win group hosts profile lay)
      roster (hosts h.2) (group h.1) 0) x=here h x := oldRead A native S ready rank win group hosts profile lay h x
  have peers_:=peerRead (short:=short) A native S ready rank win group hosts profile roster mounted lay h
  have tap (w : Walk) : (⟨(ordinalChart A roster (hosts h.2) (ActorPath.index A.degree w)).val,
        decide ((hubChart (A:=A) (roster:=roster) (hosts:=hosts) (hub:=hub) (hosts h.2) (ActorPath.index A.degree w)).val=1),w.2.2.1,w.2.2.2⟩ : LocalActor)=
      readWalk roster (hosts h.2) flag w := by
    have bool (v : Bool) : decide (v.toNat=1)=v := by cases v <;> rfl
    exact congrArg (fun b => LocalActor.mk (observedRank roster (hosts h.2) (ActorPath.index A.degree w)) b w.2.2.1 w.2.2.2)
      (bool (observedHub roster (hosts h.2) flag (ActorPath.index A.degree w)))
  have hit : real (hosts h.2) (group h.1) = panel h := spread_hit groups hosts panel h
  have sig := funext (physical_signed_read A native S ready rank group hosts h (A.block u))
  have peer := funext (fun i => funext (peers_ i))
  have measure := funext (measured_seat A native S ready rank win he groups hosts hm fit winner profile dest issuedMem q)
  have supply := (congrArg (fun p₀ => numericSupply s A.cap profile nativeC gadget.C gadget.k A.z hm p₀
    (hosts h.2) (group h.1) (A.block u) (S₀ q) K (topologyWords (M:=M) s fieldsAt)
    (fun j=>SixBirths.cut (SixBirths.width s M) (issuedMem (dest+j.val)).val)) hit).trans measure
  refine Eq.trans ?_ (congrArg packDonor licensed)
  apply congrArg packDonor
  congr 1 <;> first | exact hit | exact sig | exact funext tap | exact funext own

/-- The fixed raster is retained for every padded host. An absent genuine
donor forces a zero grain count even on an occupied vertex with empty ports. -/
theorem source_empty (v : Fin H) (g : Fin G) (x : Fin r) (t : Fin A.cap)
    (vacant : ¬∃q : DescentSharedCableNames.Stage.Positive A,
      oldSlot A S ready native hosts group q=(v,finProdFinEquiv (finProdFinEquiv (g,x),t))) :
    DescentSharedCableNames.Stage.sourceGrains (physicalSigned A native S ready rank group hosts v g x) t=0 := by
  by_cases occupied : ∃u,hosts u=v
  · obtain ⟨u,rfl⟩:=occupied
    have old_ : physicalSigned A native S ready rank group hosts (hosts u) g x=fun slot=>
        DescentSignedCableCodec.encode (DescentSharedCableNames.Stage.signedPanel A native S ready names ((group.symm g,u),x) slot) := by
      funext j;simpa using physical_signed_read A native S ready rank group hosts (group.symm g,u) x j
    rw [old_]
    by_contra positive
    obtain ⟨q,here_,bit⟩:=(DescentSharedCableNames.Stage.source_live A native S ready names ((group.symm g,u),x) t).mp
      (Nat.pos_of_ne_zero positive)
    apply vacant
    refine ⟨q,?_⟩
    have coords:=congrArg Prod.fst here_
    have bx:=congrArg Prod.snd here_
    change A.block (W.graph.src q.val)=x at bx
    change A.pos (W.graph.src q.val)=(group.symm g,u) at coords
    change (hosts (A.pos (W.graph.src q.val)).2,finProdFinEquiv
      (finProdFinEquiv (group (A.pos (W.graph.src q.val)).1,A.block (W.graph.src q.val)),S₀ q))=_
    simp only [coords,bx,bit,Equiv.apply_symm_apply]
  · have zeros : physicalSigned A native S ready rank group hosts v g x=fun _=>0 := by
      funext j
      exact dite_eq_right occupied
    rw [zeros]
    have clear : DescentSignedCableCodec.decode A.degree A.cap 0=none := by
      simpa only [DescentSignedCableCodec.empty] using DescentSignedCableCodec.decode_encode (none:Option (DescentSharedCableNames.Stage.Live A.degree A.cap))
    simp [DescentSharedCableNames.Stage.sourceGrains,clear,DescentSharedCableNames.Stage.atSource]

include coord named fit winner df edgeOrder sumSize stored mounted in
theorem all_seats
    (birth : ∀c : C,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=SixBirths.slot (seat c).2 j q
        SixBirths.atom A.stage.z (digit ((s).digit+1) ip.val (issuedMem (dest+(seat c).1.val)).val) ip.val=
          some (A.stage.z,DescentTerminalEpochFlags.encode (selected ⟨c,e⟩),q.val))
    (slots bytes age : ℕ) (v : Fin H) (g : Fin G) (x : Fin r) (t : Fin A.cap) :
    let fmt:=shapeOf (short:=short) A bytes
    (encode (bundleBits 3 bytes nativeC) (r*A.cap)).symm
      (DepotRAM.chip fmt A.cap profile gadget.b slots
        (nativeParts A native S ready rank win group hosts hm profile dest issuedMem roster hub lay bytes v g))
      (finProdFinEquiv (x,t))=
        packDonor (physicalRows (hCode:=age) A S ready native hosts group old lay P₀ key (fun z=>hub z.2)
          slots selected (relative old lay P₀ key) v (finProdFinEquiv (finProdFinEquiv (g,x),t))) := by
  intro fmt
  let index:=oldSlot A S ready native hosts group
  by_cases hit : ∃q,index q=(v,finProdFinEquiv (finProdFinEquiv (g,x),t))
  · obtain ⟨q,hq⟩:=hit
    have vEq:=congrArg Prod.fst hq
    have vs:=finProdFinEquiv.injective (congrArg Prod.snd hq)
    have gx:=finProdFinEquiv.injective (congrArg Prod.fst vs)
    have gEq:=congrArg Prod.fst gx
    have xEq:=congrArg Prod.snd gx
    have tEq:=congrArg Prod.snd vs
    let u:=W.graph.src q.val
    change hosts (A.pos u).2=v at vEq
    change group (A.pos u).1=g at gEq
    change A.block u=x at xEq
    change S₀ q=t at tEq
    subst v;subst g;subst x;subst t
    refine (printed_seat A native S ready rank win he group hosts hm coord named fit winner df edgeOrder profile b m sumSize stored choice dest issuedMem
      roster mounted hub same lay birth q slots bytes age).trans ?_
    exact congrArg packDonor (occupied_read (a:=bytes) (hCode:=age) A S ready native hosts group old lay
      P₀ key (fun z=>hub z.2) slots selected (relative old lay P₀ key) q).symm
  · have zero:=source_empty A native S ready rank group hosts v g x t hit
    refine (DepotRAM.printed_parts (shapeOf (short:=short) A bytes) A.cap profile gadget.b slots lay
      (real v g) (physicalSigned A native S ready rank group hosts v g)
      (Owners.registers (ownerWord (short:=short) A native S ready rank win group hosts profile lay) roster v g)
      (ordinalChart A roster v) (hubChart (A:=A) (roster:=roster) (hosts:=hosts) (hub:=hub) v)
      (fun y z => numericSupply s A.cap profile nativeC gadget.C gadget.k A.z hm (real v g) v g y z K
        (topologyWords (M:=M) s fieldsAt) (fun j=>SixBirths.cut (SixBirths.width s M) (issuedMem (dest+j.val)).val)) x t).trans ?_
    apply congrArg packDonor
    refine Eq.trans (b:=emptyDonor 3 bytes nativeC) ?_ ?_
    · exact ite_eq_left zero
    · unfold physicalRows
      split
      · rename_i present
        exact False.elim (hit present)
      · rfl

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
