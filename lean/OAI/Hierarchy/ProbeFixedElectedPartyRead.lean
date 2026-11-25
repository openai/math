import OAI.Hierarchy.ProbeFixedElectedPartyCircuit
import OAI.Hierarchy.TaggedWideCalendarPartyRead
import OAI.Hierarchy.TaggedWideSpillFieldRoom

namespace OAI
/-! # Native value of an actually selected signed party in the complete menu -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Strip
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets PurchaseStage ReportSockets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open WireTelescope ChosenPackets ChosenPackets.RowRouting PacketTurns
open scoped Classical Fin.CommRing

namespace FixedProtocolFormat.ElectedSource
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} {v : FixedProtocolFormat F k p q Q σ Λ}
    {h width : ℕ}
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "W" => wordBits h D copies
local notation "days" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "K" => siteLast h D k+1
local notation "fs" => v.nativeFormats P h width
local notation "b" => (P).catalogue
local notation "sig" => (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet
local notation "name" => (siteNumber h D k).toEmbedding
variable {π : Equiv.Perm (Fin (2^h))}
    {mark : Marks h v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)}
    {ends : Fin (v.widePlacement h width).catalogue.rows → Site h (2^v.W) k × Site h (2^v.W) k}
    {m : Memory (Native.wordBits h (2^v.W) Native.copies)} {a : Attempt} {i : ℕ}
    (z : v.ElectedSource h width π mark ends m a i) (at₀ : v.widePacketMenuIndex h a)
    (rt : Fin (v.wideBallotParties h a)) (pad : Chord (siteLast h (2^v.W) k+1)) (siteROM : ℕ)
local notation "fd" => v.wideFields P h width siteROM (.attempt a)
local notation "mass" => (fs a).histMass
local notation "R" => z.routing at₀ rt mass pad
local notation "phys" => installedRows π ends name pad

open HistoryRoles
local notation "M" => v.widePacketRoles h
local notation "degree" => v.widePacketDegree
local notation "roles" => Fintype.card (R).Roles
local notation "before" => (v.wideBallotShape P h width (.attempt a)).columns
local notation "middle" => PacketTurns.middleColumns M
local notation "J" => v.wideBallotParties h a
local notation "op" => z.operands at₀ rt pad siteROM

open PassMatrix PartyPins Probe Tagged
open LinearAlgebra.SpectralBooks.SiteTensor
variable {V : Type} [Fintype V]
local notation "Q₀" => z.placed at₀ rt
local notation "i₀" j => Fin.cast (z.parties at₀ rt).symm j
local notation "old" => (v.wideBallotShape P h width (.attempt a)).columns


open ThreeFlat Routing Diagonal TraceWords
open TurnShelf CalendarTape
variable (unitCost selectorBits : ℕ) (stride : Bank) (preStart postStart : ℕ) (j : Fin (v.wideBallotParties h a))
    (read : ℕ→ℕ→V⊕Bool) (env : V→Bool) (mem : Memory (Native.wordBits h (2^v.W) Native.copies))
    (arg : Word (Native.wordBits h (2^v.W) Native.copies))
local notation "site" => (Q₀).place (i₀ j)
local notation "here" => v.wideBallotSite P h width siteROM a j
local notation "fields" => v.widePacketFields h width selectorBits (.attempt a) siteROM stride preStart postStart
local notation "sheet" f => DatedRoleSheets.bank (v.widePacketPhysical h width) postStart (v.widePacketShelf h) selectorBits f
local notation "price" => pageRead (sheet 0) stride here (d:=degree)
local notation "other" => pageRead (sheet 2) stride here (d:=degree)
local notation "ord" => (R).order
local notation "route" => (R).install.steps ord
local notation "ends₀" => Installs.starts (source:=(R).source) ord
local notation "p₀" => v.partyRoleBits h
local notation "e₀" => v.partyLaneBits h width a unitCost
local notation "keys₀" => v.partyKeyBits
local notation "cap" => v.wideNeighborCap width unitCost
local notation "slab" => 2^e₀
local notation "inputValue" => (fun n bit => Sum.elim env id (read n bit))
variable (c : Histogram (Fin (z.placed at₀ rt).data.terms) ((v.nativeFormats (v.widePlacement h width) h width a).histMass))
local notation "weights" => Installs.numbered ord ((R).bits c)
variable {n : ℕ} (rest : Widths (siteLast h (2^v.W) k+1)) (gs : Fin n→Widths (siteLast h (2^v.W) k+1)) (pick : Fin n)
local notation "total" => fun q : (portGraph K).Port site=>(rest+∑t,gs t) q.val.1
variable (parts : PassiveWindow.Parts
    ((portGraph (siteLast h (2^v.W) k+1)).Port ((z.placed at₀ rt).place (Fin.cast (z.parties at₀ rt).symm j)))
    (Fin v.widePacketDegree) (v.wideNeighborCap width unitCost) (fun q => (rest + ∑ t, gs t) q.val.1))
    (beforeBits afterBits : Fin v.widePacketDegree × Fin (v.wideNeighborCap width unitCost) → Bool)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8192 in
/-- The hardware lookup evaluates the original elected row using its true
posted native columns, before and after the signed intermediate contraction. -/
theorem selected_value (shape : gs pick=(R).post c) (away : ∀u,u≠pick→Subsingleton (State (gs u) site))
    (x : State ((Q₀).wants mass) site) (z' : State (rest+∑u,gs u) site)
    (geom : PacketTurns.Reads ends₀ phys route weights op mem arg)
    (atSite : (here).eval mem arg=((site).val:Word W)) (sitesFit : K≤2^W)
    (rowsFit : Fintype.card (Commodity (Fin (2^h)) N k)+(b).rows≤2^W)
    (mounted : PacketTurns.NeighborReads mem arg parts price other)
    (field : ∀ (col : Fin (v.widePacketShape h width (.attempt a)).columns) (bit : ℕ), inputValue col.val bit = (((fields).value j col).eval mem arg).val.testBit bit)
    (roleRoom : 2^p₀≤2^W) (wordRoom : slab<2^W)
    (postBound : ∀e,(R).post c e≤ slab)
    (top : ∀q,total q≤cap)
    (afterRead : ∀q d,afterBits (q,d)=ChordAperture.canonical parts (fun p k=>(z' p).val.testBit k) q d)
    (key : Fin (Q₀).sites→Word keys₀)
    (keys : ∀u d,inputValue (socketStart old M degree+u.val) d.val=bits (key u) d)
    (counters : ∀t (d:Fin (Nat.clog 2 (mass+1))),inputValue (2+t.val) d.val=SelectorShelf.bits c _ t d)
    (wanted : ∀t (d:Fin slab),Sum.elim beforeBits id
      (PacketNeighbor.wantedSocket ((Q₀).data.inputWidths mass) (i₀ j) key id t d)=
      ((PhysicalMatrix.read (Q₀).place _ (i₀ j) (cast (congrArg (fun U=>State U site) (Q₀).placedInput.symm) x)) t).val.testBit d.val) :
    let y:=cast (congrArg (fun U=>State U site) shape)
      (blockPortState gs site ((splitPortState rest (∑u,gs u) site z').2) pick)
    TypedWiring.value (v.signedPartyAt h width a cap p₀ e₀ keys₀ read at₀ j)
      (Sum.elim (Sum.elim env beforeBits) afterBits)=(R).entry c site x y := by
  intro y
  have fuel : mass*(Q₀).data.partyUnit (Q₀).Tree≤ slab :=
    (Nat.mul_le_mul_left mass (z.selected_fuel at₀ rt)).trans (v.party_lane_room h width a unitCost).2.le
  have offer (edge : Chord K) : (Q₀).offers c edge≤ slab := by
    rw [←(Q₀).placedOutput c]
    by_cases h:edge∈Set.range (physicalChord (Q₀).place)
    · obtain ⟨q,rfl⟩:=h
      rw [PhysicalMatrix.width_at]
      let face : (portGraph (Q₀).sites).Port ((portGraph (Q₀).sites).vertex q false):=⟨(q,false),rfl⟩
      exact ((Q₀).data.unit_middle (Q₀).graph _ face c).trans fuel
    · rw [PhysicalMatrix.width_away _ _ h]
      exact Nat.zero_le _
  have sourceFit (u : Fin roles) : installedWidths ends₀ weights (ends₀ u)≤ slab := by
    rw [Installs.packed (source:=(R).source),(R).shape]
    exact offer _
  have oldFit (u : Fin roles) : weights u≤ slab := by
    by_cases positive:0<weights u
    · exact (Nat.le_add_left _ _).trans ((datedBase_room ends₀ weights u positive).trans (sourceFit u))
    · exact (Nat.eq_zero_of_not_pos positive).le.trans (Nat.zero_le _)
  have room (u) : ChordAperture.room (Middle.parts R c site slab oldFit) u<2^(e₀+1) := by
    rw [Middle.room_fields]
    have bound:=offer (ends₀ u.1)
    have pos:0<slab:=Nat.two_pow_pos _
    have extra : slab < 2^(e₀+1) := by rw [Nat.pow_succ]; omega
    split
    · exact bound.trans_lt extra
    · exact pos.trans extra
  have loadFit (u) : installedWidths phys (routeLoad route weights) (phys u)≤ slab := by
    rw [(R).install.counted ord ((R).bits c)]
    exact postBound _
  obtain ⟨tap,edges,fit,aligned,chosen⟩:=z.menu_circuit (V:=V) at₀ rt pad j
  rw [chosen]
  apply native_circuit_read Q₀ c R (i₀ j) tap edges fit old (z.roles_fit at₀ rt pad) read env
    beforeBits afterBits rest gs pick parts oldFit shape away x z' (z.short_walks at₀ rt pad) (Fintype.equivFin (Positions route)).symm
    top _ loadFit (fun t=>(oldFit t).trans_lt wordRoom) op mem arg here price other atSite geom
    sitesFit rowsFit mounted _ afterRead roleRoom wordRoom.le aligned (fun q=>offer q.val.1) room sourceFit wordRoom
    _ _ key keys counters wanted
  · have small:=z.roles_fit at₀ rt pad
    have big:=v.party_role_room h
    omega
  · intro t f
    exact z.turn_bit at₀ rt pad siteROM selectorBits stride preStart postStart j mem arg
      inputValue field t (projection f).1 (projection f).2
  · intro f bit
    let l:=PacketTurns.middleNumber M (PacketTurns.Operands.middleLift (z.roles_fit at₀ rt pad) f)
    let offset := socketStart old M degree + J
    have readColumn := field (Fin.natAdd offset l) bit
    have expression := (v.widePacket_middle h width selectorBits siteROM stride preStart postStart a j l).trans
      (congrFun (z.middle_column at₀ rt pad siteROM j) l)
    have posted := readColumn.trans (congrArg (fun e : Expr => (e.eval mem arg).val.testBit bit) expression)
    have sameSite : (fd).site j = here := by cases a <;> rfl
    simpa only [middleStart, Fin.val_natAdd, offset, z.parties at₀ rt, sameSite, l] using posted
  · intro q
    exact (((Q₀).data.unit_room (Q₀).graph (i₀ j) q mass).trans
      (Nat.mul_le_mul_left mass (z.selected_fuel at₀ rt))).trans (v.party_lane_room h width a unitCost).2.le

end FixedProtocolFormat.ElectedSource
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
