import OAI.Hierarchy.DescentResetOrdinalParts
import OAI.Hierarchy.DescentResetDyadicOrder
import OAI.Hierarchy.DescentNativeResetEdgeTape
import OAI.Hierarchy.DescentOrderedGrainPrecedence

namespace OAI
/-! # Authentic reset-parent comparisons without forming the global parent address -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentOrderedReset DescentCableUnbundling DescentStageEdgeReceipt
open ThreeFlat.RAM Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
variable {U N : ℕ} (vertex : Z.V↪Fin U) (key : A.graph.Edge↪Fin N)
local notation "W" => reenter Z T
local notation "Y" => (2^Z.n:ℕ)
local notation "partsLayout" => DescentResetCableSlots.originalLayout N U Z.k Y Ht
  (max (Fintype.card (Computability.BorderVNP.Crossing.Network.Edge (DescentCommonPalette.rotor Z.graph))) (2^(Ht+1)))

def installedParts (e : (W).graph.Edge) : (partsLayout).Value :=
  let named:=installedWireNames A T.home Z.placement.input T.hub
    (funext fun j => (Z.allWidths j).symm) Z.bank Z.tables e
  DescentResetCableSlots.originParts Z.placement vertex T.code (fun t=>(T.codeLegal t).2)
    Ht T.bookHeight Z.graph Z.positive Z.pay Z.circuit d key named

theorem installed_parts_before (x y : (W).graph.Edge) :
    (partsLayout).before (installedParts Z T vertex key x) (installedParts Z T vertex key y) ↔
      installedResetOrdinal Z T vertex key x < installedResetOrdinal Z T vertex key y := by
  let names := installedWireNames A T.home Z.placement.input T.hub
    (funext fun j => (Z.allWidths j).symm) Z.bank Z.tables
  exact DescentResetCableSlots.originParts_before Z.placement vertex T.code (fun t=>(T.codeLegal t).2)
    Ht T.bookHeight Z.graph Z.positive Z.pay Z.circuit d key (names x) (names y)

/-- Compaction renumbers the actual interval catalogue but preserves its
original tag order. -/
theorem issued_interval_lt {k : ℕ} (u v : ↥(DescentHostDirectory.codes k)) :
    DescentResetCableSlots.interval k u<DescentResetCableSlots.interval k v ↔
      Nat.pair u.val.1 u.val.2<Nat.pair v.val.1 v.val.2 := by
  let id:=((Function.Embedding.subtype (·∈DescentHostDirectory.codes k)).trans Nat.pairEquiv.toEmbedding)
  change ProtocolRAMPortRanks.«prefix» (fun _=>1) id u+0<
    ProtocolRAMPortRanks.«prefix» (fun _=>1) id v+0 ↔ id u < id v
  simpa only [Nat.add_zero] using DescentOrderedGrainPrecedence.first
    (fun _=>1) id u v (by decide) (by decide)

/-- Comparing two actual full terminal names at the same coarse group reads
a host digit, a bounded relative interval, the coarse-zero bit and the
optional registered socket. Public depth enters only the table definition. -/
theorem emitted_interval_before (u v : Z.Fallback)
    (group : DescentChosenRouter.coarseName T.commonDepth (T.code u)=
      DescentChosenRouter.coarseName T.commonDepth (T.code v)) :
    let a:=T.code u
    let b:=T.code v
    let c:=DescentChosenRouter.coarseName T.commonDepth a
    let la:=DescentRelativeContacts.shortName T.commonDepth a
    let lb:=DescentRelativeContacts.shortName T.commonDepth b
    DescentResetCableSlots.interval Z.k ⟨a.2.1,DescentHostDirectory.mem_codes (T.codeLegal u).2.1 (T.codeLegal u).2.2⟩<
      DescentResetCableSlots.interval Z.k ⟨b.2.1,DescentHostDirectory.mem_codes (T.codeLegal v).2.1 (T.codeLegal v).2.2⟩ ↔
        DescentResetDyadicOrder.before T.commonDepth (decide (c=0)) la.2.1.1 la.2.1.2 lb.2.1.1 lb.2.1.2 := by
  dsimp only
  rw [issued_interval_lt]
  have x:=DescentResetDyadicOrder.raw_reconstruct T.commonDepth (T.code u).2.1.1 (T.code u).2.1.2 (T.codeLegal u).1
  have y:=DescentResetDyadicOrder.raw_reconstruct T.commonDepth (T.code v).2.1.1 (T.code v).2.1.2 (T.codeLegal v).1
  rw [←x,←y]
  change DescentResetDyadicOrder.raw T.commonDepth (DescentChosenRouter.coarseName T.commonDepth (T.code u)) _ _<
    DescentResetDyadicOrder.raw T.commonDepth (DescentChosenRouter.coarseName T.commonDepth (T.code v)) _ _ ↔ _
  rw [←group]
  exact DescentResetDyadicOrder.raw_before _ _ _ _ _ _
    (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))

/-- The ordering of the two relative interval columns in the physical
terminal operand.  The exceptional coarse-zero flag is shared by that
receiver's entire census. -/
def relativeInterval (zero : Bool) (u v : Z.Fallback) : Prop :=
  let a:=DescentRelativeContacts.shortName T.commonDepth (T.code u)
  let b:=DescentRelativeContacts.shortName T.commonDepth (T.code v)
  DescentResetDyadicOrder.before T.commonDepth zero a.2.1.1 a.2.1.2 b.2.1.1 b.2.1.2

/-- Terminal operand after replacing its original host by its small halo
rank.  The optional socket remains its actual registered local number. -/
def localTerminalBefore (zero : Bool) (hostU hostV : Nat) (u v : Z.Fallback) : Prop :=
  hostU<hostV ∨ hostU=hostV ∧
    (relativeInterval Z T zero u v ∨
      (¬relativeInterval Z T zero u v ∧ ¬relativeInterval Z T zero v u) ∧
        DescentResetCableSlots.optional (T.code u).2.2<DescentResetCableSlots.optional (T.code v).2.2)

theorem terminal_local_before (u v : Z.Fallback) (hostU hostV : Nat)
    (lower : hostU<hostV ↔ vertex (T.code u).1<vertex (T.code v).1)
    (equal : hostU=hostV ↔ vertex (T.code u).1=vertex (T.code v).1)
    (group : DescentChosenRouter.coarseName T.commonDepth (T.code u)=
      DescentChosenRouter.coarseName T.commonDepth (T.code v)) :
    localTerminalBefore Z T (decide (DescentChosenRouter.coarseName T.commonDepth (T.code u)=0))
        hostU hostV u v ↔
      (DescentResetCableSlots.termLayout U Z.k Y).before
        (DescentResetCableSlots.terminalDigits vertex T.code (fun t=>(T.codeLegal t).2) u)
        (DescentResetCableSlots.terminalDigits vertex T.code (fun t=>(T.codeLegal t).2) v) := by
  let zero:=decide (DescentChosenRouter.coarseName T.commonDepth (T.code u)=0)
  let cell (t : Z.Fallback):=DescentResetCableSlots.interval Z.k
    ⟨(T.code t).2.1,DescentHostDirectory.mem_codes (T.codeLegal t).2.1 (T.codeLegal t).2.2⟩
  have uv : cell u<cell v ↔ relativeInterval Z T zero u v:=emitted_interval_before Z T u v group
  have vu : cell v<cell u ↔ relativeInterval Z T zero v u:=by
    have h:=emitted_interval_before Z T v u group.symm
    dsimp only at h
    rw [←group] at h
    exact h
  have tie : (¬relativeInterval Z T zero u v ∧ ¬relativeInterval Z T zero v u) ↔ cell u=cell v:=by
    rw [←uv,←vu]
    exact ⟨fun h=>le_antisymm (le_of_not_gt h.2) (le_of_not_gt h.1),
      fun h=>by rw [h];exact ⟨lt_irrefl _,lt_irrefl _⟩⟩
  let socket (t : Z.Fallback) := DescentResetCableSlots.optional (T.code t).2.2
  change (hostU<hostV ∨ hostU=hostV ∧ (relativeInterval Z T zero u v ∨
    (¬relativeInterval Z T zero u v ∧ ¬relativeInterval Z T zero v u) ∧ socket u<socket v)) ↔
    (vertex (T.code u).1<vertex (T.code v).1 ∨ vertex (T.code u).1=vertex (T.code v).1 ∧
      (cell u<cell v ∨ cell u=cell v ∧ socket u<socket v))
  rw [lower,equal,tie,←uv]

/-- The two equal host ranks identify the same physical old host, so the two
good-site block addresses have the same absolute depth. Their order is the
order of the bounded remainders in the common coarse group. -/
theorem base_local_before (a b : Z.placement.Good) (hostA hostB : Nat)
    (lower : hostA<hostB ↔ vertex a.val.1<vertex b.val.1)
    (equal : hostA=hostB ↔ vertex a.val.1=vertex b.val.1)
    (group : a.val.2.val/2^(Z.placement.b a.val.1-T.commonDepth)=
      b.val.2.val/2^(Z.placement.b b.val.1-T.commonDepth)) :
    (hostA<hostB ∨ hostA=hostB ∧ a.val.2.val%2^(Z.placement.b a.val.1-T.commonDepth)<
        b.val.2.val%2^(Z.placement.b b.val.1-T.commonDepth)) ↔
      (DescentResetCableSlots.goodLayout U Z.k).before (DescentResetCableSlots.baseDigits Z.placement vertex a)
        (DescentResetCableSlots.baseDigits Z.placement vertex b) := by
  change _ ↔ vertex a.val.1<vertex b.val.1 ∨ vertex a.val.1=vertex b.val.1 ∧ a.val.2.val<b.val.2.val
  rw [lower,equal]
  by_cases same : vertex a.val.1=vertex b.val.1
  · have h:=vertex.injective same
    have exp : 2^(Z.placement.b a.val.1-T.commonDepth)=2^(Z.placement.b b.val.1-T.commonDepth):=by rw [h]
    rw [exp] at group ⊢
    let q:=2^(Z.placement.b b.val.1-T.commonDepth)
    have ex:=Nat.mod_add_div a.val.2.val q
    have ey:=Nat.mod_add_div b.val.2.val q
    have share : q*(a.val.2.val/q)=q*(b.val.2.val/q):=congrArg (fun x=>q*x) group
    change _ ∨ _ ∧ a.val.2.val%q<b.val.2.val%q ↔ _ ∨ _ ∧ a.val.2.val<b.val.2.val
    omega
  · simp only [same,false_and,or_false]

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
