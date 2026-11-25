import OAI.Hierarchy.ProtocolRAMCatalystPayloadDate
import OAI.Hierarchy.ProtocolRAMCatalystPurchasedDate

namespace OAI
/-! # Constructing the signed archive at every actual date of the same calendar -/

namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe CatalystArchive ProbeStage CoreBoard ColumnWires StripDirectory PurchaseStage StockCommit
open scoped Classical
noncomputable section
set_option maxHeartbeats 600000
variable {z W k q depth K payload : ℕ}
local notation "N" => Stages z (2^W)
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))
local notation "bits" => Native.wordBits z (2^W) Native.copies
local notation "num" => Fintype.card (CoreBoard.Columns z (2^W))*k

/-- The native mesh never consults a future or out-of-range birth shelf. -/
theorem scheduled_inner (c : Mesh) (p a j t : ℕ) (active : Event.attempt (.inner p a j t)∈events c) :
    p<c.inject+c.cool ∧ a<c.outerFuel ∧ j<c.reserveSteps ∧ t<c.innerFuel := by
  rcases List.mem_flatMap.mp active with ⟨u,hu,phase⟩
  simp only [outerBlock,List.mem_append,List.mem_singleton] at phase
  rcases phase with trial | bad
  · rcases List.mem_flatMap.mp trial with ⟨v,hv,entered⟩
    simp only [trialBlock,List.mem_cons] at entered
    rcases entered with bad | slice
    · cases bad
    · rcases List.mem_flatMap.mp slice with ⟨l,hl,row⟩
      simp only [reserveBlock,List.mem_append,List.mem_singleton] at row
      rcases row with row | bad
      · rcases List.mem_map.mp row with ⟨b,hb,same⟩
        cases same
        exact ⟨List.mem_range.mp hu,List.mem_range.mp hv,List.mem_range.mp hl,List.mem_range.mp hb⟩
      · cases bad
  · cases bad

variable (F : Type) [Field F] [Nonempty (Fin k)] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : Boards z (2^W) k q depth) (c : Mesh)
  (b : CatalogueRows.Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel)) (A : Arena)
  (C : Chart (Native.wordBits z (2^W) Native.copies) q
    (max (Fintype.card (PayloadRole (Stages z (2^W)) k)) (Fintype.card (PurchasedRole depth k)))) (initial : Memory (Native.wordBits z (2^W) Native.copies)) (π : Equiv.Perm (Fin (2^z))) (incoming : Attempt→ℕ)
  (labels : Attempt→LabelSource) (finish : ℝ) (fees : PhasePrice)
local notation "fmt" => (fun t=>build F (withPorts s c b G) t (incoming t))
local notation "prior" => (fun t=>entryMemory C initial t)

def cashWidthBase (F : Type) [Field F] {z W k q depth : ℕ}
    [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : Boards z (2^W) k q depth)
    (c : Mesh) (b : CatalogueRows.Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
    (incoming : Attempt→ℕ) : Event→ℕ
  | .feed _ => 0
  | .attempt a => let f := build F (withPorts s c b G) a (incoming a); f.pricedArea.direct+f.occurrences

/-- Actual loaded operands for each call. Every returned original permutation is fixed
to the booted input. Each variant is executed on the true prefix before its own date. -/
def datesOfStrips {J : Type*} [Fintype J] (other : PacketWidths J) (same : C.mesh=c)
    (outer : ∀(p a : ℕ), Event.attempt (.outer p a)∈events c →
      {d : PayloadData (K:=K) (payload:=payload) F s c b G p a (incoming (.outer p a)) C
        (prior (.outer p a)) (labels (.outer p a)) finish fees other // d.π=π})
    (inner : ∀(p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel) (j : Fin c.reserveSteps) (t : Fin c.innerFuel),
      let e := Attempt.inner p.val a.val j.val t.val
      {d : PurchasedData F s c b G p a j.val t.val (incoming e) C (prior e) (labels e) K payload //
        d.permutation=π}) :
    Dates C initial (ownerLedger s c b G F A) (cashWidthBase F s c b G incoming) num payload := by
  intro e he
  rw [same] at he
  cases e with
  | outer p a => exact (outer p a he).val.date A
  | inner p a j t =>
    have bounds := scheduled_inner c p a j t he
    exact (inner ⟨p,bounds.1⟩ ⟨a,bounds.2.1⟩ ⟨j,bounds.2.2.1⟩ ⟨t,bounds.2.2.2⟩).val.date A

/-- The padded occurrence enumeration records the original catalyst label,
using the appropriate (heterogeneous) alphabet for the attempted mode. -/
def AttemptPorts (stages depth k rows stride : ℕ) {count payload : ℕ} (a : Attempt)
    (e : Entry count payload) : Prop :=
  match a with
  | .outer .. => PositivePorts (fun c i=>(.catalyst c i : PayloadRole stages k)) rows stride e
  | .inner .. => PositivePorts (fun c i=>(.catalyst c i : PurchasedRole depth k)) rows stride e

omit [Nonempty (Fin k)] in
theorem datesOfStrips_positive {J : Type*} [Fintype J] (other : PacketWidths J) (same : C.mesh=c)
    (outer : ∀(p a : ℕ), Event.attempt (.outer p a)∈events c →
      {d : PayloadData (K:=K) (payload:=payload) F s c b G p a (incoming (.outer p a)) C
        (prior (.outer p a)) (labels (.outer p a)) finish fees other // d.π=π})
    (inner : ∀(p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel) (j : Fin c.reserveSteps) (t : Fin c.innerFuel),
      let e := Attempt.inner p.val a.val j.val t.val
      {d : PurchasedData F s c b G p a j.val t.val (incoming e) C (prior e) (labels e) K payload //
        d.permutation=π})
    (a : Attempt) (scheduled : Event.attempt a∈events C.mesh) :
    AttemptPorts N depth k (header F (withPorts s c b G) a).rows D a
      ((datesOfStrips F s c b G A C initial π incoming labels finish fees other same outer inner a scheduled).entry) := by
  have entered : Event.attempt a∈events c := same ▸ scheduled
  cases a with
  | outer p i => exact (outer p i entered).val.positive_ports A
  | inner p i j t =>
    have bounds := scheduled_inner c p i j t entered
    exact (inner ⟨p,bounds.1⟩ ⟨i,bounds.2.1⟩ ⟨j,bounds.2.2.1⟩ ⟨t,bounds.2.2.2⟩).val.positive_ports A

end
end Hierarchy.ProtocolRAM.Calendar.StripChart

end OAI
