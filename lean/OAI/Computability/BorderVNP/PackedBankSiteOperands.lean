import OAI.Computability.BorderVNP.PackedBankProfileFactor
import OAI.Computability.BorderVNP.PackedBankSiteView
import OAI.Computability.BorderVNP.PackedBankReferences

/-! # The profile packet operands at their sewn cable addresses

The physical words in a seed packet are the matched count, histogram, site
staging offset and canonical cable bases in its owning cell. The geometry's
endpoint choices give the source spoke at the origin, and the destination
spoke and source feeder at every terminal.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankSite

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Crossing.Profile.Cell CellSparse BankCircuit BankJoint
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (a : S)

/-- The fine site of one inserted template node in the sewn layout. -/
def seedSite (v : TemplateSite e) : (G e p bin perm positive first q).Site := .inr ⟨a,v⟩

private noncomputable abbrev J := blocks p.layout bin perm m a
variable {C : Type} (cell : (G e p bin perm positive first q).Site → C)
variable (aux : (G e p bin perm positive first q).Site → ℕ)
variable {ns ne np : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)
variable (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (boxID : TemplateSite e → ℕ)

/-- The actual raw operand vector at this seed, using its assigned merged box IDs. -/
noncomputable def physicalRaw : Raw e → ℕ
  | .inl i => i.elim (J p bin perm (m := m) a) (q a).val
  | .inr ⟨v,none⟩ =>
    let G := G e p bin perm positive first q
    let u : G.Site := .inr ⟨a,v⟩
    CellAddresses.siteBase G cell (cell u) siteID aux ⟨u,rfl⟩
  | .inr ⟨v,some none⟩ => boxID v
  | .inr ⟨v,some (some b)⟩ => (reference e v b).elim 0 fun z =>
    let G := G e p bin perm positive first q
    cableBase G cell aux edgeID portID (.inr (.inr ⟨a,z.1⟩)) z.2

variable (W : CellBanks (G e p bin perm positive first q) cell aux)

private noncomputable abbrev raw := physicalRaw e p bin perm positive first q a cell aux siteID edgeID portID boxID

/-- The address of a strided block lane in a packed cable is its contiguous physical offset. -/
theorem lane_add (base : ℕ) {c w : ℕ} (i : Fin c) (k : Fin w) :
    (⟨base,w,1⟩ : Port).atBit i k = base + (finProdFinEquiv (i,k)).val := by
  simp [Port.atBit,Nat.mul_comm,Nat.add_comm]
  omega

/-- The origin spoke read from the returned raw packet is the true physical selector of its sewn assignment. -/
theorem origin_spoke (t : Fin D × Bool) :
    let v := seedSite e p bin perm positive first q a (.inl ())
    let x := originWords e (raw e p bin perm positive first q a cell aux siteID edgeID portID boxID)
    selector (A := e.count) (j := J p bin perm (m := m) a) (W.read v) (BankPacket.physicalPort m x (.inl t)) =
      selectors e p bin perm positive first q a (W.wires edgeID portID v) t := by
  intro v x
  funext i k
  apply congrArg finTwoEquiv.symm
  let G := G e p bin perm positive first q
  let u : G.Edge := .inr (.inr ⟨a,.inl t⟩)
  change W.read v ((⟨cableBase G cell aux edgeID portID u true,Nat.clog 2 e.count,1⟩ : Port).atBit i k) = _
  rw [lane_add]
  exact cable_read G cell aux W edgeID portID u true (finProdFinEquiv (i,k))

/-- The selected destination end of a spoke carries the actual terminal's selector blocks. -/
theorem terminal_spoke (t : Fin D × Bool) :
    let v := seedSite e p bin perm positive first q a (.inr (.inl t))
    let x := terminalWords e (raw e p bin perm positive first q a cell aux siteID edgeID portID boxID) t
    selector (A := e.count) (j := J p bin perm (m := m) a) (W.read v)
        (BankPacket.physicalPort m x (.inr (.inl ()))) =
      selectors e p bin perm positive first q a (W.wires edgeID portID v) t := by
  intro v x
  funext i k
  apply congrArg finTwoEquiv.symm
  let G := G e p bin perm positive first q
  let u : G.Edge := .inr (.inr ⟨a,.inl t⟩)
  change W.read v ((⟨cableBase G cell aux edgeID portID u false,Nat.clog 2 e.count,1⟩ : Port).atBit i k) = _
  rw [lane_add]
  exact cable_read G cell aux W edgeID portID u false (finProdFinEquiv (i,k))

/-- The physical feeder starts at the terminal and has the source template's
copy order even when its count vanishes. -/
theorem terminal_feeders (t : Fin D × Bool) :
    let v := seedSite e p bin perm positive first q a (.inr (.inl t))
    let x := terminalWords e (raw e p bin perm positive first q a cell aux siteID edgeID portID boxID) t
    feeders (b := m) (q a).val (W.read v) (fun u => BankPacket.physicalPort m x (.inr (.inr (.inr u)))) =
      feederBlocks e p bin perm positive first q a (W.wires edgeID portID v) t := by
  intro v x
  funext f i k
  let G := G e p bin perm positive first q
  let u : G.Edge := .inr (.inr ⟨a,.inr (.inl (f,t))⟩)
  change W.read v ((⟨cableBase G cell aux edgeID portID u true,m,1⟩ : Port).atBit i k) = _
  rw [lane_add]
  exact cable_read G cell aux W edgeID portID u true (finProdFinEquiv (i,k))

end Packing.BankSite

end BorderVNP
end Computability
end OAI
