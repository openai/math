import OAI.Computability.BorderVNP.TransmissionChosenPhysical

/-! # The chosen reference packet and both real pin arrays on any substituted tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing ResidueBox ResiduePins ResidueIndex DiagonalResidueRAM VPVNP VPVNP.BurstRAM
open TeamContraction ProcessorSlots RoutingISA RoutingISA.Pins
open scoped Classical

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {e : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField e aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult tally w pin pc reg routines a link n ec : ℕ}
    (reader : ChosenReader chart (R+1) r mult tally w pin)
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc reg 32 routines)
    (S : SiteData R r reg 32 w a) (fit : fitsWith physical reg 32 r w a R link n ec)
    (valuation entry totals : Fin (R+1) → ℕ) (extension : Fin (R+1) → Fin 81 → Word w)
    (L : Routing.WireLayout (R+1) r link)
local notation "bits" => (pairedTableParameters (k+1) s+2)*pin
local notation "query" => Board.Physical (pairedTableParameters (k+1) s) pin tally (e.Entry ⊕ ι)

/-- On the actual shared-header wiring the reader's physical stride, complete input
rectangle, two disjoint pin copies, and dense payload all fit the same startup
reservation. This holds after substituting arbitrary site literals and reader addresses. -/
theorem ChosenReader.chosen_packet_pin_bounds (u : Fin (R+1)) (header : 0 < L.header)
    (copies : reader.packetBitCount ≤ r) :
    let A := reader.startupArenaWith (n:=n) (reg:=reg) physical a link L.header
    let place := fun v : Fin (R+1) => ReaderPlacement.inArena A (valuation v) (entry v) (totals v) (extension v)
    let packet := reader.packetAt (place u)
    let G := wiringWith physical P S bits link n ec fit
    let pins := G.pinLayout u A.ibase A.hbase (A.dense+packet.offset)
    A.next < 2^w → pins.stride < 2^w ∧ pins.count < 2^w ∧ bits ≤ pins.count ∧
      LoopFits w pins ∧ Separated pins ∧ bits ≤ A.count ∧ (6+3*reader.gates+Fintype.card query)*w ≤ A.copied := by
  intro A place packet G pins room
  have ok := reader.arena_fitsWith physical P S fit valuation entry totals extension L u header copies room
  have op := reader.siteOperands_arenaWith physical P S fit valuation entry totals extension L u
  rw [op] at ok
  have loop : LoopFits w pins := ok.2.2.2.2.1
  have index : bits ≤ pins.count := ok.2.2.2.2.2.2
  have teamFit := L.three
  let pair : Routing.Block (R+1) := ⟨(⟨0,by omega⟩,⟨1,by omega⟩),Nat.zero_lt_one⟩
  have block : L.header ≤ r*link := by have load := L.fits pair; omega
  have procs : 0 < r := Nat.pos_of_mul_pos_right (header.trans_le block)
  have stride : pins.stride = A.stride := by
    change A.literal+(A.teams-1)*A.link+A.literal=2*A.literal+(A.teams-1)*A.link
    omega
  have occupied : pins.processors*pins.stride=A.frame := by rw [stride]; rfl
  have before : A.frame ≤ A.ibase := by unfold StartupArena.ibase StartupArena.broadcastBase StartupArena.dense; omega
  have count : pins.count=A.count := rfl
  have tail : A.hbase=A.ibase+A.count := rfl
  have nextAddr : A.next=A.hbase+A.count := rfl
  have strFits : pins.stride ≤ A.frame := occupied ▸ Nat.le_mul_of_pos_left _ procs
  have diff := Separated.of_intervals pins
    (show pins.processors*pins.stride ≤ A.ibase from occupied ▸ before)
    (show pins.processors*pins.stride ≤ A.hbase from occupied ▸ before.trans (Nat.le_add_right _ _))
    (Or.inl (show A.ibase+pins.count ≤ A.hbase from count ▸ le_rfl))
  have len : packet.entry.length=6+3*reader.gates+Fintype.card query := payload_length ..
  have copy : packet.entry.length*w ≤ packet.bits.length := by
    calc
      packet.entry.length*w ≤ (packet.entry.length+81)*w := Nat.mul_le_mul_right w (Nat.le_add_right ..)
      _ = packet.offset := Nat.mul_comm ..
      _ ≤ packet.offset+bits := Nat.le_add_right ..
      _ = packet.bits.length := packet.bits_length.symm
  rw [reader.packetAt_length] at copy
  exact ⟨by omega,by omega,index,loop,diff,count ▸ index,len ▸ copy⟩

end Diagonal

end BorderVNP
end Computability
end OAI
