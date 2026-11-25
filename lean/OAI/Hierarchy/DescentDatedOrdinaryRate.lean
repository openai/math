import OAI.Hierarchy.DescentDatedOrdinaryArea
import OAI.Hierarchy.DescentDatedAddressRate
import OAI.Hierarchy.DescentPackedOrdinaryUnit

namespace OAI
/-! # A uniform linear address exponent for complete ordinary matching dates -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary
open DescentSIMDLookup DescentPackedColony ProtocolRAM DescentDatedAddressBook Filter
open ThreeFlat.Routing

variable {ι : ℕ→Type*} (a : ∀h,ι h→Ordinary) (roster : ∀h,ι h→Bank)

structure ScalarRoom (a : ∀h,ι h→Ordinary) : Prop where
  hosts : DescentDatedAddressBook.Bounded (fun h i=>(a h i).H)
  groups : DescentDatedAddressBook.Bounded (fun h i=>(a h i).G)
  radix : DescentDatedAddressBook.Bounded (fun h i=>2^(a h i).k)
  degree : DescentDatedAddressBook.Bounded (fun h i=>(a h i).D)
  wires : DescentDatedAddressBook.Bounded (fun h i=>(a h i).cap)
  seats : DescentDatedAddressBook.Bounded (fun h i=>(a h i).seats)
  payload : ∃R : ℕ,∀ᶠ h:ℕ in atTop,∀i,(a h i).payload≤R*h
  census : ∀h i,let v:=a h i;Phase.recordWidth v.k v.b (2*v.cap)≤v.unit
  field : ∀h i,let v:=a h i;2^v.k+(v.k+3)≤v.unit
  cable : ∀h i,let v:=a h i;DescentSignedCableCodec.width v.D v.cap≤v.unit

private theorem word {f : ∀h,ι h→ℕ} (b : ScalarRoom a)
    (fit : ∀h i,f h i≤(a h i).payload) : DescentDatedAddressBook.Bounded (fun h i=>2^(f h i)) := by
  obtain ⟨R,bound⟩:=b.payload
  exact DescentDatedAddressBook.Bounded.pow_of_linear (K:=R) (bound.mono fun h hh i=>(fit h i).trans (hh i))

private theorem table {f : ∀h,ι h→ℕ} (b : ScalarRoom a)
    (fit : ∀h i,f h i≤(a h i).unit) : DescentDatedAddressBook.Bounded (fun h i=>2^(f h i*(a h i).lanesAt)) := by
  apply word a b
  intro h i
  let v:=a h i
  have lanes : v.unit*v.lanesAt≤v.payload/2 := by simpa only [lanesAt,Nat.mul_comm v.unit] using lanes_fit v.payload v.unit
  exact ((Nat.mul_le_mul_right _ (fit h i)).trans lanes).trans (Nat.div_le_self ..)

local macro "close_rate" : tactic =>
  `(tactic| repeat' first
    | assumption
    | apply DescentDatedAddressBook.Bounded.add
    | apply DescentDatedAddressBook.Bounded.mul
    | apply DescentDatedAddressBook.Bounded.max'
    | apply DescentDatedAddressBook.Bounded.sub
    | apply DescentDatedAddressBook.Bounded.div
    | apply DescentDatedAddressBook.Bounded.padded
    | apply DescentDatedAddressBook.Bounded.logPage
    | apply DescentDatedAddressBook.Bounded.const)

set_option maxHeartbeats 600000 in
theorem matcher_rate (b : ScalarRoom a) :
    DescentDatedAddressBook.Bounded (fun h i=>((a h i).matcher (roster h i) 0).endAddr) := by
  have H:=b.hosts
  have G:=b.groups
  have r:=b.radix
  have D:=b.degree
  have cap:=b.wires
  have seats:=b.seats
  have k : DescentDatedAddressBook.Bounded (fun h i=>(a h i).k) := r.of_le fun _ _=>Nat.lt_two_pow_self.le
  have rad : DescentDatedAddressBook.Bounded (fun h i=>2^((a h i).k+1)) := by simpa only [Nat.pow_succ] using r.mul (DescentDatedAddressBook.Bounded.const 2)
  have halfKey := word a b (fun h i=>Nat.div_le_self (a h i).payload 2)
  have allKey := word a b (fun h i=>le_rfl : ∀h i,(a h i).payload≤(a h i).payload)
  have payload : DescentDatedAddressBook.Bounded (fun h i=>(a h i).payload) := allKey.of_le fun _ _=>Nat.lt_two_pow_self.le
  have lanes : DescentDatedAddressBook.Bounded (fun h i=>(a h i).lanesAt) := payload.of_le fun _ _=>Nat.div_le_self ..
  have chunks' : DescentDatedAddressBook.Bounded (fun h i=>chunks (a h i).G (a h i).lanesAt) := by
    unfold chunks poolBatchCount
    close_rate
  have rows' : DescentDatedAddressBook.Bounded (fun h i=>(a h i).rows) := H.mul chunks'
  have readPage : DescentDatedAddressBook.Bounded (fun h i=>(a h i).page) := by
    change DescentDatedAddressBook.Bounded (fun h i=>2^Nat.clog 2 ((a h i).rows+1))
    close_rate
  have unitKey:=table a b (fun h i=>le_rfl : ∀h i,(a h i).unit≤(a h i).unit)
  have censusKey:=table a b (fun h i=>(le_max_right _ _).trans (b.census h i) :
    ∀h i,(1+(a h i).b+2*(2*(a h i).cap))*2^(a h i).k≤(a h i).unit)
  have shiftKey:=table a b (fun h i=>show 1*2^(a h i).k≤(a h i).unit by have h':=b.field h i;dsimp only at h';omega)
  have gateKey:=table a b (fun h i=>show 1*2^(a h i).k+((a h i).k+3)≤(a h i).unit by simpa only [Nat.one_mul] using b.field h i)
  have signedKey:=table a b (b.cable)
  have raw : DescentDatedAddressBook.Bounded (fun h i=>(a h i).phaseAt 0) := by
    change DescentDatedAddressBook.Bounded (fun h i=>
      (0+(a h i).rows+(a h i).page+
        (2^(a h i).k*(1+(1+2*(a h i).cap)))*2^((a h i).unit*(a h i).lanesAt)+(a h i).page+
        2*2^(((1+(a h i).b+2*(2*(a h i).cap))*2^(a h i).k)*(a h i).lanesAt)+
        2^((a h i).rows.log2+1)+(a h i).page+(a h i).page))
    have zero := DescentDatedAddressBook.Bounded.const (ι := ι) 0
    have one := DescentDatedAddressBook.Bounded.const (ι := ι) 1
    have two := DescentDatedAddressBook.Bounded.const (ι := ι) 2
    have columns := r.mul (one.add (one.add (two.mul cap)))
    have source := ((zero.add rows').add readPage).add (columns.mul unitKey)
    exact (((((source.add readPage).add (two.mul censusKey)).add rows'.logPage).add readPage).add readPage)
  have packKey:=table a b (fun h i=>(le_max_left _ _).trans (b.census h i) :
    ∀h i,Phase.unit (a h i).k (a h i).b≤(a h i).unit)
  have menuKey : DescentDatedAddressBook.Bounded (fun h i=>2^((a h i).phaseWidth/2)) := by
    apply packKey.of_le
    intro h i
    apply Nat.pow_le_pow_right (by decide)
    dsimp only [phaseWidth]
    rw [Nat.mul_assoc,Nat.mul_div_cancel_left _ (by decide : 0<2)]
  have frameKey := table a b (fun h i=>show DescentPackedColony.unit (a h i).k (a h i).b≤(a h i).unit by
    apply le_trans _ ((le_max_left _ _).trans (b.census h i))
    unfold DescentPackedColony.unit Phase.unit
    apply max_le <;> dsimp [DescentPackedColony.width] <;> omega)
  have frame : DescentDatedAddressBook.Bounded (fun h i=>((a h i).chooser (roster h i) 0).chart.page) := by
    have both:=(H.max' rows').logPage.add frameKey
    apply both.of_le
    intro h i
    change 2^(max _ _)≤_+_
    rw [max_def]
    split <;> first | exact Nat.le_add_right .. | exact Nat.le_add_left ..
  have win : DescentDatedAddressBook.Bounded (fun h i=>(a h i).winnerEnd (roster h i) 0) := by
    apply DescentDatedAddressBook.Bounded.of_le (le:=fun h i=>(a h i).winner_bound (roster h i) 0)
    dsimp only [Phase.Menu.pages]
    close_rate
  have pre : DescentDatedAddressBook.Bounded (fun h i=>(a h i).prepareAt (roster h i) 0) := win.add readPage
  have two := DescentDatedAddressBook.Bounded.const (ι := ι) 2
  have headPage := ((H.mul D).add (DescentDatedAddressBook.Bounded.const 1)).padded
  have staticRoom := (((shiftKey.add (r.mul gateKey)).add signedKey).add rows').add ((two.mul H).mul D)
  have sort' : DescentDatedAddressBook.Bounded (fun h i=>(a h i).sorterAt (roster h i) 0) :=
    ((pre.add staticRoom).add readPage).add headPage
  have mid : DescentDatedAddressBook.Bounded (fun h i=>(a h i).matcherAt (roster h i) 0) :=
    (((sort'.add (H.mul D)).add ((r.add (r.mul (two.mul cap))).mul rows')).add readPage).max' (sort'.add headPage)
  apply DescentDatedAddressBook.Bounded.of_le (le:=fun h i=>(a h i).matcher_extent (roster h i) 0)
  dsimp only [«fields»]
  close_rate

end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary

end OAI
