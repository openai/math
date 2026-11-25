import OAI.Hierarchy.DescentFallbackPacket
import OAI.Hierarchy.DescentPackedLocalLookup
import OAI.Hierarchy.DescentLocalRotorTicket
import OAI.Hierarchy.DescentResetPackedOrder

namespace OAI
/-! # One finite packed rotor scoreboard over real signed chips, reusing the inverse-GL order bits -/
namespace Hierarchy.DescentRotorWindowScore
open DescentSIMDLookup DescentFallbackPeriod DescentPackedFallbackTree.Image
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical
noncomputable section
variable {D L cap n r field : ℕ}

structure Entry where
  neighbor : ℕ
  ownBase : ℕ
  peerBase : ℕ
  wire : ℕ
  within : ℕ

def interval (n w : ℕ) := w/2/(2^n+1)
abbrev Slot (L cap : ℕ) := Fin L×Fin (2*cap)

/-- The row digit inside a good base can change without changing the reservation. -/
def entry (v : Packet D L cap n r field) (side : Bool) (j : Slot L cap) : Option Entry := do
  let chip←signed v j.1 j.2
  let pr←arrival v side j.1 j.2
  let own:=localWord v j.1
  if own%2=0 ∧ pr.2%2=0 then
    some ⟨pr.1.val,interval n own,interval n pr.2,chip.sourceWire.val,chip.within.val⟩
  else none

def cohort (a b : Entry) : Prop := a.neighbor=b.neighbor ∧ a.ownBase=b.ownBase ∧ a.peerBase=b.peerBase

def prior (earlier : Fin L→Fin L→Bool) (u v : Slot L cap) (a b : Entry) : Prop :=
  earlier u.1 v.1=true ∨ u.1=v.1 ∧ (a.wire<b.wire ∨ a.wire=b.wire ∧ a.within<b.within)

def tally (v : Packet D L cap n r field) (side : Bool) (earlier : Fin L→Fin L→Bool) (atRow : Slot L cap) : ℕ :=
  match entry v side atRow with
  | none=>0
  | some b=>(Finset.univ.filter (fun u : Slot L cap=>(entry v side u).any
      (fun a=>decide (cohort a b ∧ prior earlier u atRow a b)))).card

theorem tally_le (v : Packet D L cap n r field) (side : Bool) (earlier : Fin L→Fin L→Bool) (atRow : Slot L cap) :
    tally v side earlier atRow≤L*(2*cap) := by
  unfold tally
  split
  · exact Nat.zero_le _
  · exact (Finset.card_le_univ _).trans_eq (by simp [Slot])

theorem entry_at (v : Packet D L cap n r field) (side : Bool) (j : Slot L cap) (a : DescentSharedCableNames.Stage.Live D cap)
    (peer : ℕ) (physical : signed v j.1 j.2=some a) (link : arrival v side j.1 j.2=some (a.neighbor,peer))
    (ownGood : localWord v j.1%2=0) (peerGood : peer%2=0) :
    entry v side j=some ⟨a.neighbor.val,interval n (localWord v j.1),interval n peer,a.sourceWire.val,a.within.val⟩ := by
  simp [entry,physical,link,ownGood,peerGood]

def bits (L cap : ℕ) := ProtocolRAMPurchaseSampler.bits (L*(2*cap))
def scoreboard (D L cap n r field : ℕ) (side : Bool) :
    Cell (field*inputCount D L cap n r+L*L)→Cell (bits L cap*(L*(2*cap))) := fun packed=>
  let pair:=finProdFinEquiv.symm (Fin.cast (by rw [pow_add]) packed)
  let v:=packet (D:=D) (L:=L) (cap:=cap) (n:=n) (r:=r) (field:=field) pair.1
  let old:=fun (a b : Fin L)=>pair.2.val.testBit (finProdFinEquiv (a,b)).val
  encode _ _ (fun id=>⟨tally v side old (finProdFinEquiv.symm id),
    (tally_le v side old _).trans_lt (ProtocolRAMPurchaseSampler.lt_span _)⟩)

def input (v : Packet D L cap n r field) (orderBits : Cell (L*L)) : Cell (field*inputCount D L cap n r+L*L) :=
  Fin.cast (by rw [pow_add]) (finProdFinEquiv (encodePacket v,orderBits))

theorem scoreboard_read (v : Packet D L cap n r field) (side : Bool) (orderBits : Cell (L*L)) (j : Slot L cap) :
    ((encode (bits L cap) (L*(2*cap))).symm (scoreboard D L cap n r field side (input v orderBits))
      (finProdFinEquiv j)).val=tally v side (fun a b=>orderBits.val.testBit (finProdFinEquiv (a,b)).val) j := by
  simp only [scoreboard,input,Fin.cast_cast,Fin.cast_refl,id_eq,Equiv.symm_apply_apply,packet_encode]

/-- All ticket counts for one direction in one packed output row. The input optionally
shares the old-chart rank fields with the exceptional branch. -/
theorem issued {H G M w : ℕ} (menu : Banks) (out : ℕ) (side : Bool) (v : Fin H→Fin G→Packet D L cap n r field)
    (orderBits : Fin H→Fin G→Cell (L*L)) (pos : 0<M) (mem : Memory w)
    (safe : DescentSIMDLookup.Fits menu (field*inputCount D L cap n r+L*L) (bits L cap*(L*(2*cap))) M H G w out)
    (lookup : resident (scoreboard D L cap n r field side) menu H G M mem)
    (src : ∀q : Row H G M,mem (menu.source.base+(row H G M q).val)=
      (data (fun h j=>input (v h j) (orderBits h j)) q).val) :
    let dst:=imageBank H G M out menu mem
    (program menu out H G M w).Exec mem dst (4+44*(H*chunks G M)) ∧
    ∀h j,digit (bits L cap*(L*(2*cap))) (lane j pos).val (dst (out+(row H G M (position h j pos)).val)).val=
      (scoreboard D L cap n r field side (input (v h j) (orderBits h j))).val := by
  obtain ⟨run,read,_,_⟩:=DescentPackedLocalLookup.compile menu out (scoreboard D L cap n r field side)
    (fun h j=>input (v h j) (orderBits h j)) pos safe mem lookup (fun q=>by
      apply Fin.ext
      change _ = _ % (2^w)
      rw [←src q,Nat.mod_eq_of_lt (mem _).isLt])
  exact ⟨run,read⟩

end
end Hierarchy.DescentRotorWindowScore

end OAI
