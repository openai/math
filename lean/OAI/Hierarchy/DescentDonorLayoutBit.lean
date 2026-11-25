import OAI.Hierarchy.DescentDonorShape
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Broadcast the actual best-layout choice into the old source registers -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Owners.LayoutBit
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M w r D p d : ℕ}

def join (n : ℕ) (tag : Cell 1) (raw : Cell n) : Cell (1+n) :=
  finCongr (pow_add 2 1 n).symm (finProdFinEquiv (tag,raw))

theorem zero (n : ℕ) : join n 0 0=0 := by
  apply Fin.ext
  simp [join,finProdFinEquiv_apply_val]

structure Banks where
  gate : Bank
  live : Bank
  widen : Tables

def broadcast (B : Banks) : Expr :=
  .branch .eq (.lookup B.gate (.lit 0)) (.lit 0) (.lit 0) (.lookup B.live .row)

def field (B : Banks) (raw : Expr) := B.widen.read (broadcast B) raw

structure Room (B : Banks) (e : Expr) (H G M n w base : ℕ) : Prop where
  gate : B.gate.Fits w base
  mask : B.live.Fits w base
  rows : H*chunks G M≤B.live.size
  widen : DescentPackedZip.Fits B.widen (broadcast B) e 1 n M base w
  positive : 0<w

theorem source (B : Banks) (e : Expr) (base : ℕ) (room : Room B e H G M (d*fields r D p) w base)
    (lay : Bool) (u : Fin H→Fin G→Panel r D p d) (m : Memory w)
    (chosen : m B.gate.base=(if lay then (1:Word w) else 0))
    (active : ∀q : Row H G M,m (B.live.base+(row H G M q).val)=
      ((data (fun (_:Fin H) (_:Fin G)=>(1:Cell 1)) q).val:Word w))
    (static : Static B.widen (join (d*fields r D p)) M m)
    (topology : Source e (fun h g=>encodePanel (u h g)) M m) :
    Source (field B e) (fun h g=>register lay (u h g)) M m := by
  have value : Source (broadcast B) (fun (_:Fin H) (_:Fin G)=>(lay.toNat:Cell 1)) M m := by
    intro q
    have old : B.gate.read m 0=(if lay then (1:Word w) else 0) := by
      calc
        _ = m (B.gate.base+0) := by
          simpa only [Nat.cast_zero] using bank_read B.gate m (i:=0) room.gate.1 room.gate
        _ = _ := by simpa only [Nat.add_zero] using chosen
    have live:= (bank_read B.live m ((row H G M q).isLt.trans_le room.rows) room.mask).trans (active q)
    have one : (1:Word w)≠0:=by
      have low : 1<2^w:=Nat.one_lt_two_pow (by have:=room.positive;omega)
      intro no
      have h:=congrArg Fin.val no
      rw [show (1:Word w).val=1 from Fin.val_cast_of_lt low] at h
      exact Nat.one_ne_zero h
    have gateZero : DescriptorExpr.Comparison.eq.test (B.gate.read m 0) 0=(!lay) := by
      cases lay <;> simp [DescriptorExpr.Comparison.test,old,one]
    cases lay
    · simp [broadcast,Expr.eval,gateZero,data,encode]
    · simpa [broadcast,Expr.eval,gateZero] using live
  exact read_data B.widen (broadcast B) e base room.widen (join _) (zero _) m static _ _ value topology

/-- Read the saved common bit after the chooser has returned. All earlier
topology and lookup cells stay under the chooser's first write. -/
theorem source_before (B : Banks) (e : Expr) (base cutoff : ℕ) (room : Room B e H G M (d*fields r D p) w base)
    (lay : Bool) (u : Fin H→Fin G→Panel r D p d) (prior current : Memory w)
    (early : e.Fits w cutoff) (kept : ∀i,i<cutoff→current i=prior i)
    (old : B.live.base+B.live.size≤cutoff ∧ B.widen.shift.base+B.widen.shift.size≤cutoff ∧
      B.widen.apply.base+B.widen.apply.size≤cutoff)
    (chosen : current B.gate.base=(if lay then (1:Word w) else 0))
    (active : ∀q : Row H G M,prior (B.live.base+(row H G M q).val)=
      ((data (fun (_:Fin H) (_:Fin G)=>(1:Cell 1)) q).val:Word w))
    (static : Static B.widen (join (d*fields r D p)) M prior)
    (topology : Source e (fun h g=>encodePanel (u h g)) M prior) :
    Source (field B e) (fun h g=>register lay (u h g)) M current := by
  apply source B e base room lay u current chosen
  · intro q
    exact (kept _ ((Nat.add_lt_add_left ((row H G M q).isLt.trans_le room.rows) _).trans_le old.1)).trans (active q)
  · constructor
    · intro x
      have len:x.val<B.widen.shift.size:=by simpa [Bank.size,room.widen.shiftBits] using x.isLt
      exact (kept _ ((Nat.add_lt_add_left len _).trans_le old.2.1)).trans (static.1 x)
    · intro x
      have len:x.val<B.widen.apply.size:=by simp [Bank.size,room.widen.applyBits]
      exact (kept _ ((Nat.add_lt_add_left len _).trans_le old.2.2)).trans (static.2 x)
  · intro q
    exact (ProtocolRAM.eval_below e _ prior current early kept).trans (topology q)

theorem fits {n base : ℕ} (B : Banks) (e : Expr) (room : Room B e H G M n w base) : (field B e).Fits w base :=
  ⟨room.widen.apply,room.widen.right,room.widen.shift,room.widen.left⟩

theorem work (B : Banks) (e : Expr) : (field B e).work≤e.work+30 := by
  rw [field,DescentPackedZip.work]
  simp only [broadcast,Expr.work];omega

end
end Hierarchy.DescentPacking.PackedMatch.Local.Owners.LayoutBit

end OAI
