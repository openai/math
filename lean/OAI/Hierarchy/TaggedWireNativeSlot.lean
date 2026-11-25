import OAI.Hierarchy.TaggedWireHopData
import OAI.Hierarchy.TaggedShorterCommonScan

namespace OAI
/-! # The actual weighted native prefix as the slot of a route occurrence -/

noncomputable section
namespace Hierarchy.WireTelescope.NativeSlot
open TaggedShorterCommonScan AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
variable {n d W : ℕ}

def mass (key : Fin n→Fin d) (width : Fin n→ℕ) (g : Fin d) :=
  ∑i,if key i=g then width i else 0

theorem full (key : Fin n→Fin d) (width : Fin n→ℕ) (g : Fin d) :
    earlier key width n g=mass key width g := by
  unfold mass earlier
  symm
  apply Finset.sum_bij (fun i _=>i.val)
  · intro i _; exact Finset.mem_range.mpr i.isLt
  · intro a _ b _ eqn; exact Fin.ext eqn
  · intro j hj; exact ⟨⟨j,Finset.mem_range.mp hj⟩,Finset.mem_univ _,rfl⟩
  · intro i _; simp [i.isLt]

theorem earlier_mono (key : Fin n→Fin d) (width : Fin n→ℕ) (g : Fin d) {a b : ℕ}
    (h : a≤b) : earlier key width a g≤earlier key width b g :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _=>Nat.zero_le _)

theorem next (key : Fin n→Fin d) (width : Fin n→ℕ) (i : Fin n) :
    earlier key width (i.val+1) (key i)=earlier key width i.val (key i)+width i := by
  simp [earlier,Finset.sum_range_succ,i.isLt]

def offset (key : Fin n→Fin d) (width : Fin n→ℕ) (c : Bundle width) :=
  earlier key width c.1.val (key c.1)+c.2.val

theorem offset_lt (key : Fin n→Fin d) (width : Fin n→ℕ) (c : Bundle width) :
    offset key width c<mass key width (key c.1) := by
  have top := earlier_mono key width (key c.1) (Nat.succ_le_of_lt c.1.isLt)
  rw [next,full] at top
  exact (Nat.add_lt_add_left c.2.isLt _).trans_le top

private theorem cells (length : Fin n→ℕ) : Fintype.card (Bundle length)=∑i,length i := by
  simp only [Bundle,Fintype.card_sigma,Fintype.card_fin]

def put (key : Fin n→Fin d) (width : Fin n→ℕ) :
    Bundle width≃Bundle (mass key width) := by
  let f (c : Bundle width) : Bundle (mass key width) :=
    ⟨key c.1,offset key width c,offset_lt key width c⟩
  refine Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨?_,?_⟩)
  · rintro ⟨i,u⟩ ⟨j,v⟩ same
    have group : key i=key j := congrArg Sigma.fst same
    have ord : earlier key width i.val (key i)+u.val=earlier key width j.val (key j)+v.val :=
      congrArg (fun t : Bundle (mass key width)=>t.2.val) same
    have distinct (i j : Fin n) (u : Fin (width i)) (v : Fin (width j)) (lt : i<j) (eq : key i=key j) :
        earlier key width i.val (key i)+u.val<earlier key width j.val (key j)+v.val := by
      have before := earlier_mono key width (key i) (Nat.succ_le_of_lt lt)
      rw [next] at before
      rw [←eq]
      have := u.isLt
      omega
    have index : i=j := by
      rcases lt_trichotomy i j with h|eq|h
      · exact ((distinct i j u v h group).ne ord).elim
      · exact eq
      · exact ((distinct j i v u h group.symm).ne ord.symm).elim
    subst j
    exact congrArg (Sigma.mk i) (Fin.ext (Nat.add_left_cancel ord))
  · calc
      Fintype.card (Bundle width) = ∑i,width i := cells width
      _ = ∑g,mass key width g := by
        unfold mass
        rw [Finset.sum_comm]
        simp
      _ = Fintype.card (Bundle (mass key width)) := (cells (mass key width)).symm

/-- Read the actual start address written for this occurrence by the existing
single native weighted scan. The occurrence's own bit is added locally. -/
theorem read_slot (src groups counters dst : ℕ) (key : Fin n→Fin d) (width : Fin n→ℕ) (m : Memory W)
    (sC : src+3*n≤counters) (gC : groups+4*n≤counters) (cD : counters+d≤dst)
    (fits : dst+4*n<2^W) (loaded : Input src groups counters id key width m)
    (i : Fin n) (j : Fin (width i)) :
    image src groups counters dst n m (dst+4*i.val+3)+(j.val:Word W) =
      (((put key width ⟨i,j⟩).2.val:ℕ):Word W) := by
  rw [(read_frame src groups counters dst id key width m sC gC cD fits loaded).1 i]
  change (earlier key width i.val (key i):Word W)+(j.val:Word W)=
    ((earlier key width i.val (key i)+j.val:ℕ):Word W)
  rw [Nat.cast_add]

variable {I : Type} [Fintype I] (route : I→List (Fin d)) (bits : I→ℕ)
variable (rows : Fin n≃Σi,Fin (route i).length)

def edge (j : Fin n) := (route (rows j).1).get (rows j).2
def amount (j : Fin n) := bits (rows j).1

theorem mass_route (e : Fin d) : mass (edge route rows) (amount (route:=route) (bits:=bits) (rows:=rows)) e=routeLoad route bits e := by
  have enumerated := rows.sum_comp (fun q : Σi,Fin (route i).length=>
    if (route q.1).get q.2=e then bits q.1 else 0)
  unfold mass
  refine enumerated.trans ?_
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun i _=>sum_positions_eq_count (route i) e (bits i)

def positions : Hop route bits≃Bundle (amount (route:=route) (bits:=bits) (rows:=rows)) :=
  let turn : Hop route bits≃Σ q : (Σi,Fin (route i).length),Fin (bits q.1) :=
    ⟨fun h=>⟨⟨h.1.1,h.2⟩,h.1.2⟩,fun q=>⟨⟨q.1.1,q.2⟩,q.1.2⟩,fun _=>rfl,fun _=>rfl⟩
  turn.trans (Equiv.sigmaCongrLeft (β:=fun v : Σi,Fin (route i).length=>Fin (bits v.1)) rows).symm

/-- The particular per-edge bijection chosen by the native weighted prefix
engine; it can be given directly to `placed_action`. -/
def allocation : Hop route bits≃Bundle (routeLoad route bits) :=
  ((positions route bits rows).trans (put (edge route rows) (amount (route:=route) (bits:=bits) (rows:=rows)))).trans
    (Equiv.sigmaCongrRight fun e=>finCongr (mass_route route bits rows e))

theorem allocation_edge (h : Hop route bits) : (allocation route bits rows h).1=hopEdge route bits h := by
  change (route (rows (rows.symm ⟨h.1.1,h.2⟩)).1).get (rows (rows.symm ⟨h.1.1,h.2⟩)).2=_
  rw [rows.apply_symm_apply]
  rfl

end Hierarchy.WireTelescope.NativeSlot

end
end OAI
