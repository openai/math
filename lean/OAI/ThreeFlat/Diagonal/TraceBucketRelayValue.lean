import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.Diagonal.TraceBucketRelayRows
import OAI.ThreeFlat.Diagonal.TraceBucketRelayMask
import OAI.ThreeFlat.Diagonal.TraceBucketRelayFit

namespace OAI
/-! # The emitted words of every hole and forwarding factor in the initial relay -/

namespace ThreeFlat.Diagonal.TraceBucketRelay
open LaneCursor RAM
open scoped Classical Fin.CommRing

variable {F O D : Type*} [CommSemiring F] {r k t : ℕ}

private theorem send_address (extra : ℕ) (s : Fin (arcs r)) (a : Fin t) :
    shiftedSource extra (sendPin s a) = 2+extra+(a.val+t*s.val) := rfl

private theorem recv_address (extra : ℕ) (s : Fin (arcs r)) (a : Fin t) :
    shiftedSource extra (recvPin s a) = 2+extra+(arcs r*t+(a.val+t*s.val)) := rfl

def equalityTag (tag : ((Fin 3 → Bool) → F) → ℕ) : ℕ :=
  tag (fun z => if z 0=z 1 then 1 else 0)

private theorem relay_table (ord : Fin t ≃ O × D) (mask : O → Lane (k+1)) (i : Fin (k+1))
    (c : Fin (arcs r*t+t)) (tag : ((Fin 3 → Bool) → F) → ℕ) :
    tag ((RelayNetwork.network (r:=r) ord mask i).table c) = equalityTag tag := rfl

theorem values_metadata (ord : Fin t ≃ O × D) (mask : O → Lane (k+1)) (i : Fin (k+1))
    (perOffset d low extra : ℕ) (tag : ((Fin 3 → Bool) → F) → ℕ)
    (sel : ∀ (a : Fin t) (j : Fin (k+1)), (selected (r:=r) mask (ord a).1 j).val =
      chooseSlot d (a.val/perOffset) (low+j.val))
    (c : Fin (arcs r*t+t)) (j : Fin 4) :
    values (arguments (arcs r) t perOffset d low i.val extra (equalityTag tag) c.val j.val) =
      metadata extra tag (RelayNetwork.network ord mask i) c j := by
  induction c using Fin.addCases with
  | left z =>
    obtain ⟨⟨s,a⟩,rfl⟩ := finProdFinEquiv.surjective z
    let u := finProdFinEquiv (s,a)
    have hu : u.val<arcs r*t := u.isLt
    have m : u.val%t=a.val := by
      change (a.val+t*s.val)%t=a.val
      rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt a.isLt]
    have q : u.val/t=s.val := by
      change (a.val+t*s.val)/t=s.val
      rw [Nat.add_mul_div_left _ _ (show 0<t by have := a.isLt; omega),Nat.div_eq_of_lt a.isLt,Nat.zero_add]
    have he : s.val=chooseSlot d (a.val/perOffset) (low+i.val) ↔ s=selected (r:=r) mask (ord a).1 i := by
      rw [← sel a i]
      exact Fin.ext_iff.symm
    have hv : u.val=a.val+t*s.val := rfl
    change values (arguments _ _ _ _ _ _ _ _ u.val j.val) = metadata extra tag (RelayNetwork.network (r:=r) ord mask i) (u.castAdd t) j
    have send (b : Fin (arcs r)) : (finProdFinEquiv (b,a)).val=a.val+t*b.val:=rfl
    fin_cases j <;> simp [metadata,values,arguments,hole_sources,relay_table,shiftedSource,hv,u] <;> split_ifs <;> simp_all [sendPin]
  | right a =>
    let u := Fin.natAdd (arcs r*t) a
    have hn : ¬u.val<arcs r*t := by change ¬arcs r*t+a.val<_; omega
    have m : u.val%t=a.val := by
      change (arcs r*t+a.val)%t=a.val
      rw [Nat.add_comm,Nat.mul_comm (arcs r) t,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt a.isLt]
    have hi : i.val=0 ↔ i=0 := ⟨fun e => Fin.ext e,fun e => congrArg Fin.val e⟩
    change values (arguments _ _ _ _ _ _ _ _ u.val j.val) = metadata extra tag (RelayNetwork.network (r:=r) ord mask i) u j
    have send (b : Fin (arcs r)) : (finProdFinEquiv (b,a)).val=a.val+t*b.val:=rfl
    fin_cases j <;> by_cases h0 : i=0 <;> simp [metadata,values,arguments,hi,h0,
      forward_sources,relay_table,sel,previous,u,shiftedSource,sendPin,recvPin,
      send,Nat.mod_eq_of_lt a.isLt]; omega

/-- Execute the fixed ten-register kernel on a row of the physical relay.
The caller supplies the prefix of locally owned genuine input pins. -/
theorem program_metadata {W K n low offsets slots : ℕ} {N : BitNetwork F n}
    (P : RowLayout N (k+1) low offsets slots) (d : ℕ)
    (hd : ∀ o : Fin offsets, (P.offset o).val=TracePhysical.maskNat d o.val)
    (i : Fin (k+1)) (extra : ℕ) (tag : ((Fin 3 → Bool) → F) → ℕ)
    (c : Fin (arcs r*(offsets*(2^low*(slots*3)))+offsets*(2^low*(slots*3)))) (j : Fin 4)
    (port : RAM.PhysicalPinsExpr.Param → Fin K) (data : Fin K → ℕ) (m : ℕ → ℕ)
    (h : Bounds W (arguments (arcs r) (offsets*(2^low*(slots*3))) (2^low*(slots*3))
      d low i.val extra (equalityTag tag) c.val j.val)) :
    (program W K port).eval (fun z => (data z : Computability.VPVNP.BurstRAM.Word W))
      (fun z => (m z : Computability.VPVNP.BurstRAM.Word W))
      (fun z => (arguments (arcs r) (offsets*(2^low*(slots*3))) (2^low*(slots*3))
        d low i.val extra (equalityTag tag) c.val j.val z : Computability.VPVNP.BurstRAM.Word W)) =
      (metadata extra tag (RelayNetwork.network (r:=r) (RowLayout.tagOrder offsets low slots) P.mask i) c j :
        Computability.VPVNP.BurstRAM.Word W) := by
  rw [program_eval port data m _ h,values_metadata _ _ _ _ _ _ _ _ (selected_slot P hd)]

end ThreeFlat.Diagonal.TraceBucketRelay

end OAI
