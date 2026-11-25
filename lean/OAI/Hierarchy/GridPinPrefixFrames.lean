import OAI.Hierarchy.GridPinNativeNatural
import OAI.Hierarchy.GridPinLiteralImage

namespace OAI
/-! # Memory frames for the three native prefix passes -/

namespace Hierarchy.GridPinNativeLoops
open Computability.VPVNP.BurstRAM PrivateRAM FactorBucketRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- An address lies outside a contiguous bank of a given word length. -/
def outside (base length a : ℕ) : Prop := a<base ∨ base+length≤a

private theorem outside_ne {base length a offset : ℕ} (h : outside base length a)
    (row : offset<length) : a≠base+offset := by
  rcases h with h | h <;> omega

private theorem indexed_address (base : ℕ) (z : Word w) (fit : base+z.val<2^w) :
    ((base:Word w)+z).val=base+z.val := by
  have eqn : (base:Word w)+z=((base+z.val:ℕ):Word w) := by simp
  rw [eqn,Fin.val_cast_of_lt fit]

private theorem two_writes (m : Memory w) (p q x y : Word w) (a : ℕ)
    (hq : a≠q.val) (hp : a≠p.val) :
    writeMemory (writeMemory m p x) q y a=m a := by simp [writeMemory,hq,hp]

private theorem iter_preserved (step : Parameters w→Word w→Memory w→Memory w) (v : Parameters w)
    (m : Memory w) (n : ℕ) (keep : ℕ→Prop)
    (one : ∀ i<n, ∀ o : Memory w, (∀ a,keep a → o a=m a) →
      ∀ a,keep a→step v (i:Word w) o a=o a) :
    ∀ a,keep a→iterRows step v m n a=m a := by
  have stable (j : ℕ) (hj : j≤n) : ∀ a, keep a→iterRows step v m j a=m a := by
    induction j with
    | zero => exact fun _ _=>rfl
    | succ j ih =>
      have frame := ih (by omega)
      intro a ha
      exact (one j (by omega) _ frame a ha).trans (frame a ha)
  exact stable n le_rfl

/-- The addresses written by the factor scan depend only on the row index and
the original bounded owner word. Both possible destination banks are framed. -/
theorem factor_frame (p : FactorBanks) (m : Memory w) (n T : ℕ)
    (itemsPos : 0<n→0<p.items) (nFit : n≤2^w) (itemsFit : p.items<2^w)
    (ownersRoom : p.owners+p.items≤2^w) (basesRoom : p.bases+p.items≤2^w)
    (ticksRoom : p.ticks+T≤2^w) (owner : ∀ f : Fin p.items,(m (p.owners+f.val)).val<T)
    (ownersAway : ∀ f : Fin p.items, outside p.ticks T (p.owners+f.val) ∧
      outside p.bases p.items (p.owners+f.val))
    (a : ℕ) (aTick : outside p.ticks T a) (aBase : outside p.bases p.items a) :
    iterRows factorStep (factorWords w n p) m n a=m a := by
  let keep := fun z=>outside p.ticks T z ∧ outside p.bases p.items z
  apply iter_preserved factorStep _ m n keep _ a ⟨aTick,aBase⟩
  intro i hi o same z hz
  let f : Fin p.items := ⟨i%p.items,Nat.mod_lt _ (itemsPos (by omega))⟩
  have modEq : BinaryOp.mod.eval (i:Word w) (p.items:Word w)=(f.val:Word w) := by
    simp [f,BinaryOp.eval,Fin.val_cast_of_lt (hi.trans_le nFit),Fin.val_cast_of_lt itemsFit]
  have fi := f.isLt
  have srcFit : p.owners+f.val<2^w := by omega
  have destFit : p.bases+f.val<2^w := by omega
  have own : (o (p.owners+f.val)).val<T := by rw [same _ (ownersAway f)];exact owner f
  have cpFit : p.ticks+(o (p.owners+f.val)).val<2^w := by omega
  unfold factorStep
  apply two_writes
  · change z≠((p.ticks:Word w)+o (((p.owners:Word w)+BinaryOp.mod.eval (i:Word w) (p.items:Word w)).val)).val
    rw [modEq,←Nat.cast_add,Fin.val_cast_of_lt srcFit,indexed_address _ _ cpFit]
    exact outside_ne hz.1 own
  · change z≠((p.bases:Word w)+BinaryOp.mod.eval (i:Word w) (p.items:Word w)).val
    rw [modEq,←Nat.cast_add,Fin.val_cast_of_lt destFit]
    exact outside_ne hz.2 fi

/-- The bucket scan writes only the active lane bases and their factors' cursors. -/
theorem bucket_frame (p : BucketBanks) (m : Memory w) (n N : ℕ)
    (ownersRoom : p.owners+n≤2^w) (blocksRoom : p.blocks+n≤2^w)
    (cursorRoom : p.cursors+N≤2^w) (owner : ∀ b : Fin n,(m (p.owners+b.val)).val<N)
    (ownersAway : ∀ b : Fin n, outside p.cursors N (p.owners+b.val) ∧ outside p.blocks n (p.owners+b.val))
    (a : ℕ) (aCur : outside p.cursors N a) (aBlock : outside p.blocks n a) :
    iterRows bucketStep (bucketWords w n p) m n a=m a := by
  let keep := fun z=>outside p.cursors N z ∧ outside p.blocks n z
  apply iter_preserved bucketStep _ m n keep _ a ⟨aCur,aBlock⟩
  intro i hi o same z hz
  have srcFit : p.owners+i<2^w := by omega
  have dstFit : p.blocks+i<2^w := by omega
  have own : (o (p.owners+i)).val<N := by
    rw [same _ (ownersAway ⟨i,hi⟩)];exact owner ⟨i,hi⟩
  have cpFit : p.cursors+(o (p.owners+i)).val<2^w := by omega
  unfold bucketStep
  apply two_writes
  · change z≠((p.cursors:Word w)+o (((p.owners:Word w)+(i:Word w)).val)).val
    rw [←Nat.cast_add,Fin.val_cast_of_lt srcFit,indexed_address _ _ cpFit]
    exact outside_ne hz.1 own
  · change z≠((p.blocks:Word w)+(i:Word w)).val
    rw [←Nat.cast_add,Fin.val_cast_of_lt dstFit]
    exact outside_ne hz.2 hi

theorem seed_rows (dst stride start n : ℕ) (m : Memory w) (room : dst+n≤2^w) :
    iterRows seedStep (seedWords w n dst stride start) m n=
      GridPinLiteralImage.writeRows (fun i=>dst+i) (fun i=>((i*stride+start:ℕ):Word w)) m n := by
  have eqn (k : ℕ) (hk : k≤n) : iterRows seedStep (seedWords w n dst stride start) m k=
      GridPinLiteralImage.writeRows (fun i=>dst+i) (fun i=>((i*stride+start:ℕ):Word w)) m k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iterRows,seedStep_natural _ _ _ _ _ _ (by omega),ih (by omega)]
      rfl
  exact eqn n le_rfl

theorem seed_frame (dst stride start n : ℕ) (m : Memory w) (room : dst+n≤2^w)
    (a : ℕ) (ha : outside dst n a) : iterRows seedStep (seedWords w n dst stride start) m n a=m a := by
  rw [seed_rows _ _ _ _ _ room]
  exact GridPinLiteralImage.untouched _ _ _ _ _ (fun i hi=>(outside_ne ha hi).symm)

theorem seed_readback (dst stride start n : ℕ) (m : Memory w) (room : dst+n≤2^w)
    (i : ℕ) (hi : i<n) : iterRows seedStep (seedWords w n dst stride start) m n (dst+i)=
      ((i*stride+start:ℕ):Word w) := by
  rw [seed_rows _ _ _ _ _ room]
  exact GridPinLiteralImage.hit (fun j=>dst+j) _ _ _ _ hi (fun j _ h=>Nat.add_left_cancel h)

end Hierarchy.GridPinNativeLoops

end OAI
