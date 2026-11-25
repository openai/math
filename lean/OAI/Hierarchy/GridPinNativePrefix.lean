import OAI.Hierarchy.GridPinNativeNatural
import OAI.Hierarchy.GridPinScanPrefix

namespace OAI
/-! # Physical prefix cursors from the genuine key, owner and resource words -/

namespace Hierarchy.GridPinNativeLoops
open Computability.VPVNP.BurstRAM PrivateRAM
open FactorBucketRAM FactorPinIntervals GridPinPrefixMemory
open scoped Fin.CommRing

variable {w : ℕ}

/-- Applying a variable list of one- or two-write rows preserves the full
upstream bank. Its contents are only required in the initial memory. -/
private theorem preserved_rows {R C : Type} {n : ℕ} (select : ℕ→Option R)
    (owner : R→C) (size : R→Word w) (cur : C→ℕ) (dst : R→ℕ)
    (m₀ : Memory w) (m : ℕ→Memory w) (init : m 0=m₀) (read : ℕ→Prop)
    (away : ∀ a, read a → (∀ c, a≠cur c) ∧ ∀ r, a≠dst r)
    (write : ∀ i<n, (∀ a, read a→m i a=m₀ a) →
      m (i+1)=(select i).elim (m i) (store owner size cur dst (m i))) :
    ∀ i<n, m (i+1)=(select i).elim (m i) (store owner size cur dst (m i)) := by
  have stable (i : ℕ) (hi : i≤n) : ∀ a, read a→m i a=m₀ a := by
    induction i with
    | zero => simp [init]
    | succ i ih =>
      have h := ih (by omega)
      rw [write i (by omega) h]
      intro a ha
      obtain ⟨hc,hd⟩ := away a ha
      cases e : select i with
      | none => exact h _ ha
      | some r => simpa [store,Function.update_of_ne (hc (owner r)),Function.update_of_ne (hd r)] using h _ ha
  exact fun i hi=>write i hi (stable i hi.le)

def FactorBanks.reads (p : FactorBanks) (N a : ℕ) : Prop :=
  ∃ f : Fin N, a=p.keys+f.val ∨ a=p.owners+f.val ∨ a=p.resource+f.val*p.stride+p.amount

/-- Constant upstream words suffice for *all* subsequent states of the
class-major native pass. The returned prefix is precisely the initial
tick cursor plus the lengths of earlier original factors in that tick. -/
theorem factor_readback {N T d S : ℕ} (ht : 0<T) (scale : ℕ) (cost : Fin N→Fin d→ℕ)
    (origin : Fin S→Fin N) (p : FactorBanks) (rows : p.items=N) (m : Memory w)
    (countFit : ((20*(scale+1)+2)^d)*N<2^w) (nFit : N<2^w)
    (keyFit : ∀ f, factorKey scale cost f<2^w) (tFit : T≤2^w)
    (keyAt : ∀ f, m (p.keys+f.val)=(factorKey scale cost f:Word w))
    (ownerAt : ∀ f, m (p.owners+f.val)=((FactorAllocation.owner ht scale cost f).val:Word w))
    (costAt : ∀ f : Fin N, m (p.resource+f.val*p.stride+p.amount)=((intervalBits origin f).length:Word w))
    (fit : ∀f : Fin N, p.keys+f.val<2^w ∧ p.owners+f.val<2^w ∧
      p.resource+f.val*p.stride+p.amount<2^w ∧ p.bases+f.val<2^w)
    (ticksFit : ∀t : Fin T, p.ticks+t.val<2^w)
    (away : ∀ a,p.reads N a → (∀t : Fin T, a≠p.ticks+t.val) ∧ ∀f : Fin N,a≠p.bases+f.val)
    (sep : ∀t : Fin T,∀ f : Fin N,p.ticks+t.val≠p.bases+f.val)
    (f : Fin N) (pre post : List (Fin N))
    (atRow : FactorAllocation.factors scale cost (List.finRange N)
      (FactorAllocation.owner ht scale cost f)=pre++f::post) :
    let K:=((20*(scale+1)+2)^d)*N
    iterRows factorStep (factorWords w K p) m K (p.bases+f.val)=
      m (p.ticks+(FactorAllocation.owner ht scale cost f).val)+((stream origin pre).length:Word w) := by
  intro K
  let mem := iterRows factorStep (factorWords w K p) m
  apply factor_prefix ht scale cost origin (fun t=>p.ticks+t.val) (fun f=>p.bases+f.val) mem
    (fun _ _ h=>Fin.ext (Nat.add_left_cancel h)) (fun _ _ h=>Fin.ext (Nat.add_left_cancel h)) sep _ f pre post atRow
  apply preserved_rows _ _ _ _ _ m mem rfl (p.reads N) away
  intro i hi same
  have pos : 0<N := (Nat.zero_lt_of_lt f.isLt)
  let u : Fin N := ⟨i%N,Nat.mod_lt _ pos⟩
  obtain ⟨a,b,c,e⟩ := fit u
  have kread := (same _ ⟨u,Or.inl rfl⟩).trans (keyAt u)
  let t := FactorAllocation.owner ht scale cost u
  have oread := (same _ ⟨u,Or.inr (Or.inl rfl)⟩).trans (ownerAt u)
  have cread := (same _ ⟨u,Or.inr (Or.inr rfl)⟩).trans (costAt u)
  have tval : (mem i (p.owners+u.val)).val=t.val := by
    rw [oread]
    exact Fin.val_cast_of_lt (t.isLt.trans_le tFit)
  have kval : (mem i (p.keys+u.val)).val=factorKey scale cost u := by rw [kread,Fin.val_cast_of_lt (keyFit u)]
  rw [show mem (i+1)=factorStep (factorWords w K p) (i:Word w) (mem i) from rfl,
    factorStep_natural p K i _ (hi.trans countFit) (rows ▸ nFit) u.val (i/N) (by rw [rows]) (by rw [rows])
      a b c e (by rw [tval];exact ticksFit t),kval,tval,cread]
  have im := Nat.mod_lt i pos
  by_cases hit : factorKey scale cost u=i/N <;> simp [classRow,im,u,hit,store,Option.guard,t] at *

theorem bucket_readback {N full : ℕ} (owner : Fin full→Fin N)
    (p : BucketBanks) (m : Memory w) (n : ℕ) (within : n≤full)
    (cnt : n<2^w) (size : p.cap<2^w) (width : p.span<2^w) (pos : 0<p.span)
    (active : ∀ i<n,i*p.span≤p.cap) (ordFit : N≤2^w)
    (actual : ∀ b : Fin full, m (p.owners+b.val)=((owner b).val:Word w))
    (fit : ∀ b : Fin full,p.owners+b.val<2^w ∧ p.blocks+b.val<2^w)
    (cFit : ∀ f : Fin N,p.cursors+f.val<2^w)
    (off : ∀ b : Fin full,(∀f : Fin N, p.owners+b.val≠p.cursors+f.val) ∧
       ∀ s : Fin full,p.owners+b.val≠p.blocks+s.val)
    (sep : ∀ f : Fin N,∀ b : Fin full,p.cursors+f.val≠p.blocks+b.val)
    (b : Fin full) (hit : b.val<n) (desc pre post : List (Fin full)) (ordered : desc.Pairwise (· < ·))
    (fiber : ∀ s,s∈desc ↔ owner s=owner b) (index : desc=pre++b::post) :
    iterRows bucketStep (bucketWords w n p) m n (p.blocks+b.val)=m (p.cursors+(owner b).val)+
      (((pre.map (fun q=>bucketLength p.cap p.span q.val)).sum:ℕ):Word w) := by
  let mem := iterRows bucketStep (bucketWords w n p) m
  apply bucket_prefix_truncated within owner (fun f=>p.cursors+f.val) (fun s=>p.blocks+s.val) mem
    (fun _ _ h=>Fin.ext (Nat.add_left_cancel h)) (fun _ _ h=>Fin.ext (Nat.add_left_cancel h)) sep
    _ b hit desc pre post ordered fiber index
  apply preserved_rows _ _ _ _ _ m mem rfl (fun a=>∃s : Fin full,a=p.owners+s.val)
  · rintro a ⟨s,rfl⟩; exact off s
  intro i hi same
  let row : Fin full := ⟨i,hi.trans_le within⟩
  have eqn := (same _ ⟨row,rfl⟩).trans (actual row)
  have val : (mem i (p.owners+i)).val=(owner row).val := by
    rw [show mem i (p.owners+i)=_ from eqn,Fin.val_cast_of_lt ((owner row).isLt.trans_le ordFit)]
  obtain ⟨a,b⟩ := fit row
  rw [show mem (i+1)=bucketStep (bucketWords w n p) (i:Word w) (mem i) from rfl,
    bucketStep_natural p n i _ (hi.trans cnt) width size pos (active _ hi) a b
      (by rw [val];exact cFit _),val]
  simp [bucketRow,hi.trans_le within,store,row]

/-- Combine the two native prefix readbacks. The pointer lookup plus the
original remainder is the actual absolute pin, with no scan over other bits. -/
theorem traced_offset {T : Type} {S N L d span : ℕ} (P : Layout T S N d) (pos : 0< span)
    (ordinal : T→ℕ) (bucket : Fin S→Fin L) (quotient : ∀ j, (bucket j).val=j.val/span)
    (desc : Fin N→List (Fin L)) (sorted : ∀ f,(desc f).Pairwise (· < ·))
    (admit : ∀ f j,bucket j∈desc f ↔ P.origin j=f)
    (factorBase : Fin N→Word w) (bucketBase : Fin L→Word w)
    (factors : ∀ f pre post, P.rows (P.owner f)=pre++f::post →
      factorBase f=((ordinal (P.owner f)*d+(P.header (P.owner f)).length+
        (stream P.origin pre).length:ℕ):Word w))
    (buckets : ∀ j f pre post, desc f=pre++bucket j::post →
      bucketBase (bucket j)=factorBase f+(((pre.map (fun s=>bucketLength S span s.val)).sum:ℕ):Word w))
    (j : Fin S) :
    bucketBase (bucket j)+((j.val%span:ℕ):Word w)=((ordinal (P.tick j)*d+(P.slot j).val:ℕ):Word w) := by
  obtain ⟨xs,ys,atF⟩ := List.append_of_mem ((P.owns (P.origin j) (P.tick j)).mpr rfl)
  obtain ⟨before,after,atB⟩ := List.append_of_mem ((admit (P.origin j) j).mpr rfl)
  rw [buckets _ _ _ _ atB,factors _ _ _ atF,
    slot_at_bucket P pos bucket quotient desc sorted admit j rfl atF atB]
  simp [Layout.tick,Nat.cast_add,add_assoc]

end Hierarchy.GridPinNativeLoops

end OAI
