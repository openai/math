import OAI.Hierarchy.GridPinPublisher
import OAI.Hierarchy.GridPinBankRoom
import OAI.Hierarchy.GridPinPrefixFrames

namespace OAI
/-! # The absolute native pin computed at the physically scheduled occurrence -/

namespace Hierarchy.GridPinPublisher
open Computability.VPVNP.BurstRAM PrivateRAM
open GridThrough FactorPinIntervals GridPinNativeLoops GridPinPrefixMemory
open FactorBucketRAM
open scoped Fin.CommRing Classical
noncomputable section
variable {W r full L S m N k n q d : ℕ}

theorem bucket_visited {S span : ℕ} (pos : 0< span) (j : Fin S) :
    j.val/span<(S+span-1)/span := by
  apply (Nat.lt_div_iff_mul_lt pos).mpr
  have a := Nat.div_mul_le_self j.val span
  have b := j.isLt
  omega

/-- With the real incoming key/owner/length table and immutable ancestor row
preserved, the two native prefix scans give the scheduled absolute address at
every original bit. This phase has no destination-bank hypothesis. -/
theorem scheduled_offsets (P : Plan) (Q : Layout (Cell k n×Fin q) S N d)
    (ht : 0<(n+1)^k*q) (scale : ℕ) (cost : Fin N→Fin m→ℕ) (mem : Memory W)
    (lane : Fin full→Fin N)
    (owner : ∀ f, GridTicks.index (Q.owner f)=FactorAllocation.owner ht scale cost f)
    (order : ∀ t,Q.rows t=FactorAllocation.factors scale cost (List.finRange N) (GridTicks.index t))
    (hlen : ∀t,(Q.header t).length=P.headerSize) (pins : d=P.header.pins)
    (rows : P.factor.items=N) (nt : P.ticks=(n+1)^k*q)
    (countF : P.factors=((20*(scale+1)+2)^m)*N) (countB : P.lanes=L)
    (fcur : P.bucket.cursors=P.factor.bases) (blocks : P.source.blocks=P.bucket.blocks)
    (cap : P.bucket.cap=S) (span : P.source.span=P.bucket.span)
    (within : L≤full) (active : ∀ i<L,i*P.bucket.span≤S)
    (bucket : Fin S→Fin full) (quotient : ∀ j,(bucket j).val=j.val/P.bucket.span)
    (inhabited : ∀ j,(bucket j).val<L) (trueOwner : ∀ j,lane (bucket j)=Q.origin j)
    (pos : 0<P.bucket.span) (countFit : P.factors<2^W) (itemFit : N<2^W)
    (tickFit : P.ticks≤2^W) (boundKey : (20*(scale+1)+2)^m≤2^W)
    (lFit : L<2^W) (spanFit : P.bucket.span<2^W) (sFit : S<2^W)
    (R : BankRoom W P r full) (amount : P.factor.amount<P.factor.stride)
    (keys : ∀ f, P.seeded mem (P.factor.keys+f.val)=(factorKey scale cost f:Word W))
    (owners : ∀ f, P.seeded mem (P.factor.owners+f.val)=((FactorAllocation.owner ht scale cost f).val:Word W))
    (sizes : ∀ f : Fin N, P.seeded mem (P.factor.resource+f.val*P.factor.stride+P.factor.amount)=
      ((intervalBits Q.origin f).length:Word W))
    (initial : ∀ b : Fin full,P.factorized mem (P.bucket.owners+b.val)=((lane b).val:Word W))
    (wholeBlock : ∀ b : Fin full, P.bucket.blocks+b.val<2^W)
    (wholeOff : ∀ b : Fin full,∀ j : Fin full,P.bucket.owners+b.val≠P.bucket.blocks+j.val)
    (wholeSep : ∀ f : Fin N,∀ b : Fin full,P.factor.bases+f.val≠P.bucket.blocks+b.val)
    (j : Fin S) :
    P.bucketed mem (P.source.blocks+j.val/P.source.span)+((j.val%P.source.span:ℕ):Word W)=
      ((GridPinAddressImage.code (Q.address j)).val:Word W) := by
  let desc := fun f=>(List.finRange full).filter (fun b=>lane b=f)
  have fiber (f : Fin N) (b : Fin full) : b∈desc f ↔ lane b=f := by simp [desc]
  have small (f : Fin N) : f.val<P.factor.items := rows ▸ f.isLt
  have tickSmall (t : Fin ((n+1)^k*q)) : t.val<P.ticks := by rw [nt]; exact t.isLt
  have addressSmall (f : Fin N) : f.val*P.factor.stride+P.factor.amount<P.factor.items*P.factor.stride := by
    have le := Nat.mul_le_mul_right P.factor.stride (small f)
    rw [Nat.succ_mul] at le
    omega
  have F (f : Fin N) (pre post : List (Fin N)) (split : Q.rows (Q.owner f)=pre++f::post) :
      P.factorized mem (P.factor.bases+f.val) =
        (((GridTicks.index (Q.owner f)).val*d+(Q.header (Q.owner f)).length+
          (stream Q.origin pre).length:ℕ):Word W) := by
    have fixed := factor_readback ht scale cost Q.origin P.factor rows (P.seeded mem)
      (countF ▸ countFit) itemFit (fun _=>(Fin.isLt _).trans_le boundKey) (nt ▸ tickFit)
      keys owners sizes
      (fun f=>⟨R.address .keys (small f),R.address .owners (small f),
        by simpa [Bank.base,Nat.add_assoc] using R.address .resource (addressSmall f),
        R.address .factors (small f)⟩)
      (fun t=>R.address .ticks (tickSmall t)) (by
        rintro a ⟨u,h | h | h⟩ <;> subst a
        · exact ⟨fun t=>R.ne .keys .ticks (by decide) (small u) (tickSmall t),
            fun f=>R.ne .keys .factors (by decide) (small u) (small f)⟩
        · exact ⟨fun t=>R.ne .owners .ticks (by decide) (small u) (tickSmall t),
            fun f=>R.ne .owners .factors (by decide) (small u) (small f)⟩
        · constructor
          · intro t; simpa [Bank.base,Nat.add_assoc] using R.ne .resource .ticks (by decide) (addressSmall u) (tickSmall t)
          · intro f; simpa [Bank.base,Nat.add_assoc] using R.ne .resource .factors (by decide) (addressSmall u) (small f))
      (fun t f=>R.ne .ticks .factors (by decide) (tickSmall t) (small f)) f pre post
      (by rwa [order,owner] at split)
    change iterRows _ _ _ _ _=_
    rw [countF,fixed,←owner,hlen]
    rw [show P.seeded mem (P.factor.ticks+(GridTicks.index (Q.owner f)).val)=_ from
      seed_readback P.factor.ticks P.header.pins P.headerSize P.ticks mem (R.fit .ticks)
        _ (tickSmall _)]
    simp only [←pins,Nat.cast_add]
  have B (f : Fin N) (b : Fin full) (pre post : List (Fin full)) (atB : desc f=pre++b::post)
      (touched : b.val<L) :
      P.bucketed mem (P.bucket.blocks+b.val)=P.factorized mem (P.factor.bases+f.val)+
        (((pre.map (fun u=>bucketLength S P.bucket.span u.val)).sum:ℕ):Word W) := by
    have eqn := (fiber f b).mp (atB ▸ List.mem_append_right _ List.mem_cons_self)
    have z := bucket_readback lane P.bucket (P.factorized mem) L within lFit (cap ▸ sFit) spanFit pos
      (cap ▸ active) itemFit.le initial (fun s=>⟨R.address .ancestors s.isLt,wholeBlock s⟩)
      (by intro i;rw [fcur];exact R.address .factors (small i))
      (fun s=>⟨by intro f;rw [fcur];exact R.ne .ancestors .factors (by decide) s.isLt (small f),wholeOff s⟩)
      (by rw [fcur];exact wholeSep) b touched (desc f) pre post ((List.pairwise_lt_finRange _).filter _)
      (fun s=>eqn ▸ fiber f s) atB
    simpa only [bucketed,countB,cap,fcur,eqn] using z
  have h := traced_offset Q pos (fun t=>(GridTicks.index t).val) bucket quotient desc
    (fun f=>(List.pairwise_lt_finRange _).filter _) (fun f i=>(fiber f _).trans (by rw [trueOwner]))
    (fun f=>P.factorized mem (P.factor.bases+f.val))
    (fun b=>P.bucketed mem (P.bucket.blocks+b.val)) F
    (fun i f before after atB=>B f (bucket i) before after atB (inhabited i)) j
  have addressCode : (GridPinAddressImage.code (Q.address j)).val=
      (GridTicks.index (Q.tick j)).val*d+(Q.slot j).val := GridPinAddressImage.code_val (Q.tick j) (Q.slot j)
  simpa only [blocks,span,quotient,addressCode] using h

end
end Hierarchy.GridPinPublisher

end OAI
