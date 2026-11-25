import OAI.Hierarchy.GridPinPublisher
import OAI.Hierarchy.GridPinArenaRoom
import OAI.Hierarchy.GridPinReceiverPrefix

namespace OAI
/-! # Interval starts computed from the receiver's four registered word tables -/

namespace Hierarchy.GridPinPublisher
open ThreeFlat RAM RAM.PhysicalProcedure Computability.VPVNP.BurstRAM
open GridThrough FactorPinIntervals GridPinPrefixMemory GridPinNativeLoops FactorBucketRAM
open scoped Fin.CommRing Classical
noncomputable section

variable {k n q S N d m full W : ℕ}

structure CountInputs (P : Plan) (Q : Layout (Cell k n × Fin q) S N d)
    (ht : 0 < (n+1)^k*q) (scale : ℕ) (cost : Fin N → Fin m → ℕ)
    (lane : Fin full → Fin N) (mem : Memory W) : Prop where
  key : ∀ f, mem (P.factor.keys+f.val)=(factorKey scale cost f : Word W)
  owner : ∀ f, mem (P.factor.owners+f.val)=((FactorAllocation.owner ht scale cost f).val : Word W)
  inputLength : ∀ f : Fin N, mem (P.factor.resource+f.val*P.factor.stride+P.factor.amount)=
    ((intervalBits Q.origin f).length : Word W)
  ancestor : ∀ b : Fin full, mem (P.bucket.owners+b.val)=((lane b).val : Word W)

theorem CountInputs.keep {P : Plan} {Q : Layout (Cell k n × Fin q) S N d}
    {ht : 0 < (n+1)^k*q} {scale : ℕ} {cost : Fin N → Fin m → ℕ} {lane : Fin full → Fin N}
    {before after : Memory W} (src : CountInputs P Q ht scale cost lane before)
    (hk : ∀ f : Fin N, after (P.factor.keys+f.val)=before (P.factor.keys+f.val))
    (ho : ∀ f : Fin N, after (P.factor.owners+f.val)=before (P.factor.owners+f.val))
    (hl : ∀ f : Fin N, after (P.factor.resource+f.val*P.factor.stride+P.factor.amount)=
      before (P.factor.resource+f.val*P.factor.stride+P.factor.amount))
    (ha : ∀ b : Fin full, after (P.bucket.owners+b.val)=before (P.bucket.owners+b.val)) :
    CountInputs P Q ht scale cost lane after :=
  ⟨fun f=>(hk f).trans (src.key f),fun f=>(ho f).trans (src.owner f),
    fun f=>(hl f).trans (src.inputLength f),fun b=>(ha b).trans (src.ancestor b)⟩

theorem CountInputs.prefix {P : Plan} {Q : Layout (Cell k n×Fin q) S N d}
    {ht : 0<(n+1)^k*q} {scale : ℕ} {cost : Fin N→Fin m→ℕ} {lane : Fin full→Fin N}
    {mem : Memory W} (src : CountInputs P Q ht scale cost lane mem)
    (items : N=P.factor.items) (ticks : (n+1)^k*q=P.ticks) (fits : P.ticks<2^W)
    (rows : P.factor.items<2^W) (within : P.lanes≤full) : PrefixOwners P mem := by
  refine ⟨?_,?_⟩
  · intro i
    let f := i.cast items.symm
    have rd:=src.owner f
    change mem (P.factor.owners+i.val)=_ at rd
    rw [rd,Fin.val_cast_of_lt ((Fin.isLt _).trans (ticks.trans_lt fits))]
    exact (Fin.isLt _).trans_le ticks.le
  · intro j
    let v : Fin full := ⟨j.val,j.isLt.trans_le within⟩
    have rd:=src.ancestor v
    change mem (P.bucket.owners+j.val)=_ at rd
    rw [rd,Fin.val_cast_of_lt ((Fin.isLt _).trans (items.trans_lt rows))]
    exact (Fin.isLt _).trans_le items.le

variable {scale nparams ell text compact rails stages span : ℕ}

theorem receiver_offsets (Q : Layout (Cell k n × Fin q) S N d)
    (ht : 0 < (n+1)^k*q) (cost : Fin N → Fin (k+2) → ℕ) (lane : Fin full → Fin N)
    (dispatch : ∀ f, GridTicks.index (Q.owner f)=FactorAllocation.owner ht scale cost f)
    (order : ∀ t,Q.rows t=FactorAllocation.factors scale cost (List.finRange N) (GridTicks.index t))
    (bucket : Fin S → Fin full) (quotient : ∀ j,(bucket j).val=j.val/span)
    (trueOwner : ∀ j,lane (bucket j)=Q.origin j)
    (P : Plan) (actual : P=canonical scale k n q d nparams ell text compact rails S N stages full span)
    (lens : ∀ t,(Q.header t).length=P.headerSize)
    (R : GridPinArena.Scalars (64*scale) P S full ((20*(scale+1)+2)^(k+2)) (GridPinArena.slab scale))
    (small : GridPinArena.Small scale P S full (stages*full) ((20*(scale+1)+2)^(k+2)))
    (mem : Memory (64*scale)) (src : CountInputs P Q ht scale cost lane mem) (j : Fin S) :
    P.bucketed mem (P.source.blocks+j.val/P.source.span)+((j.val%P.source.span : ℕ) : Word (64*scale))=
      ((GridPinAddressImage.code (Q.address j)).val : Word (64*scale)) := by
  subst P
  let P := canonical scale k n q d nparams ell text compact rails S N stages full span
  let geo : PrefixGeometry (64*scale) P full :=
    ⟨R.factorsFit.le,R.itemsFit,fun h => Nat.pos_of_mul_pos_left h,R.within,rfl⟩
  have own (f : Fin P.factor.items) : (mem (P.factor.owners+f.val)).val<P.ticks := by
    let v : Fin N := ⟨f.val,f.isLt⟩
    let t := FactorAllocation.owner ht scale cost v
    have bound : t.val < P.ticks := t.isLt
    have read : mem (P.factor.owners+f.val)=(t.val : Word (64*scale)) := src.owner v
    exact ((congrArg Fin.val read).trans (Fin.val_cast_of_lt (bound.trans R.ticksFit))).trans_lt bound
  have lenAddr (f : Fin N) : f.val*(k+2)+1<N*(k+2) := by
    have h:=Nat.mul_le_mul_right (k+2) f.isLt
    rw [Nat.succ_mul] at h
    omega
  have Nslab : N≤GridPinArena.slab scale :=
    (Nat.le_mul_of_pos_right N (by omega : 0<k+2)).trans small.resource
  apply scheduled_offsets P Q ht scale cost mem lane dispatch order lens rfl rfl rfl rfl rfl rfl rfl rfl rfl
    R.within R.active bucket quotient (fun i=>by rw [quotient];exact bucket_visited R.spanPos i) trueOwner
    R.spanPos R.factorsFit R.itemsFit R.ticksFit.le R.classesFit.le R.lanesFit R.spanFit R.bitsFit R.bank
    (by change 1<k+2;omega)
  · intro f; exact (R.bank.seeded_read mem .keys (by decide) _ f.isLt).trans (src.key f)
  · intro f; exact (R.bank.seeded_read mem .owners (by decide) _ f.isLt).trans (src.owner f)
  · intro f
    have read := R.bank.seeded_read mem .resource (by decide) _ (lenAddr f)
    change P.seeded mem (P.factor.resource+(f.val*(k+2)+1))=mem (P.factor.resource+(f.val*(k+2)+1)) at read
    have actual : mem (P.factor.resource+f.val*(k+2)+1)=((intervalBits Q.origin f).length:Word (64*scale)) :=
      src.inputLength f
    change P.seeded mem (P.factor.resource+f.val*(k+2)+1)=_
    rw [Nat.add_assoc] at actual ⊢
    exact read.trans actual
  · intro b; exact (R.bank.factorized_read geo mem own .ancestors (by decide) (by decide) _ b.isLt).trans
      (src.ancestor b)
  · intro b; exact (Nat.add_lt_add_left (b.isLt.trans_le small.full) _).trans (R.window.fit .blocks)
  · intro b c; exact R.window.ne .ancestors .blocks (by decide)
      (b.isLt.trans_le small.full) (c.isLt.trans_le small.full)
  · intro f b; exact R.window.ne .factors .blocks (by decide)
      (f.isLt.trans_le Nslab) (b.isLt.trans_le small.full)

end
end Hierarchy.GridPinPublisher

end OAI
