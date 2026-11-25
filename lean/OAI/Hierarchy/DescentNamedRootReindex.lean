import OAI.Hierarchy.DescentPhysicalRootBook

namespace OAI
/-! # Transporting the actual reset root receiver, book, and source arrays together -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver

structure IndexedRoots (D cap N n r c H G K R M hm lb tiny field Ht w : ℕ) where
  receiver : Receiver D cap N n r c H G K R M hm lb tiny field Ht w
  book : RootBook n r D (2^r) cap field
  prepared : receiver.PreparedFits book
  sources : RootSources D (2^r) cap

namespace IndexedRoots
variable {D cap N n r c H G K R M hm lb tiny field Ht w : ℕ}
  {D' cap' n' r' c' H' G' Ht' : ℕ}
variable (x : IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w)
  (degree : D=D') (capacity : cap=cap') (dimension : n=n') (residual : r=r')
  (depth : c=c') (hosts : H=H') (groups : G=G') (height : Ht=Ht')

def reindex : IndexedRoots D' cap' N n' r' c' H' G' K R M hm lb tiny field Ht' w := by
  cases degree
  cases capacity
  cases dimension
  cases residual
  cases depth
  cases hosts
  cases groups
  cases height
  exact x

theorem reindex_fields :
    let z:=x.reindex degree capacity dimension residual depth hosts groups height
    HEq z.receiver x.receiver ∧ HEq z.book x.book ∧ HEq z.prepared x.prepared ∧ HEq z.sources x.sources :=by
  cases degree
  cases capacity
  cases dimension
  cases residual
  cases depth
  cases hosts
  cases groups
  cases height
  exact ⟨HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩
theorem reindex_reindex {D₂ cap₂ n₂ r₂ c₂ H₂ G₂ Ht₂ : ℕ}
    (degree₂ : D'=D₂) (capacity₂ : cap'=cap₂) (dimension₂ : n'=n₂) (residual₂ : r'=r₂)
    (depth₂ : c'=c₂) (hosts₂ : H'=H₂) (groups₂ : G'=G₂) (height₂ : Ht'=Ht₂) :
    (x.reindex degree capacity dimension residual depth hosts groups height).reindex
        degree₂ capacity₂ dimension₂ residual₂ depth₂ hosts₂ groups₂ height₂ =
      x.reindex (degree.trans degree₂) (capacity.trans capacity₂) (dimension.trans dimension₂)
        (residual.trans residual₂) (depth.trans depth₂) (hosts.trans hosts₂) (groups.trans groups₂) (height.trans height₂) :=by
  subst_vars
  rfl

end IndexedRoots

theorem reindex_roots {D cap N n r c H G K R M hm lb tiny field Ht w D' cap' n' r' c' H' G' Ht' : ℕ}
    (rc : Receiver D cap N n r c H G K R M hm lb tiny field Ht w)
    (book : RootBook n r D (2^r) cap field) (fit : rc.PreparedFits book) (src : RootSources D (2^r) cap)
    (degree : D=D') (capacity : cap=cap') (dimension : n=n') (residual : r=r') (depth : c=c')
    (hosts : H=H') (groups : G=G') (height : Ht=Ht') :
    ∃ (rc' : Receiver D' cap' N n' r' c' H' G' K R M hm lb tiny field Ht' w)
      (book' : RootBook n' r' D' (2^r') cap' field) (fits' : rc'.PreparedFits book')
      (src' : RootSources D' (2^r') cap'),
      HEq rc' rc ∧ HEq book' book ∧ HEq src' src ∧ HEq fits' fit :=by
  let x:IndexedRoots D cap N n r c H G K R M hm lb tiny field Ht w:=⟨rc,book,fit,src⟩
  let y:=x.reindex degree capacity dimension residual depth hosts groups height
  obtain ⟨a,b,p,s⟩:=x.reindex_fields degree capacity dimension residual depth hosts groups height
  exact ⟨y.receiver,y.book,y.prepared,y.sources,a,b,s,p⟩

end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
