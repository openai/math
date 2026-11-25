import OAI.Hierarchy.TaggedWideStripParties
import OAI.Hierarchy.TaggedWireChosenPackets
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # Native low endpoint of the inactive carry after an actual strip purchase -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.SiteDirectory
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.RAM.DescriptorExpr
open WireTelescope.ChosenPackets AdaptiveProbe Probe ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
variable {h S k W : ℕ} {A : Type} [Fintype A]

/-- The unoriented comparison uses both printed endpoints. Every demand
is charged once even when multiple wanted axes have the same endpoints. -/
def compareRole (left right site neighbor amount : Expr) : Expr :=
  .branch .eq left site (.branch .eq right neighbor amount (.lit 0))
    (.branch .eq left neighbor (.branch .eq right site amount (.lit 0)) (.lit 0))

private def scanWants : (n : ℕ)→(Fin n→Expr)→Expr
  | 0,_=>.lit 0
  | n+1,f=>.op .add (f 0) (scanWants n (fun i=>f i.succ))

private theorem scanWants_eval (m : Memory W) (row : Word W) (n : ℕ) (f : Fin n→Expr) :
    (scanWants n f).eval m row=∑i,(f i).eval m row := by
  induction n with
  | zero=>simp [scanWants,Expr.eval]
  | succ n ih=>rw [Fin.sum_univ_succ];simp [scanWants,Expr.eval,RowOp.opcode,BinaryOp.eval,ih]

def released (edge : A→Chord k) (party : Fin k→Expr) (site neighbor amount : Expr) : Expr :=
  scanWants (Fintype.card A) (fun i=>
    let c:=edge ((Fintype.equivFin A).symm i)
    compareRole (party c.val.1) (party c.val.2) site neighbor amount)

private theorem asWord_eq (a b : Fin S) (limit : S≤2^W) :
    ((a.val:Word W)=(b.val:Word W)) ↔ a=b := by
  rw [Fin.ext_iff,Fin.val_cast_of_lt (a.isLt.trans_le limit),Fin.val_cast_of_lt (b.isLt.trans_le limit),Fin.ext_iff]

private theorem sorted_eq (a b : Fin S) (ne : a≠b) (g : Chord S) :
    orderedEnds a b ne=g ↔ (a=g.val.1 ∧ b=g.val.2) ∨ (a=g.val.2 ∧ b=g.val.1) := by
  rcases g with ⟨⟨l,u⟩,lo⟩
  dsimp only
  by_cases h:a<b
  · simp only [orderedEnds,dite_eq_left h,Subtype.mk.injEq,Prod.mk.injEq]
    constructor
    · exact Or.inl
    · rintro (hit|⟨rfl,rfl⟩)
      · exact hit
      · exact False.elim ((not_lt_of_ge lo.le) h)
  · simp only [orderedEnds,dite_eq_right h,Subtype.mk.injEq,Prod.mk.injEq]
    constructor
    · exact fun z=>Or.inr ⟨z.2,z.1⟩
    · rintro (⟨rfl,rfl⟩|hit)
      · exact False.elim (h lo)
      · exact ⟨hit.2,hit.1⟩

private theorem compare_read (m : Memory W) (row : Word W) (a b s t : Fin S) (limit : S≤2^W)
    (left right site neighbor amount : Expr) (weight : ℕ)
    (leftRead : left.eval m row=(a.val:Word W)) (rightRead : right.eval m row=(b.val:Word W))
    (siteRead : site.eval m row=(s.val:Word W)) (neighborRead : neighbor.eval m row=(t.val:Word W))
    (unitRead : amount.eval m row=(weight:Word W)) (ne : s≠t) :
    (compareRole left right site neighbor amount).eval m row=
      if (a=s ∧ b=t) ∨ (a=t ∧ b=s) then (weight:Word W) else 0 := by
  by_cases hs:a=s <;> by_cases ht:a=t <;> by_cases ls:b=s <;> by_cases lt:b=t <;>
    simp_all [compareRole,Expr.eval,Comparison.test,beq_iff_eq,asWord_eq _ _ limit]

/-- Take a class coefficient at the actual selected candidate row. The
static program knows only its finite local directed role list. Global
site numbers and the two queried endpoints come from native words. -/
theorem released_read (m : Memory W) (row : Word W) (edge : A→Chord k) (place : Fin k ↪ Fin S)
    (party : Fin k→Expr) (site neighbor amount : Expr) (weight : ℕ) (g : Chord S)
    (limit : S≤2^W) (reads : ∀i,(party i).eval m row=((place i).val:Word W))
    (siteRead : site.eval m row=(g.val.1.val:Word W)) (neighborRead : neighbor.eval m row=(g.val.2.val:Word W))
    (unitRead : amount.eval m row=(weight:Word W)) :
    (released edge party site neighbor amount).eval m row=
      (optionWidths (fun a=>physicalChord place (edge a)) (fun _=>weight) g : ℕ) := by
  rw [released,scanWants_eval,←(Fintype.equivFin A).sum_comp]
  simp only [Equiv.symm_apply_apply,optionWidths,Finsupp.finsetSum_apply,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  let c:=edge a
  have eq:=compare_read m row (place c.val.1) (place c.val.2) g.val.1 g.val.2 limit _ _ _ _ _ weight
    (reads c.val.1) (reads c.val.2) siteRead neighborRead unitRead g.property.ne
  rw [eq]
  have aligned : physicalChord place c=g ↔
      (place c.val.1=g.val.1 ∧ place c.val.2=g.val.2) ∨
      (place c.val.1=g.val.2 ∧ place c.val.2=g.val.1) :=
    sorted_eq _ _ (place.injective.ne c.property.ne) g
  by_cases hit : physicalChord place (edge a)=g
  · simp only [ite_eq_left (aligned.mp hit),Finsupp.single_apply,ite_eq_left hit]
  · simp only [ite_eq_right (fun p=>hit (aligned.mpr p)),Finsupp.single_apply,ite_eq_right hit,Nat.cast_zero]

theorem Placed.released_before {F : Type} [Field F] (P : Placed F S) (copies : ℕ)
    (m : Memory W) (row : Word W) (party : Fin P.sites→Expr) (site neighbor : Expr) (g : Chord S)
    (limit : S≤2^W) (read : ∀i,(party i).eval m row=((P.place i).val:Word W))
    (left : site.eval m row=(g.val.1.val:Word W)) (right : neighbor.eval m row=(g.val.2.val:Word W)) :
    (released (fun a=>P.edge (P.wanted a)) party site neighbor (.lit (copies*P.data.width))).eval m row=
      (P.wants copies g:Word W) :=
  released_read _ _ _ _ _ _ _ _ _ _ limit read left right rfl

/-- Gather every wanted endpoint at the historical elected candidate. The
site and neighbor belong to the current public site-role row. -/
def lowBefore (edge : A→Chord k) (party : Fin k→Expr) (elected site neighbor amount : Expr) : Expr :=
  released edge (fun i=>(party i).atRow elected)
    (.branch .lt site neighbor site neighbor) (.branch .lt site neighbor neighbor site) amount

theorem lowBefore_read (m : Memory W) (row : Word W) (edge : A→Chord k) (place : Fin k ↪ Fin S)
    (party : Fin k→Expr) (elected site neighbor amount : Expr) (loc other : Fin S) (ne : loc≠other)
    (weight : ℕ) (limit : S≤2^W) (reads : ∀i,(party i).eval m (elected.eval m row)=((place i).val:Word W))
    (siteRead : site.eval m row=(loc.val:Word W)) (neighborRead : neighbor.eval m row=(other.val:Word W))
    (unitRead : amount.eval m row=(weight:Word W)) :
    (lowBefore edge party elected site neighbor amount).eval m row=
      (optionWidths (fun a=>physicalChord place (edge a)) (fun _=>weight) (orderedEnds loc other ne):ℕ) := by
  have cmp : ((loc.val:Word W)<(other.val:Word W)) ↔ loc<other := by
    simp only [Fin.lt_def,Fin.val_cast_of_lt (loc.isLt.trans_le limit),Fin.val_cast_of_lt (other.isLt.trans_le limit)]
  apply released_read _ _ _ _ _ _ _ _ _ _ limit _ _ _ unitRead
  · intro i
    simpa only [eval_atRow] using reads i
  · by_cases h:loc<other <;> simp [Expr.eval,Comparison.test,orderedEnds,siteRead,neighborRead,cmp,h]
  · by_cases h:loc<other <;> simp [Expr.eval,Comparison.test,orderedEnds,siteRead,neighborRead,cmp,h]

theorem Placed.lowBefore_wants {F : Type} [Field F] (P : Placed F S) (copies : ℕ)
    (m : Memory W) (row : Word W) (party : Fin P.sites→Expr) (elected site neighbor : Expr)
    (i : Fin P.sites) (other : Fin S) (ne : P.place i≠other) (limit : S≤2^W)
    (read : ∀a,(party a).eval m (elected.eval m row)=((P.place a).val:Word W))
    (here : site.eval m row=((P.place i).val:Word W)) (opposite : neighbor.eval m row=(other.val:Word W)) :
    (lowBefore (fun a=>P.edge (P.wanted a)) party elected site neighbor (.lit (copies*P.data.width))).eval m row=
      (P.wants copies (orderedEnds (P.place i) other ne):Word W) :=
  lowBefore_read _ _ _ P.place _ _ _ _ _ _ _ ne _ limit read here opposite rfl

/-- Compiling a shape-local party into its genuine global-numbering cell.
The static order of the two geometries is allowed to differ. -/
def partyField {I : Type} [Fintype I] {k : ℕ} (base h d : ℕ) (name : ColumnSite I k≃Fin (Fintype.card (ColumnSite I k)))
    (col : I→Expr) (i : Fin (Fintype.card (ColumnSite I k))) : Expr :=
  cell base h d (name.symm i).2 (col (name.symm i).1)

theorem payload_partyField {h d k base : ℕ} (π : Equiv.Perm (Fin (2^h)))
    (name : ColumnSite (PayloadStrip.Columns (Stages h d)) k≃Fin (Fintype.card (ColumnSite (PayloadStrip.Columns (Stages h d)) k)))
    (col : PayloadStrip.Columns (Stages h d)→Expr) (m : Memory W) (p : Fin (2^h))
    (ready : HistoryRoles.RoleROM.Mounted base (table h d k) m) (fit : size h d k≤2^W)
    (measured : ∀c,(col c).eval m (p.val:Word W)=((Fintype.equivFin _ (payloadPlace π p c)).val:Word W))
    (i : Fin (Fintype.card (ColumnSite (PayloadStrip.Columns (Stages h d)) k))) :
    (partyField base h d name col i).eval m (p.val:Word W)=
      (((name.symm.toEmbedding.trans (Strip.ballEmbedding (payloadParties (d:=d) (k:=k) π) p)) i).val:Word W) :=
  payload_site π m p (name.symm i) _ ready fit (measured _)

theorem bought_partyField {h d k depth base : ℕ} (π : Equiv.Perm (Fin (2^h)))
    (sampler : PurchaseSampler) (mark : StageAt h d→Fin k×Bool→Finset (Fin (2^h)))
    (unique : ∀s c c' r,r∈mark s c → r∈mark s c'→c=c')
    (name : ColumnSite (ChainStrip.Columns depth) k≃Fin (Fintype.card (ColumnSite (ChainStrip.Columns depth) k)))
    (col : ChainStrip.Columns depth→Expr) (m : Memory W) (p : LiveChains sampler π depth mark) (row : Word W)
    (ready : HistoryRoles.RoleROM.Mounted base (table h d k) m) (fit : size h d k≤2^W)
    (measured : ∀c,(col c).eval m row=((Fintype.equivFin (Columns h d)
      (stageOrd (allStripColumns sampler π depth mark unique (p,c)))).val:Word W))
    (i : Fin (Fintype.card (ColumnSite (ChainStrip.Columns depth) k))) :
    (partyField base h d name col i).eval m row=
      (((name.symm.toEmbedding.trans (Strip.ballEmbedding (boughtParties π sampler mark unique) p)) i).val:Word W) :=
  bought_site π sampler mark unique m p (name.symm i) row _ ready fit (measured _)

/-- Bounding the finite additive scan needs no register or word-size bound. -/
private theorem scanWants_work (n bound : ℕ) (f : Fin n→Expr) (small : ∀i,(f i).work≤bound) :
    (scanWants n f).work≤1+n*(bound+1) := by
  induction n with
  | zero=>simp [scanWants,Expr.work]
  | succ n ih=>
    have rest:=ih (fun i=>f i.succ) (fun i=>small _)
    have first:=small 0
    simp only [scanWants,Expr.work,Nat.succ_mul]
    omega

theorem released_work (edge : A→Chord k) (party : Fin k→Expr) (site neighbor amount : Expr)
    (bound : ℕ) (same : ∀a,(party a).work≤bound) :
    (released edge party site neighbor amount).work≤
      1+Fintype.card A*(4*bound+2*site.work+2*neighbor.work+2*amount.work+8) := by
  apply scanWants_work
  intro a
  let e:=edge ((Fintype.equivFin A).symm a)
  have l:=same e.val.1
  have r:=same e.val.2
  change (compareRole (party e.val.1) (party e.val.2) site neighbor amount).work≤_
  simp only [compareRole,Expr.work]
  omega

end Hierarchy.ProbeStage.CoreBoard.SiteDirectory
end

end OAI
