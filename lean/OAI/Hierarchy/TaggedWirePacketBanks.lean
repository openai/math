import OAI.Hierarchy.TaggedWirePacketGatheredOpcode

namespace OAI
/-! # Every bank of the actual scoped packet header is resident below the sparse scatter -/
namespace Hierarchy.ProtocolRAM.PacketScan
variable {n W out : ℕ}

theorem earlier_fits (key amount : Fin n→Expr) (seek : Expr)
    (kh : ∀i,(key i).Fits W out) (ah : ∀i,(amount i).Fits W out) (target : seek.Fits W out) :
    ∀k,(earlier key amount seek k).Fits W out := by
  intro k;induction k with
  | zero=>trivial
  | succ k ih=>
    change _ ∧ _
    refine ⟨ih,?_⟩
    by_cases h:k<n
    · simp [h,Expr.Fits,kh,ah,target]
    · simp [h,Expr.Fits]

theorem first_fits (seek : Expr) (target : seek.Fits W out) (xs : List Expr)
    (entries : ∀e∈xs,e.Fits W out) : (first seek xs).Fits W out := by
  induction xs with
  | nil=>trivial
  | cons x xs ih=>
    have head:=entries x (by simp)
    have tail:=ih (fun e he=>entries e (by simp [he]))
    exact ⟨head,target,trivial,trivial,tail⟩

end Hierarchy.ProtocolRAM.PacketScan

namespace Hierarchy.WireTelescope.PacketTurns.Operands
open ProtocolRAM
variable {n t D W out : ℕ} {len : Fin n→ℕ} (o : Operands len) (ord : Fin t≃Σi,Fin (len i))

structure Resident (W out : ℕ) : Prop where
  old : ∀i b,(o.oldSite i b).Fits W out
  width : ∀i,(o.width i).Fits W out
  key : ∀i q,(o.edge i q).Fits W out
  site : ∀i q b,(o.endSite i q b).Fits W out

variable (res : o.Resident W out)
include res

theorem site_fits (i : Fin n) (j : ℕ) : (o.site i j).Fits W out := by
  unfold site
  split <;> first | exact res.old _ _ | split
  all_goals first | exact res.old _ _ | split
  all_goals simp [Expr.Fits,res.old,res.site]

theorem offset_fits (i : Fin n) (q : Fin (len i)) : (o.offset ord i q).Fits W out :=
  PacketScan.earlier_fits _ _ _ (fun _=>res.key _ _) (fun _=>res.width _) (res.key _ _) _

theorem aggregate_fits (i : Fin n) (q : Fin (len i)) : (o.aggregateStart ord i q).Fits W out :=
  PacketScan.earlier_fits (W:=W) (out:=out) (fun _ : Fin t=>.lit 0) (o.priorAmount ord i q) (.lit 0)
    (fun _=>trivial) (fun _=>by simp [priorAmount,Expr.Fits,res.key,res.site,res.width])
    trivial _

theorem low_fits (x y : Expr) (xf : x.Fits W out) (yf : y.Fits W out) :
    (o.aggregateWidth ord x y).Fits W out :=
  PacketScan.earlier_fits (W:=W) (out:=out) (fun _ : Fin t=>.lit 0) (o.matchingAmount ord x y) (.lit 0)
    (fun _=>trivial) (fun _=>by simp [matchingAmount,Expr.Fits,res.site,res.width,xf,yf])
    trivial _

variable (width nbr : Fin D→Expr) (wf : ∀q,(width q).Fits W out) (nf : ∀q,(nbr q).Fits W out)
include wf nf
omit res in
theorem neighbor_fits (seek : Expr) (sf : seek.Fits W out) : (neighborSector n width nbr seek).Fits W out := by
  refine ⟨trivial,PacketScan.first_fits (W:=W) (out:=out) (.lit 1) trivial
    (List.ofFn (fun q=>PacketNeighbor.compare (width q) (nbr q) seek)) ?_⟩
  intro x mem
  obtain ⟨q,rfl⟩:=List.mem_ofFn.mp mem
  simp [PacketNeighbor.compare,Expr.Fits,wf,nf,sf]

theorem link_fits (i : Fin n) (q : Fin (len i)) (j : ℕ) (a : Bool) :
    (o.gatheredLink ord width nbr i q (o.site i j) a).Fits W out := by
  cases a
  · exact ⟨res.site _ _ _,site_fits o res _ _,neighbor_fits (n:=n) width nbr wf nf _ (res.site _ _ _),
      neighbor_fits (n:=n) width nbr wf nf _ (res.site _ _ _)⟩
  · exact ⟨aggregate_fits o ord res _ _,offset_fits o ord res _ _⟩

theorem gathered_fits (i : Fin n) (j : ℕ) (a b : Bool) :
    (o.gatheredSide ord width nbr i j a b).Fits W out := by
  have ok (q : Fin (len i)):=link_fits o ord res width nbr wf nf i q j b
  unfold gatheredSide
  cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals split
  all_goals first | exact ok _ | trivial | split
  all_goals first | exact ok _ | trivial

theorem words_fits (i : Fin n) (j : ℕ) (f : Fin 7) : (o.gatheredWords ord width nbr i j f).Fits W out := by
  fin_cases f <;> simp only [gatheredWords] <;> first
    | exact gathered_fits o ord res width nbr wf nf i j false false
    | exact gathered_fits o ord res width nbr wf nf i j true false
    | exact gathered_fits o ord res width nbr wf nf i j false true
    | exact gathered_fits o ord res width nbr wf nf i j true true
    | exact res.width i
    | exact site_fits o res i j
    | trivial

theorem column_fits (party : Expr) (pf : party.Fits W out) (f : Fin ((n*3)*5)) :
    (o.column (o.gatheredWords ord width nbr) party f).Fits W out := by
  dsimp only [column]
  split
  · exact ⟨res.width _,trivial,trivial,site_fits o res _ _,pf,words_fits o ord res width nbr wf nf _ _ _,trivial⟩
  · trivial

end Hierarchy.WireTelescope.PacketTurns.Operands

end OAI
