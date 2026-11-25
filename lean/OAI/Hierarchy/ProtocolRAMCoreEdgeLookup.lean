import OAI.Hierarchy.ProbeCoreBoard
import OAI.Hierarchy.ProtocolRAMBinarySpan
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # A format-only inverse directory for the physical core catalogue -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe
open ThreeFlat.RAM
open scoped Fin.CommRing Classical

variable {h d k R w : ℕ} {S : PurchaseSampler}

abbrev AxisPair (k : ℕ) := {ab : Fin k × Fin k // ab.1<ab.2}
abbrev Channel (D N k : ℕ) :=
  (Fin k×Bool) ⊕ ((AxisPair k×(Bool×Bool)) ⊕ (ColumnLayer k ⊕ ((Fin D×ColumnLayer k) ⊕ (Fin N×ColumnLayer k))))

def radius {D N k : ℕ} (i : Fin k) (s : Bool) : Channel D N k := .inl (i,s)
def cross {D N k : ℕ} (a : AxisPair k) (s t : Bool) : Channel D N k := .inr (.inl (a,s,t))
def fixed {D N k : ℕ} (l : ColumnLayer k) : Channel D N k := .inr (.inr (.inl l))
def sample {D N k : ℕ} (digit : Fin D) (l : ColumnLayer k) : Channel D N k := .inr (.inr (.inr (.inl (digit,l))))
def tile {D N k : ℕ} (t : Fin N) (l : ColumnLayer k) : Channel D N k := .inr (.inr (.inr (.inr (t,l))))

def touches (e : Fixed h d) (c : Columns h d) := e.val.1=c ∨ e.val.2=c

/-- Each actual fixed identification appears from either incident endpoint in
the same immutable matching directory, independent of the active permutation. -/
theorem touches_unique {c : Columns h d} {e f : Fixed h d} (he : touches e c) (hf : touches f c) : e=f := by
  rcases e with ⟨⟨a,b⟩,ab,lt⟩
  rcases f with ⟨⟨x,y⟩,xy,order⟩
  change a=c ∨ b=c at he
  change x=c ∨ y=c at hf
  let fabric:=permutationFabric h d
  have unique {u v s : Columns h d} (H : fabric.fixedAll (fabricBoard h d u) (fabricBoard h d v))
      (K : fabric.fixedAll (fabricBoard h d u) (fabricBoard h d s)) : v=s :=
    (fabricBoard h d).injective (fabric.all_fixed_unique _ _ _ H K)
  rcases he with rfl|rfl <;> rcases hf with h|h <;> subst_vars
  · exact Subtype.ext (Prod.ext rfl (unique ab xy))
  · have same := unique ab (fabric.fixedAll_symm _ _ xy)
    subst_vars
    exact (lt_asymm lt order).elim
  · have same := unique (fabric.fixedAll_symm _ _ ab) xy
    subst_vars
    exact (lt_asymm lt order).elim
  · exact Subtype.ext (Prod.ext (unique (fabric.fixedAll_symm _ _ ab) (fabric.fixedAll_symm _ _ xy)) rfl)

def matching (c : Columns h d) : Option (Fixed h d) :=
  if H : ∃ e,touches e c then some H.choose else none

theorem matching_read (c : Columns h d) (e : Fixed h d) (here : touches e c) : matching c=some e := by
  have exists' : ∃ e,touches e c := ⟨e,here⟩
  simp only [matching,dite_eq_left exists',Option.some.injEq]
  exact touches_unique exists'.choose_spec here

/-- Duplicate digits of a sampler list name the very same physical core edge. -/
def neighbor (S : PurchaseSampler) (c : Columns h d) (digit : Fin S.degree) : Option (Sample S h d) :=
  match c with
  | .inr (.inl ⟨t,g,.inr o⟩) =>
    let xs:=S.rows (stageAt h d t).span o
    if H : digit.val<xs.length then some ⟨t,g,o,⟨xs[digit.val],List.getElem_mem H⟩⟩ else none
  | _ => none

theorem neighbor_read (S : PurchaseSampler) (t : StageAt h d) (g : (stageAt h d t).Group)
    (o i : Fin (stageAt h d t).span) (digit : Fin S.degree) (ok : digit.val<(S.rows _ o).length)
    (hit : (S.rows _ o)[digit.val]=i) :
    neighbor S (outputCol t g o) digit=some ⟨t,g,o,⟨i,hit ▸ List.getElem_mem ok⟩⟩ := by
  subst i
  simp [neighbor,outputCol,ok]

private def onColumn (j : ℕ) (f : Columns h d→Option (Edges S h d k)) : Option (Edges S h d k) :=
  if fit : j<Fintype.card (Columns h d) then f ((Fintype.equivFin _).symm ⟨j,fit⟩) else none

private theorem onColumn_at (c : Columns h d) (f : Columns h d→Option (Edges S h d k)) :
    onColumn ((Fintype.equivFin _) c).val f=f c := by
  rw [onColumn,dite_eq_left ((Fintype.equivFin _) c).isLt]
  exact congrArg f ((Fintype.equivFin _).symm_apply_apply c)

def resolve (S : PurchaseSampler) (h d k : ℕ) :
    Channel S.degree (Stages h d) k→ℕ→Option (Edges S h d k)
  | .inl axis,j => onColumn j (fun c=>some (.inl (.inl (c,axis))))
  | .inr (.inl datum),j => onColumn j (fun c=>some (.inl (.inr (.inl (c,datum)))))
  | .inr (.inr (.inl l)),j => onColumn j (fun c=>(matching c).map (fun e=>.inl (.inr (.inr (.inl (e,l))))))
  | .inr (.inr (.inr (.inl (digit,l)))),j => onColumn j (fun c=>(neighbor S c digit).map (fun e=>.inl (.inr (.inr (.inr (e,l))))))
  | .inr (.inr (.inr (.inr (t,l)))),j => if H : j<2^h then some (.inr ((⟨j,H⟩,t),l)) else none

theorem resolve_radius (c : Columns h d) (i : Fin k) (s : Bool) :
    resolve S h d k (radius i s) ((Fintype.equivFin _) c).val=some (.inl (.inl (c,i,s))) :=
  onColumn_at (S:=S) (k:=k) c (fun x=>some (.inl (.inl (x,i,s))))

theorem resolve_cross (c : Columns h d) (a : AxisPair k) (s t : Bool) :
    resolve S h d k (cross a s t) ((Fintype.equivFin _) c).val=some (.inl (.inr (.inl (c,a,s,t)))) :=
  onColumn_at (S:=S) (k:=k) c (fun x=>some (.inl (.inr (.inl (x,a,s,t)))))

theorem resolve_fixed (c : Columns h d) (e : Fixed h d) (here : touches e c) (l : ColumnLayer k) :
    resolve S h d k (fixed l) ((Fintype.equivFin _) c).val=some (.inl (.inr (.inr (.inl (e,l))))) := by
  simp only [resolve,fixed,onColumn_at,matching_read c e here,Option.map_some]

theorem resolve_sample (c : Columns h d) (x : Fin S.degree) (e : Sample S h d) (hit : neighbor S c x=some e)
    (l : ColumnLayer k) :
    resolve S h d k (sample x l) ((Fintype.equivFin _) c).val=some (.inl (.inr (.inr (.inr (e,l))))) := by
  simp only [resolve,sample,onColumn_at,hit,Option.map_some]

theorem resolve_tile (p : Fin (2^h)) (t : StageAt h d) (l : ColumnLayer k) :
    resolve S h d k (tile t l) p.val=some (.inr ((p,t),l)) := by simp [resolve,tile,p.isLt]

/-- One slab for every static local kind, with one cell per possible source
column or original record. No slab indexes a pair of global columns. -/
def positions (h d : ℕ) := max (Fintype.card (Columns h d)) (2^h)
def stride (h d : ℕ) := ProtocolRAMPurchaseSampler.span (positions h d)
def words (S : PurchaseSampler) (h d k : ℕ) :=
  Fintype.card (Channel S.degree (Stages h d) k)*stride h d

def bank (base : ℕ) (kind : Channel S.degree (Stages h d) k) : Bank :=
  ⟨base+((Fintype.equivFin _) kind).val*stride h d,ProtocolRAMPurchaseSampler.bits (positions h d)⟩

def field (base : ℕ) (kind : Channel S.degree (Stages h d) k) (key : Expr) : Expr :=
  .lookup (bank (h:=h) (d:=d) (S:=S) base kind) key

def cell (order : Fin R≃Edges S h d k) (kind : Channel S.degree (Stages h d) k) (j : ℕ) :=
  ((resolve S h d k kind j).map (fun e=>(order.symm e).val)).getD R

def mount (base : ℕ) (order : Fin R≃Edges S h d k) (m : Memory w) : Memory w :=
  fillSegment base (words S h d k) (fun a=>
    let offset:=a-base
    if H : offset/stride h d<Fintype.card (Channel S.degree (Stages h d) k)
      then (cell order ((Fintype.equivFin _).symm ⟨_,H⟩) (offset%stride h d):Word w) else 0) m

def Loaded (base : ℕ) (order : Fin R≃Edges S h d k) (m : Memory w) : Prop :=
  ∀ (t : Channel S.degree (Stages h d) k) (j : Fin (positions h d)),
    m ((bank (S:=S) (h:=h) (d:=d) base t).base+j.val)=(cell order t j.val:Word w)

theorem mount_loaded (base : ℕ) (order : Fin R≃Edges S h d k) (m : Memory w) : Loaded base order (mount base order m) := by
  intro t j
  let n:=((Fintype.equivFin _) t).val
  have hi : n<Fintype.card (Channel S.degree (Stages h d) k) := ((Fintype.equivFin _) t).isLt
  have lo : j.val<stride h d := j.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)
  have pos := Nat.zero_lt_of_lt lo
  have block := Nat.mul_le_mul_right (stride h d) hi
  rw [Nat.succ_mul] at block
  have inside : base≤base+n*stride h d+j.val ∧ base+n*stride h d+j.val<base+words S h d k := by unfold words;omega
  have div : (n*stride h d+j.val)/stride h d=n := by
    rw [Nat.mul_comm n,Nat.mul_add_div pos,Nat.div_eq_of_lt lo,Nat.add_zero]
  have mod : (n*stride h d+j.val)%stride h d=j.val := Nat.mul_add_mod_of_lt lo
  change mount base order m (base+n*stride h d+j.val)=_
  rw [mount,fillSegment,ite_eq_left inside]
  simp only [Nat.add_assoc,Nat.add_sub_cancel_left,div,mod,dite_eq_left hi]
  simp [n]

theorem Loaded.read {base : ℕ} {order : Fin R≃Edges S h d k} {m : Memory w}
    (H : Loaded base order m) (kind : Channel S.degree (Stages h d) k) (key : Expr) (r : Word w)
    (j : Fin (positions h d)) (matchKey : (key.eval m r).val=j.val) (e : Edges S h d k)
    (trueEdge : resolve S h d k kind j.val=some e) :
    (field (S:=S) (h:=h) (d:=d) base kind key).eval m r=((order.symm e).val:Word w) := by
  have small : j.val<(bank (S:=S) (h:=h) (d:=d) base kind).size := j.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)
  change m ((bank (S:=S) (h:=h) (d:=d) base kind).base+(key.eval m r).val%(bank (S:=S) (h:=h) (d:=d) base kind).size)=_
  rw [matchKey,Nat.mod_eq_of_lt small,H,cell,trueEdge]
  rfl

theorem cell_inside (base : ℕ) (kind : Channel S.degree (Stages h d) k) (j : Fin (positions h d)) :
    base≤(bank (S:=S) (h:=h) (d:=d) base kind).base+j.val ∧
      (bank (S:=S) (h:=h) (d:=d) base kind).base+j.val<base+words S h d k := by
  have order := Nat.mul_le_mul_right (stride h d) ((Fintype.equivFin _) kind).isLt
  rw [Nat.succ_mul] at order
  have fit : j.val<stride h d := j.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)
  dsimp only [bank,words];omega

theorem Loaded.frame {base : ℕ} {order : Fin R≃Edges S h d k} {m m' : Memory w}
    (loaded : Loaded base order m) (stable : ∀ x,base≤x→x<base+words S h d k→m' x=m x) :
    Loaded base order m' := fun kind j=>
  (stable _ (cell_inside base kind j).1 (cell_inside base kind j).2).trans (loaded kind j)

theorem mount_outside (base : ℕ) (order : Fin R≃Edges S h d k) (m : Memory w) (x : ℕ)
    (away : x<base ∨ base+words S h d k≤x) : mount base order m x=m x := by
  simp [mount,fillSegment,show ¬(base≤x∧x<base+words S h d k) by omega]

theorem field_work (base : ℕ) (kind : Channel S.degree (Stages h d) k) (key : Expr) :
    (field (S:=S) (h:=h) (d:=d) base kind key).work=key.work+5 := rfl

end Hierarchy.ProtocolRAM.Calendar.CoreLookup
end

end OAI
