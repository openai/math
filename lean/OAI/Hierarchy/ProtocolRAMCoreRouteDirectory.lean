import OAI.Hierarchy.ProtocolRAMCatalystLayoutTypes
import OAI.Hierarchy.ProtocolRAMCoreRouteOrder
import OAI.Hierarchy.ProtocolRAMCoreRouteHops
import OAI.Hierarchy.ProtocolRAMRouteDirectory

namespace OAI
/-! # Native settlement directory from the permutation and the original CT catalogue -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical
variable {z W k w R attempts edges K : ℕ} {S : PurchaseSampler}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "Slots₀" => Slots z D k
local notation "A" => Actions N k
local notation "r" => Fintype.card Slots₀

section
variable {h d l J E : ℕ} {π₀ : Equiv.Perm (Fin (2^h))} {g : Site h d l→Fin J} (B : Mount (S:=S) π₀ g E)
theorem tailKind (v : Slots h d l) : RouteSettlement.oddKind (toOccurrence B v)=siteKind v := by cases v <;> rfl

theorem tailResource (ci : Commodity (Fin (2^h)) (Stages h d) l→ℕ) (cj : Columns h d×Fin l→ℕ)
    (v : Slots h d l) : RouteSettlement.resource ci cj (toOccurrence B v)=siteResource ci cj v := by cases v <;> rfl

end

def operator (x : Source) (S : PurchaseSampler) (z W k attempts : ℕ) : Actions (Stages z (2^W)) k→Expr :=
  Sum.elim (x.payloadExpr S z W k attempts) (Sum.elim (x.tileExpr S z W k)
    (Sum.elim (fun a=>x.quoteExpr S z W k attempts a.1 a.2) (x.centerExpr S z W k)))

theorem physical_hop (π : Equiv.Perm (Fin (2^z))) (place : Site z D k→Fin K) (B : Mount (S:=S) π place edges)
    (order : Fin R≃Edges S z D k) (physical : ∀e,(B.row e).val=(order.symm e).val)
    {x : Source} {m : Memory w} (data : Readable x S z W k attempts order π m) (v : Slots₀) :
    (operator x S z W k attempts (action v).1).eval m ((action v).2:Word w)=
      ((toOccurrence B v).edge.val:Word w) := by
  cases v with
  | inl v =>
    rcases v with ⟨i,j⟩
    cases i with
    | inl p =>
      let e : Fin (2*N+1) := j
      change (x.payloadExpr S z W k attempts e).eval m (p.val:Word w)=_
      have hslot : e.val < ((payloadWalk (S:=S) (k:=k) π p).map B.row).length := by
        simpa only [List.length_map, payload_length] using e.isLt
      change _=((((payloadWalk π p).map B.row)[e.val]'hslot).val : Word w)
      rw [List.getElem_map, physical]
      by_cases even : e.val%2=0
      · let t : Fin (N+1) := ⟨e.val/2,by have:=e.isLt;omega⟩
        have eq : e.val=2*t.val := by dsimp [t];omega
        simpa only [eq,payload_even] using data.payload_joint p t e eq
      · let t : StageAt z D := ⟨e.val/2, by
          change e.val / 2 < Stages z D
          have bound : e.val < 2*Stages z D+1 := e.isLt
          omega⟩
        have eq : e.val=2*t.val+1 := by dsimp [t];omega
        simpa only [eq,payload_odd] using data.payload_tile p e t eq
    | inr q =>
      obtain ⟨⟨p,t⟩,l⟩ := q
      change Fin 2 at j
      fin_cases j
      · change (x.tileExpr S z W k t).eval m (p.val : Word w) = ((B.row (tileEdge p t none)).val : Word w)
        rw [physical]
        exact data.tile p t
      · let a := advisedStage z D π t
        change (x.quoteExpr S z W k attempts t l).eval m (p.val : Word w) =
          ((B.row (radiusEdge (outputCol t (a.group p) (a.output p)) l)).val : Word w)
        rw [physical]
        exact data.quote p t l
  | inr v =>
    rcases v with ⟨⟨c,l⟩,j⟩
    fin_cases j
    · change (x.centerExpr S z W k (l,false)).eval m (((Fintype.equivFin _) c).val : Word w) =
        ((B.row (radiusEdge c (l,false))).val : Word w)
      rw [physical]
      exact data.center c (l,false)
    · change (x.centerExpr S z W k (l,true)).eval m (((Fintype.equivFin _) c).val : Word w) =
        ((B.row (radiusEdge c (l,true))).val : Word w)
      rw [physical]
      exact data.center c (l,true)

def getSlot (o : Orders z D k) (i : Fin r) : Slots₀ := (slotOrder o).symm i

def Installed (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ) (m : Memory w) : Prop :=
  ∀i : Fin r,let v := getSlot o i
    p.kind.read m ((2*i.val:ℕ):Word w)=0 ∧ p.kind.read m ((2*i.val+1:ℕ):Word w)=(siteKind v:Word w) ∧
    p.mode.read m ((2*i.val:ℕ):Word w)=(((Fintype.equivFin A) (action v).1).val:Word w) ∧
    p.operand.read m ((2*i.val:ℕ):Word w)=((action v).2:Word w) ∧
    p.operand.read m ((2*i.val+1:ℕ):Word w)=(siteResource ci cj v:Word w)

def indexWord (p : Recipes) (x : Source) (S : PurchaseSampler) (z W k attempts : ℕ) : Expr :=
  let rows := Expr.lookup p.operand .row
  let ord := Fintype.equivFin (Actions (Stages z (2^W)) k)
  .branch .eq (.lookup p.kind .row) (.lit 0)
    (chooseField _ 0 (fun i=>(operator x S z W k attempts (ord.symm i)).atRow rows) (.lookup p.mode .row)) rows

def stages (b : RouteSettlement.Banks) (p : Recipes) (x : Source) (S : PurchaseSampler) (z W k attempts : ℕ) : List Pass :=
  let n := 2*Fintype.card (Slots z (2^W) k)
  [⟨b.kind.base,n,.lookup p.kind .row⟩,⟨b.index.base,n,indexWord p x S z W k attempts⟩]

/-- Re-evaluating one even recipe word recovers the original physical hop before any output scan. -/
theorem edge_word (p : Recipes) (x : Source) (π : Equiv.Perm (Fin (2^z)))
    (place : Site z D k→Fin K) (B : Mount (S:=S) π place edges) (order : Fin R≃Edges S z D k)
    (o : Orders z D k) (physical : ∀e,(B.row e).val=(order.symm e).val) (m : Memory w)
    (data : Readable x S z W k attempts order π m)
    (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ) (rom : Installed p o ci cj m)
    (menu : Fintype.card A≤2^w) (i : Fin r) :
    (indexWord p x S z W k attempts).eval m ((2*i.val:ℕ):Word w)=((toOccurrence B (getSlot o i)).edge.val:Word w) := by
  let v := getSlot o i
  have ready := rom i
  let code := (Fintype.equivFin A) (action v).1
  have id : ((Expr.lookup p.mode .row).eval m ((2*i.val:ℕ):Word w)).val=0+((Fintype.equivFin A) (action v).1).val := by
    change (p.mode.read m ((2*i.val:ℕ):Word w)).val=0+code.val
    rw [ready.2.2.1, Nat.zero_add]
    exact Fin.val_cast_of_lt (code.isLt.trans_le menu)
  simp only [indexWord,Expr.eval,ready.1,Comparison.test]
  rw [eval_chooseField _ _ _ _ _ _ _ (by simpa using menu) id,Equiv.symm_apply_apply,eval_atRow]
  change (operator x S z W k attempts (action v).1).eval m
    (p.operand.read m ((2*i.val:ℕ):Word w))=_
  rw [ready.2.2.2.1]
  exact physical_hop π place B order physical data v

theorem actual (p : Recipes) (x : Source) (b : RouteSettlement.Banks) (π : Equiv.Perm (Fin (2^z)))
    (place : Site z D k→Fin K) (B : Mount (S:=S) π place edges) (order : Fin R≃Edges S z D k)
    (o : Orders z D k) (physical : ∀e,(B.row e).val=(order.symm e).val) (m : Memory w) (data : Readable x S z W k attempts order π m)
    (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ) (rom : Installed p o ci cj m)
    (cap : 2*r≤2^w) (wider : 2<2^w) (menu : Fintype.card A≤2^w) (ks : 2*r≤b.kind.size) (indexCap : 2*r≤b.index.size)
    (apart : b.kind.base+2*r≤b.index.base) (prior : (indexWord p x S z W k attempts).Fits w b.kind.base) :
    RouteSettlement.Directory b (result (stages b p x S z W k attempts) m) (enum B o) ci cj := by
  let term := indexWord p x S z W k attempts
  let mid := image b.kind.base (2*r) (.lookup p.kind .row) m
  let out := image b.index.base (2*r) term mid
  have readKind (u : Fin (2*r)) : b.kind.read out (u.val:Word w)=p.kind.read m (u.val:Word w) := by
    change out (b.kind.base+(u.val:Word w).val%b.kind.size)=_
    rw [Fin.val_cast_of_lt (u.isLt.trans_le cap),Nat.mod_eq_of_lt (u.isLt.trans_le ks)]
    exact (ProtocolRAMGeneratedWrite.frame_image b.index.base (2*r) term mid (b.kind.base+u.val)
      (.inl ((Nat.add_lt_add_left u.isLt _).trans_le apart))).trans
      (ProtocolRAMGeneratedWrite.read_image b.kind.base (2*r) _ m u)
  have readIndex (u : Fin (2*r)) : b.index.read out (u.val:Word w)=term.eval m (u.val:Word w) := by
    change out (b.index.base+(u.val:Word w).val%b.index.size)=_
    rw [Fin.val_cast_of_lt (u.isLt.trans_le cap),Nat.mod_eq_of_lt (u.isLt.trans_le indexCap)]
    exact (ProtocolRAMGeneratedWrite.read_image _ _ term mid u).trans
      (eval_below term _ m mid prior (fun t ht=>
        ProtocolRAMGeneratedWrite.frame_image b.kind.base (2*r) (.lookup p.kind .row) m t (.inl ht)))
  have lo (i : Fin r) : 2*i.val<2*r := by have:=i.isLt;omega
  have hi (i : Fin r) : 2*i.val+1<2*r := by have:=i.isLt;omega
  constructor
  · intro i;exact (readKind ⟨_,lo i⟩).trans (rom i).1
  · intro i
    let v := getSlot o i
    apply (readIndex ⟨_,lo i⟩).trans
    exact edge_word p x π place B order o physical m data ci cj rom menu i
  · intro i;exact (readKind ⟨_,hi i⟩).trans ((rom i).2.1.trans (congrArg (fun n:ℕ=>(n:Word w)) (tailKind B _).symm))
  · intro i
    let v := getSlot o i
    apply (readIndex ⟨_,hi i⟩).trans
    have kinds (s : Slots₀) : 0 < siteKind s ∧ siteKind s ≤ 2 := by
      cases s with
      | inl _ => exact (by decide : 0 < (1 : ℕ) ∧ 1 ≤ 2)
      | inr _ => exact (by decide : 0 < (2 : ℕ) ∧ 2 ≤ 2)
    have nz : (siteKind (getSlot o i):Word w) ≠ 0 := by
      intro same
      have eq := congrArg Fin.val same
      change ((siteKind (getSlot o i) : Word w)).val=0 at eq
      rw [Fin.val_cast_of_lt ((kinds _).2.trans_lt wider)] at eq
      exact (Nat.ne_of_gt (kinds _).1) eq
    simp only [term,indexWord,Expr.eval,(rom i).2.1,Comparison.test,Nat.cast_zero,beq_iff_eq,ite_eq_right nz]
    exact (rom i).2.2.2.2.trans (congrArg (fun n:ℕ=>(n:Word w)) (tailResource B ci cj v).symm)

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
