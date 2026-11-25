import OAI.Hierarchy.DescentUniqueAperture
import OAI.Hierarchy.DescentApertureExpressions
import OAI.Hierarchy.DescentPackedPorts
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace OAI
/-! # Sorting and deduplicating the aperture received from the preceding physical stage -/
namespace Hierarchy.DescentSortedRoster
open DescentFallbackLeafScan DescentFallbackRankRAM DescentPackedColony
open ThreeFlat.RAM DescriptorExpr Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D H w : ℕ} (peer : Fin H→Fin D→Option (Fin H))
def present (v : Fin H) := Finset.univ.filter (fun z=>∃i,peer v i=some z)
def before (v z : Fin H) := ((present peer v).filter (·<z)).card
def indexed (v : Fin H) (i : Fin D) : Option (Fin H) :=
  if exists_ : ∃z∈present peer v,before peer v z=i.val then some exists_.choose else none

theorem before_strict {v a b : Fin H} (ha : a∈present peer v) (lt : a<b) :
    before peer v a<before peer v b := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (show ((present peer v).filter (·<a))⊆((present peer v).filter (·<b)) from
    fun x hx=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,((Finset.mem_filter.mp hx).2).trans lt⟩)).mpr
  exact ⟨a,Finset.mem_filter.mpr ⟨ha,lt⟩,by simp⟩

theorem indexed_iff (v : Fin H) (i : Fin D) (z : Fin H) :
    indexed peer v i=some z ↔ z∈present peer v ∧ before peer v z=i.val := by
  unfold indexed
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl;exact h.choose_spec
    · rintro ⟨member,score⟩
      rcases lt_trichotomy h.choose z with lt|eq|gt
      · exact False.elim ((before_strict peer h.choose_spec.1 lt).ne (h.choose_spec.2.trans score.symm))
      · exact eq
      · exact False.elim ((before_strict peer member gt).ne (score.trans h.choose_spec.2.symm))
  · rename_i no
    exact iff_of_false (by simp) (fun h=>no ⟨z,h⟩)

def keep (v z : Fin H) (j : Fin D) := (first peer v j).any (·<z)

theorem order_count (v z : Fin H) :
    (Finset.univ.filter (fun i=>keep peer v z i=true)).card=before peer v z := by
  let get j (h : keep peer v z j=true) := (first peer v j).get (by cases hx:first peer v j <;> simp_all [keep])
  have hit j (h : keep peer v z j=true) : first peer v j=some (get j h):=(Option.some_get _).symm
  apply Finset.card_bij (fun j h=>get j (Finset.mem_filter.mp h).2)
  · intro j h
    have yes:=(Finset.mem_filter.mp h).2
    let a:=get j yes
    have real:=first_real peer (hit j yes)
    have less : a<z := by
      have isKept : (first peer v j).any (fun x=>decide (x<z))=true := yes
      rw [hit j yes] at isKept
      exact of_decide_eq_true isKept
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,real⟩,less⟩
  · intro a ha b hb eqn
    exact first_unique peer ((hit a (Finset.mem_filter.mp ha).2).trans (congrArg some eqn))
      (hit b (Finset.mem_filter.mp hb).2)
  · intro b hb
    obtain ⟨seen,lt⟩:=Finset.mem_filter.mp hb
    obtain ⟨j,hj⟩:=first_one peer v b (Finset.mem_filter.mp seen).2
    have ok : keep peer v z j=true:=by simp [keep,hj,lt]
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ok⟩,Option.some.inj ((hit j ok).symm.trans hj)⟩

def rankBit (src : Fin D→Expr) (query : Expr) (j : Fin D) : Expr :=
  unlessSeen (src j) (.branch .lt (src j) query (.lit 1) (.lit 0)) ((prior j).map src)
def calculate (src : Fin D→Expr) (query : Expr) := foldSum ((Finset.univ : Finset (Fin D)).toList.map (rankBit src query))
def pick (src : Fin D→Expr) (slot : Expr) (sentinel : ℕ) : List (Fin D)→Expr
  | []=>.lit sentinel
  | i::rest=>.branch .eq
      (.branch .lt (src i) (.lit sentinel) (.branch .eq (calculate src (src i)) slot (.lit 1) (.lit 0)) (.lit 0))
      (.lit 1) (src i) (pick src slot sentinel rest)

variable (m : Memory w) (r : Word w) (src : Fin D→Expr) (v : Fin H)
variable (high : H<2^w) (wide : D<2^w) (reads : ∀j,(src j).eval m r=(target (peer v j):Word w))

include high reads in
private theorem decoded (j : Fin D) : ((src j).eval m r).val=target (peer v j) := by
  have bound : target (peer v j)<2^w := by cases e:peer v j with
    | none=>exact high
    | some t=>exact t.isLt.trans high
  rw [reads,Fin.val_cast_of_lt bound]

private theorem same {a b : Option (Fin H)} : target a=target b ↔ a=b := by
  cases a with
  | none=>cases b with
    | none=>simp
    | some j=>exact iff_of_false (fun h=>j.isLt.ne' h) (by simp)
  | some i=>cases b with
    | none=>exact iff_of_false (fun h=>i.isLt.ne h) (by simp)
    | some j=>exact ⟨fun h=>congrArg some (Fin.ext h),fun h=>congrArg target h⟩

include high reads in
theorem rankBit_read (query : Expr) (z : Fin H) (atZ : (query.eval m r).val=z.val) (j : Fin D) :
    (rankBit src query j).eval m r=((keep peer v z j).toNat:Word w) := by
  have duplicate : (∃a∈(prior j).map src,a.eval m r=(src j).eval m r) ↔ ∃i : Fin D,i<j ∧ peer v i=peer v j := by
    simp only [List.mem_map,exists_exists_and_eq_and,prior,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and]
    apply exists_congr
    intro i
    rw [Fin.ext_iff,decoded peer m r src v high reads,decoded peer m r src v high reads,same]
  simp only [rankBit,unlessSeen_eval,duplicate,keep,first]
  split
  · rfl
  · simp only [Expr.eval,Comparison.test,decide_eq_true_eq,Nat.cast_one,Nat.cast_zero]
    have agree : (src j).eval m r<query.eval m r ↔ target (peer v j)<z.val:=by
      change ((src j).eval m r).val<(query.eval m r).val ↔ _
      rw [atZ,decoded peer m r src v high reads]
    simp only [agree]
    cases e:peer v j with
    | none=>
      change (if H<z.val then (1:Word w) else 0)=0
      exact ite_eq_right (Nat.not_lt.mpr z.isLt.le)
    | some a=>
      change (if a.val<z.val then (1:Word w) else 0)=((decide (a<z)).toNat:Word w)
      by_cases earlier : a.val<z.val
      · have yes : a<z:=earlier
        simp only [ite_eq_left earlier,decide_eq_true yes,Bool.toNat_true,Nat.cast_one]
      · have no : ¬a<z:=earlier
        simp only [ite_eq_right earlier,decide_eq_false no,Bool.toNat_false,Nat.cast_zero]

include high reads in
theorem rank_read (query : Expr) (z : Fin H) (atZ : (query.eval m r).val=z.val) :
    (calculate src query).eval m r=(before peer v z:Word w) := by
  rw [calculate,foldSum_eval,List.map_map]
  simp only [Function.comp_def,rankBit_read peer m r src v high reads query z atZ]
  rw [←order_count]
  rw [Finset.sum_map_toList]
  simp [Bool.toNat,Finset.sum_boole]

include high wide reads in
theorem pick_read (slot : Expr) (s : Fin D) (slotAt : (slot.eval m r).val=s.val) :
    (pick src slot H (List.finRange D)).eval m r=(target (indexed peer v s):Word w) := by
  have nz : (0:Word w)≠1 := by
    have fit : 1<2^w := (Nat.succ_le_of_lt (Nat.zero_lt_of_lt v.isLt)).trans_lt high
    intro eqn
    have vals:=congrArg Fin.val eqn
    change 0=1%(2^w) at vals
    rw [Nat.mod_eq_of_lt fit] at vals
    contradiction
  let valid (j : Fin D):=∃t,peer v j=some t ∧ before peer v t=s.val
  have nr (j) (z : Fin H) (eqn : peer v j=some z) : (src j).eval m r=(z.val:Word w) := by
    rw [reads,eqn]; rfl
  have readPick (xs : List (Fin D)) :
      (pick src slot H xs).eval m r=
        (xs.find? (fun j=>decide (valid j))).elim (H:Word w) (fun j=>(src j).eval m r) := by
    induction xs with
    | nil=>rfl
    | cons j js ih=>
      cases eqn : peer v j with
      | none=>
        simp [pick,Expr.eval,Comparison.test,reads,eqn,target,valid,ih,nz]
      | some t=>
        have raw:=(decoded peer m r src v high reads j)
        rw [eqn] at raw
        have less : (src j).eval m r<(H:Word w) := by rw [Fin.lt_def,raw,Fin.val_cast_of_lt high];exact t.isLt
        have rankEq:=rank_read peer m r src v high reads (src j) t raw
        have room : before peer v t<2^w := ((order_count peer v t).symm.le.trans (by
          simpa using Finset.card_filter_le (s:=Finset.univ) (fun i=>keep peer v t i=true))).trans_lt wide
        have yes : (calculate src (src j)).eval m r=slot.eval m r ↔ before peer v t=s.val := by
          rw [Fin.ext_iff,rankEq,Fin.val_cast_of_lt room,slotAt]
        by_cases score : before peer v t=s.val <;> simp [pick,Expr.eval,Comparison.test,less,yes,valid,eqn,score,ih,nz]
  rw [readPick]
  cases addr:(List.finRange D).find? (fun j=>decide (valid j)) with
  | some j=>
    have chosen : decide (valid j)=true := List.find?_some (p:=fun i=>decide (valid i)) addr
    have isValid : valid j := of_decide_eq_true chosen
    obtain ⟨z,pz,pref⟩:=isValid
    have found : indexed peer v s=some z := (indexed_iff peer v s z).2
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,pz⟩,pref⟩
    simp [found,target,nr j z pz]
  | none=>
    have empty : indexed peer v s=none := by
      cases ans:indexed peer v s with
      | none=>rfl
      | some z=>
        obtain ⟨yes,pref⟩:=(indexed_iff peer v s z).1 ans
        obtain ⟨j,atj⟩:=(Finset.mem_filter.mp yes).2
        have impossible:=(List.find?_eq_none.mp addr) j (List.mem_finRange j)
        simp [valid,atj,pref] at impossible
    simp [empty,target]

end
end Hierarchy.DescentSortedRoster

end OAI
