import OAI.Hierarchy.DescentScanMinimum
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Recording the first minimizing candidate in the actual public scan order -/

namespace Hierarchy.DescentFirstMinimumRAM
open DescentColonies ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
attribute [local irreducible] Procedure.Exec

/-- A single earlier result contains the ordinal of the winning candidate of the tail.
The tie-breaking branch keeps this row when the previous score equals its score. -/
def row (b : Bank) (out key : ℕ) : List ℕ→Expr
  | []=>.lit key
  | _j::js=>
    let previous := Expr.lookup ⟨out+js.length,0⟩ (.lit 0)
    .branch .lt (.lookup b previous) (.lookup b (.lit key)) previous (.lit key)

def code (w out : ℕ) (b : Bank) : List ℕ→Procedure w
  | []=>scan w out 0 (.lit 0)
  | i::is=>(code w out b is).seq (scan w (out+is.length) 1 (row b out i is))

def after {w : ℕ} (out : ℕ) (b : Bank) (m : Memory w) : List ℕ→Memory w
  | []=>m
  | i::is=>image (out+is.length) 1 (row b out i is) (after out b m is)

def ticks (out : ℕ) (b : Bank) : List ℕ→ℕ
  | []=>4
  | i::is=>ticks out b is+(4+1*(2*(row b out i is).work+4))

theorem frame {w : ℕ} (out : ℕ) (b : Bank) (m : Memory w) (xs : List ℕ) (a : ℕ) (lo : a<out) :
    after out b m xs a=m a := by
  induction xs with
  | nil=>rfl
  | cons i is ih=>simpa [after,image,fillSegment,show ¬out+is.length≤a by omega] using ih

private theorem rowFits {w out i : ℕ} {b : Bank} (fits : b.Fits w out) (width : 1<2^w)
    (is : List ℕ) : (row b out i is).Fits w (out+is.length) := by
  cases is with
  | nil=>trivial
  | cons j js=>
    have older : (Bank.mk (out+js.length) 0).Fits w (out+(j::js).length) :=
      ⟨by simp [Bank.size],width,by simp [Bank.size,Nat.add_assoc]⟩
    have source : b.Fits w (out+(j::js).length) := ⟨fits.1,fits.2.1,fits.2.2.trans (Nat.le_add_right ..)⟩
    exact ⟨⟨source,older,trivial⟩,⟨source,trivial⟩,⟨older,trivial⟩,trivial⟩

theorem exec {w out : ℕ} (b : Bank) (m : Memory w) (xs : List ℕ) (fits : b.Fits w out)
    (room : out+xs.length<2^w) (width : 1<2^w) :
    (code w out b xs).Exec m (after out b m xs) (ticks out b xs) := by
  induction xs with
  | nil=>
    have im : ProtocolRAM.image out 0 (.lit 0) m=m := by funext a; simp [ProtocolRAM.image,fillSegment]
    change (scan w out 0 (.lit 0)).Exec m m 4
    have base : (scan w out 0 (.lit 0)).Exec m (ProtocolRAM.image out 0 (.lit 0) m) 4 :=
      @scan_exec w out 0 (.lit 0) m trivial (by simpa using room)
    rwa [im] at base
  | cons i is ih=>
    have tailRoom : out+is.length<2^w := by simp only [List.length_cons] at room;omega
    exact Procedure.Exec.then (ih tailRoom)
      (@scan_exec w (out+is.length) 1 (row b out i is) (after out b m is) (rowFits (i:=i) fits width _) (by simpa [Nat.add_assoc] using room))

theorem length_budget (out : ℕ) (b : Bank) (xs : List ℕ) : ticks out b xs≤4+70*xs.length := by
  induction xs with
  | nil=>simp [ticks]
  | cons i is ih=>cases is <;> simp [ticks,row,Expr.work] at *; omega

theorem winner_mem {S : Type*} (q : S→ℕ) (xs : List S) {s : S} {a : ℕ}
    (result : (scanMinimum q xs).1=some (s,a)) : s∈xs := by
  induction xs with
  | nil=>simp [scanMinimum] at result
  | cons x xs ih=>
    cases tail : (scanMinimum q xs).1 with
    | none=>simp [scanMinimum,tail] at result;simp [←result.1]
    | some p=>
      by_cases keep : q x≤p.2
      · simp [scanMinimum,tail,keep] at result
        simp [←result.1]
      · simp [scanMinimum,tail,keep] at result
        exact .tail _ (ih (result ▸ tail))

theorem winner {w out : ℕ} (b : Bank) (m : Memory w) (score : ℕ→ℕ) (xs : List ℕ)
    (fit : b.Fits w out) (keys : ∀i∈xs,i<b.size) (words : ∀i∈xs,m (b.base+i)=(score i:Word w))
    (caps : ∀i∈xs,score i<2^w) {i s : ℕ} (found : (scanMinimum score xs).1=some (i,s)) :
    after out b m xs (out+(xs.length-1))=(i:Word w) := by
  induction xs generalizing i s with
  | nil=>simp [scanMinimum] at found
  | cons h ts ih=>
    let mem := after out b m ts
    have stored (z : ℕ) (inList : z∈h::ts) : b.read mem (z:Word w)=(score z:Word w) := by
      have small := keys z inList
      rw [Bank.read,Fin.val_cast_of_lt (small.trans fit.2.1),Nat.mod_eq_of_lt small]
      exact (frame out b m ts _ (by have := fit.2.2;omega)).trans (words _ inList)
    have atOut : after out b m (h::ts) (out+((h::ts).length-1))=
        (row b out h ts).eval mem 0 := by simp [after,mem,image,fillSegment,Nat.cast_add]
    rw [atOut]
    cases ts with
    | nil=>simp [scanMinimum] at found; simp [row,Expr.eval,found.1]
    | cons j js=>
      have spec := (scanMinimum_spec score (j::js)).2
      cases previous : (scanMinimum score (j::js)).1 with
      | none=>simp [previous] at spec
      | some q=>
        rw [previous] at spec
        obtain ⟨correct,_⟩ := spec
        have member := winner_mem score (j::js) (s:=q.1) (a:=q.2) previous
        have source := ih (fun z hz=>keys z (by simp [hz])) (fun z hz=>words z (by simp [hz]))
          (fun z hz=>caps z (by simp [hz])) previous
        change mem (out+js.length)=_ at source
        have prev : (Expr.lookup ⟨out+js.length,0⟩ (.lit 0)).eval mem 0 = (q.1:Word w) := by
          simpa [Expr.eval,Bank.read,Bank.size] using source
        have hMem : h∈h::j::js := .head ..
        have qMem : q.1∈h::j::js := .tail _ member
        have cmp : (score q.1:Word w)<(score h:Word w) ↔ score q.1<score h := by
          rw [Fin.lt_def,Fin.val_cast_of_lt (caps _ qMem),Fin.val_cast_of_lt (caps _ hMem)]
        change (Bank.mk (out+js.length) 0).read mem 0=(q.1:Word w) at prev
        change (if decide (b.read mem ((Bank.mk (out+js.length) 0).read mem 0)<b.read mem (h:Word w)) then
          (Bank.mk (out+js.length) 0).read mem 0 else (h:Word w))=(i:Word w)
        rw [prev,stored _ qMem,stored _ hMem]
        simp only [decide_eq_true_eq,cmp]
        change some (match (scanMinimum score (j::js)).1 with
          | none=>(h,score h)
          | some p=>if score h≤p.2 then (h,score h) else p)=some (i,s) at found
        rw [previous] at found
        by_cases first : score h≤q.2
        · simp only [first,ite_true,Option.some.injEq,Prod.mk.injEq] at found
          simp [←found.1,show ¬score q.1<score h by omega]
        · simp only [first,ite_false,Option.some.injEq] at found
          have sameKey := congrArg Prod.fst found
          rw [ite_eq_left (show score q.1<score h by omega)]
          exact congrArg (fun x : ℕ=>(x:Word w)) sameKey

end
end Hierarchy.DescentFirstMinimumRAM

end OAI
