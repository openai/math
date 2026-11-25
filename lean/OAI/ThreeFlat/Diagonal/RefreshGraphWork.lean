import OAI.ThreeFlat.Diagonal.CompressorStageMachine

namespace OAI
/-! # Uniform compiled size of both orientations of the refresh graph -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Refresh

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM.DescriptorExpr Placement
open scoped Fin.NatCast

variable {W U k n m h : ℕ}

private theorem bin (op : BinaryOp) (x y : Term W k n) :
    (Term.binary op x y).binds=x.binds+y.binds+1 := by simp [Term.binary,Term.binds]; omega
private theorem select (op : Comparison) (x y z t : Term W k n) :
    (Term.select op x y z t).binds=x.binds+y.binds+z.binds+t.binds+1 := by simp [Term.select,Term.binds]; omega
private theorem load (x : Term W k n) : (Term.load x).binds=x.binds+1 := by simp [Term.load,Term.binds]
private theorem lit (x : Word W) : (Term.literal x : Term W k n).binds=1 := rfl

theorem findWord_work (x : Term W k n) (l : List (Word W × Word W)) :
    (findWord x l).binds=l.length*(x.binds+3)+1 := by
  induction l with
  | nil => simp only [findWord, lit, List.length_nil, Nat.zero_mul, Nat.zero_add]
  | cons z l ih =>
    simp only [findWord,select,lit,List.length_cons,ih,Nat.succ_mul]
    omega

theorem rom_length (E : SlotGraph (Fin m) h) (b : Bool) (p : Fin m × Fin h → ℕ) :
    (portROM (w:=W) E b p).length=m*h := by
  simp [portROM,List.length_flatMap,←List.ofFn_id,List.map_ofFn]

theorem row_work (E : SlotGraph (Fin m) h) (back : Bool) (pad : ℕ) (f : Field)
    (A : OldColumns (Term W k 1)) (B : OldColumns (Term U k 1)) (c : Term W k 1) (c' : Term U k 1)
    (h₀ : A.neighbor.binds=B.neighbor.binds) (h₁ : A.mate.binds=B.mate.binds)
    (h₂ : A.remainingShift.binds=B.remainingShift.binds) (hc : c.binds=c'.binds) :
    (row E back pad f A c).binds=(row E back pad f B c').binds := by
  cases f <;> simp only [row,terms,Placement.row,bin,select,load,lit,findWord_work,rom_length,
    Term.binds,h₀,h₁,h₂,hc]

theorem six_work (start len : Term W k 1) (start' len' : Term U k 1)
    (f : Fin 6 → Term W k 1 → Term W k 1) (g : Fin 6 → Term U k 1 → Term U k 1)
    (hs : start.binds=start'.binds) (hl : len.binds=len'.binds)
    (hf : ∀ i x y, x.binds=y.binds → (f i x).binds=(g i y).binds) :
    (sixColumns start len f).binds=(sixColumns start' len' g).binds := by
  let test (a b : Term W k 1) := Term.binary .div (.binary .sub (.result 0) a) b
  let test' (a b : Term U k 1) := Term.binary .div (.binary .sub (.result 0) a) b
  let pos (i : Fin 6) := Term.binary .add start (.binary .mul len (.literal (i.val:Word W)))
  let pos' (i : Fin 6) := Term.binary .add start' (.binary .mul len' (.literal (i.val:Word U)))
  have t : (test start len).binds=(test' start' len').binds := by simp only [test,test',bin,Term.binds,hs,hl]
  have p i : (pos i).binds=(pos' i).binds := by simp only [pos,pos',bin,lit,hs,hl]
  have fold (l : List (Fin 6)) :
      (l.foldr (fun i z => Term.select .eq (test start len) (.literal (i.val:Word W)) (f i (pos i)) z)
        (.literal 0)).binds =
      (l.foldr (fun i z => Term.select .eq (test' start' len') (.literal (i.val:Word U)) (g i (pos' i)) z)
        (.literal 0)).binds := by
    induction l with
    | nil => rfl
    | cons i l ih => simp only [List.foldr_cons,select,lit,t,hf i _ _ (p i),ih]
  exact fold _

theorem columns_work (E : SlotGraph (Fin m) h) (pad : ℕ)
    (A : Bool → OldColumns (Term W k 1)) (B : Bool → OldColumns (Term U k 1))
    (start len : Term W k 1) (start' len' : Term U k 1) (hs : start.binds=start'.binds)
    (hl : len.binds=len'.binds) (h₀ : ∀ b, (A b).neighbor.binds=(B b).neighbor.binds)
    (h₁ : ∀ b, (A b).mate.binds=(B b).mate.binds) (h₂ : ∀ b, (A b).remainingShift.binds=(B b).remainingShift.binds) :
    (refreshColumns E pad A start len).binds=(refreshColumns E pad B start' len').binds :=
  six_work _ _ _ _ _ _ hs hl (fun _i x y e => row_work E _ pad _ _ _ x y (h₀ _) (h₁ _) (h₂ _) e)


end ThreeFlat.Diagonal.CompressorPacking.Native.Refresh

end OAI
