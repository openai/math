import OAI.Hierarchy.DescentSortedRoster

namespace OAI
/-! # Space and instruction costs for sorting a bounded roster of computed neighbor reads -/
namespace Hierarchy.DescentSortedRoster
open DescentFallbackRankRAM ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical
noncomputable section

variable {n w out : ℕ} (src : Fin n→Expr)

theorem pick_lit_fits (fits : ∀j,(src j).Fits w out) (s H : ℕ) :
    (pick src (.lit s) H (List.finRange n)).Fits w out := by
  have guard (j) (e : Expr) (ef : e.Fits w out) (xs : List (Fin n)) :
      (unlessSeen (src j) e (xs.map src)).Fits w out := by
    induction xs with
    | nil=>exact ef
    | cons a as ih=>exact ⟨fits a,fits j,trivial,ih⟩
  have bit (i j : Fin n) : (rankBit src (src i) j).Fits w out :=
    guard j (.branch .lt (src j) (src i) (.lit 1) (.lit 0)) ⟨fits j,fits i,trivial,trivial⟩ _
  have total (i : Fin n) (xs : List (Fin n)) :
      (foldSum (xs.map (rankBit src (src i)))).Fits w out := by
    induction xs with
    | nil=>trivial
    | cons j js ih=>exact ⟨bit i j,ih⟩
  have build (xs : List (Fin n)) : (pick src (.lit s) H xs).Fits w out := by
    induction xs with
    | nil=>trivial
    | cons i is ih=>exact ⟨⟨fits i,trivial,⟨total i _,trivial,trivial,trivial⟩,trivial⟩,trivial,fits i,ih⟩
  exact build _

theorem pick_lit_work (b : ℕ) (small : ∀i,(src i).work≤b) (s H : ℕ) :
    (pick src (.lit s) H (List.finRange n)).work ≤ 20*(b+1)*(n+1)^3 := by
  have guard (j) (e : Expr) (xs : List (Fin n)) :
      (unlessSeen (src j) e (xs.map src)).work ≤ e.work+xs.length*(2*b+2) := by
    induction xs with
    | nil=>simp [unlessSeen]
    | cons i is ih=>
      change (src i).work+(src j).work+1+(unlessSeen (src j) e (is.map src)).work+1≤_
      rw [List.length_cons,Nat.succ_mul]
      have:=small i;have:=small j;omega
  let q:=2*b+3+n*(2*b+2)
  have bit (i j : Fin n) : (rankBit src (src i) j).work≤q := by
    have h:=guard j (.branch .lt (src j) (src i) (.lit 1) (.lit 0)) (prior j)
    have len : (prior j).length≤n := by
      simpa [prior,Finset.length_toList] using (Finset.card_filter_le (s:=Finset.univ) (fun x : Fin n=>x<j))
    have lim:=Nat.mul_le_mul_right (2*b+2) len
    change (rankBit src (src i) j).work≤(src j).work+(src i).work+1+1+1+_ at h
    dsimp only [q];have:=small i;have:=small j;omega
  have total (i : Fin n) (xs : List (Fin n)) :
      (foldSum (xs.map (rankBit src (src i)))).work≤1+xs.length*(q+1) := by
    induction xs with
    | nil=>simp [foldSum,Expr.work]
    | cons j js ih=>
      change (rankBit src (src i) j).work+(foldSum (js.map (rankBit src (src i)))).work+1≤_
      rw [List.length_cons,Nat.succ_mul]
      have:=bit i j;omega
  have calcBound (i : Fin n) : (calculate src (src i)).work≤1+n*(q+1) := by
    simpa only [calculate,Finset.length_toList,Finset.card_univ,Fintype.card_fin] using
      total i (Finset.univ : Finset (Fin n)).toList
  have walk (xs : List (Fin n)) :
      (pick src (.lit s) H xs).work ≤ 1+xs.length*(2*b+15+n*(q+1)) := by
    induction xs with
    | nil=>simp [pick,Expr.work]
    | cons i is ih=>
      have:=calcBound i;have:=small i
      change ((src i).work+1+((calculate src (src i)).work+1+1+1+1)+1+1)+1+(src i).work+
        (pick src (.lit s) H is).work+1≤_
      rw [List.length_cons,Nat.succ_mul];omega
  apply (walk _).trans
  rw [List.length_finRange]
  dsimp only [q]
  ring_nf
  omega

end
end Hierarchy.DescentSortedRoster

end OAI
