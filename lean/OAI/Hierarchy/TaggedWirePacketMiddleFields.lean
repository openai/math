import OAI.Hierarchy.TaggedWirePacketMiddleColumns
import OAI.Hierarchy.TaggedWirePacketBanks
import OAI.Hierarchy.TaggedWirePacketFieldCost

namespace OAI
/-! # Native widths, marks and offsets for the intermediate signed roles -/

noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns.Operands
open ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical
variable {n W out B : ℕ} {len : Fin n→ℕ} (o : Operands len)

def sameChord (i j : Fin n) (yes no : Expr) : Expr :=
  .branch .eq (o.oldSite i false) (o.oldSite j false)
    (.branch .eq (o.oldSite i true) (o.oldSite j true) yes no) no

def atParty (party : Expr) (i : Fin n) (b : Bool) (yes no : Expr) : Expr :=
  .branch .eq (o.oldSite i b) party yes no

/-- Compare both endpoint words instead of representing a pair by a larger native integer. -/
def middleSum (o : Operands len) (i : Fin n) : ℕ→Expr
  | 0=>.lit 0
  | t+1=>PacketScan.add (middleSum o i t) (if h:t<n then o.sameChord i ⟨t,h⟩ (o.width ⟨t,h⟩) (.lit 0) else .lit 0)

def middleColsAt (party : Expr) : MiddleField n→Expr
  | .inl (i,f)=>match f.val with
    | 0=>o.width i
    | 1=>o.atParty party i false (.lit 1) (.lit 0)
    | 2=>o.atParty party i true (.lit 1) (.lit 0)
    | 3=>o.middleSum i i.val
    | 4=>o.atParty party i false (o.middleSum i n) (.lit 0)
    | _=>o.atParty party i true (o.middleSum i n) (.lit 0)
  | .inr ((i,b),(j,c))=>
    o.atParty party i b (o.atParty party j c (o.sameChord i j (o.width i) (.lit 0)) (.lit 0)) (.lit 0)

def widenMiddle (M : ℕ) (fields : MiddleField n→Expr) : MiddleField M→Expr
  | .inl (i,f)=>if hi:i.val<n then fields (.inl (⟨i.val,hi⟩,f)) else .lit 0
  | .inr ((i,b),(j,c))=>if hi:i.val<n then if hj:j.val<n then
      fields (.inr ((⟨i.val,hi⟩,b),(⟨j.val,hj⟩,c))) else .lit 0 else .lit 0

def middleFields (M : ℕ) (party : Expr) : Fin (middleColumns M)→Expr :=
  widenMiddle M (o.middleColsAt party) ∘ (middleNumber M).symm

def middleValueRate (n B : ℕ) := 1+n*(5*B+5)+9*B+12

private theorem sum_fits (res : o.Resident W out) (i : Fin n) (t : ℕ) : (o.middleSum i t).Fits W out := by
  induction t with
  | zero=>trivial
  | succ t ih=>
    rw [middleSum]
    apply And.intro ih
    by_cases ht:t<n
    · simp only [dite_eq_left ht]
      exact ⟨res.old _ _,res.old _ _,⟨res.old _ _,res.old _ _,res.width _,trivial⟩,trivial⟩
    · simp only [dite_eq_right ht];trivial

private theorem sum_work (ok : o.Bound B) (i : Fin n) (t : ℕ) :
    (o.middleSum i t).work≤1+t*(5*B+5) := by
  induction t with
  | zero=>simp [middleSum,Expr.work]
  | succ t ih=>
    simp only [middleSum,PacketScan.add,Expr.work]
    rw [Nat.succ_mul t (5*B+5)]
    by_cases ht:t<n
    · simp only [dite_eq_left ht,sameChord,Expr.work]
      have h1:=ok.old i false;have h2:=ok.old i true
      have h3:=ok.old ⟨t,ht⟩ false;have h4:=ok.old ⟨t,ht⟩ true
      have h5:=ok.width ⟨t,ht⟩
      omega
    · simp only [dite_eq_right ht,Expr.work];omega

theorem middleColsAt_fits (res : o.Resident W out) (party : Expr) (here : party.Fits W out) :
    ∀f,(o.middleColsAt party f).Fits W out := by
  rintro (⟨i,f⟩|⟨⟨i,b⟩,⟨j,c⟩⟩)
  · fin_cases f <;> first | exact res.width i | exact o.sum_fits res i _ |
      exact ⟨res.old _ _,here,trivial,trivial⟩ | exact ⟨res.old _ _,here,o.sum_fits res _ _,trivial⟩
  · exact ⟨res.old _ _,here,⟨res.old _ _,here,⟨res.old _ _,res.old _ _,
      ⟨res.old _ _,res.old _ _,res.width _,trivial⟩,trivial⟩,trivial⟩,trivial⟩

theorem middleColsAt_work (ok : o.Bound B) (party : Expr) (here : party.work≤B) :
    ∀f,(o.middleColsAt party f).work≤ middleValueRate n B := by
  rintro (⟨i,f⟩|⟨⟨i,b⟩,⟨j,c⟩⟩)
  · have lo:=ok.old i false; have hi:=ok.old i true; have qty:=ok.width i
    have earlier:=(o.sum_work ok i i.val).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt.le) 1)
    have full:=o.sum_work ok i n
    fin_cases f
    · change (o.width i).work≤_
      unfold middleValueRate
      omega
    · change (o.oldSite i false).work+party.work+1+1+1≤_
      unfold middleValueRate
      omega
    · change (o.oldSite i true).work+party.work+1+1+1≤_
      unfold middleValueRate
      omega
    · change (o.middleSum i i.val).work≤_
      unfold middleValueRate
      omega
    · change (o.oldSite i false).work+party.work+(o.middleSum i n).work+1+1≤_
      unfold middleValueRate
      omega
    · change (o.oldSite i true).work+party.work+(o.middleSum i n).work+1+1≤_
      unfold middleValueRate
      omega
  · have hi:=ok.old i b; have hj:=ok.old j c
    have il:=ok.old i false;have ih:=ok.old i true
    have jl:=ok.old j false;have jh:=ok.old j true;have qty:=ok.width i
    dsimp only [middleColsAt,atParty,sameChord,Expr.work,middleValueRate]
    omega

theorem middleFields_fits (res : o.Resident W out) (M : ℕ) (party : Expr) (here : party.Fits W out)
    (f : Fin (middleColumns M)) : (o.middleFields M party f).Fits W out := by
  rcases e:(middleNumber M).symm f with ⟨i,g⟩|⟨⟨i,b⟩,⟨j,c⟩⟩ <;>
    simp only [middleFields,Function.comp_apply,e,widenMiddle] <;>split_ifs <;>
    first | exact o.middleColsAt_fits res party here _ | trivial

theorem middleFields_work (ok : o.Bound B) (M : ℕ) (room : n≤M) (party : Expr) (here : party.work≤B)
    (f : Fin (middleColumns M)) : (o.middleFields M party f).work≤ middleValueRate M B := by
  have leRate : middleValueRate n B≤ middleValueRate M B := by
    unfold middleValueRate
    have h:=Nat.mul_le_mul_right (5*B+5) room
    omega
  rcases e:(middleNumber M).symm f with ⟨i,g⟩|⟨⟨i,b⟩,⟨j,c⟩⟩ <;>
    simp only [middleFields,Function.comp_apply,e,widenMiddle] <;>split_ifs <;>
    first | exact (o.middleColsAt_work ok party here _).trans leRate | simp [Expr.work,middleValueRate]

end Hierarchy.WireTelescope.PacketTurns.Operands
end

end OAI
