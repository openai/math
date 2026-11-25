import OAI.Computability.IntegerMultiplication.Brief.Signed

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Brief
open Code Carry Bits Grid Staff Strip

abbrev Ticket:= S × Word -- assume pos denom; all operations can preserve
def live (x:Ticket) : Prop := 0 < value x.2
noncomputable def view (x:Ticket) : ℝ := (whole x.1:ℝ)/(value x.2:ℝ)
def fuse (x:Ticket×Ticket):Ticket :=
  (plus (times (x.1.1, register x.2.2),times (x.2.1,register x.1.2)),
    times0 (x.1.2,x.2.2))
@[fun_prop] theorem fuseP : Poly fuse := by unfold fuse; have v:=easy_plus.poly; fun_prop
theorem fuse_v (x y) (a:live x) (b:live y):
    view (fuse (x,y))=view x+view y ∧ live (fuse (x,y)) := by
  unfold view fuse live
  constructor
  · rw [Grid.plus_v,timeV,timeV,tm_value,regV,regV]
    push_cast
    have h : (value x.2:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast a)
    have t : (value y.2:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast b)
    field
  rw [tm_value]; exact Nat.mul_pos a b

def sumTicket (x:List Ticket) :=
  x.foldl (fun s y => fuse (s,y)) ((false,([]:Word)),[true])
theorem sumTicket_v (x) (h : ∀ y∈x,live y) :
    view (sumTicket x)=(x.map view).sum ∧ live (sumTicket x) := by
  have e (x:List Ticket) (s:Ticket) (p:live s) (h:∀ y∈x,live y) :
      let T := x.foldl (fun s y=> fuse (s,y)) s
      view T=view s+(x.map view).sum ∧ live T := by
    induction x generalizing s with
    | nil=> exact ⟨by simp,p⟩
    | cons a x ih=>
      have v:= fuse_v _ _ p (h a (by simp))
      obtain ⟨i,g⟩ := ih (fuse (s,a)) v.2 (fun y e=>h y (by simp [e]))
      exact ⟨by dsimp only [List.foldl_cons]; rw [i,v.1,List.map_cons,List.sum_cons]; ring,g⟩
  obtain ⟨t,g⟩:=e x ((false,[]),[true]) (by simp [live]) h
  exact ⟨by simpa [sumTicket,view,whole] using t,g⟩

abbrev cap (x:Ticket):=size x.2
private theorem fuseS (i j:Ticket) :
    cap (fuse (i,j)) ≤ cap i+size j ∧
    size (fuse (i,j)) ≤ size i+cap i+4*size j+4 := by
  unfold cap fuse
  dsimp only
  rw [size_prod,size_word,tm_length]
  have A := timeS i.1 (register j.2)
  have B := timeS j.1 (register i.2)
  have p := plusS (times (i.1,register j.2)) (times (j.1,register i.2))
  have r (w:Word): size (register w)=size w+2 := by unfold register; rw [size_prod]; rw [show size (false:Bool)=1 from rfl]; dsimp only; omega
  rw [r] at A B
  rw [size_prod (x:=i)] -- j already
  rw [size_prod (x:= (Grid.plus (times (i.1,register j.2),times (j.1, register i.2)), times0 (i.2,j.2))),size_word (times0 (i.2,j.2)),tm_length]
  simp only [size_word] at *
  omega

private theorem costTicket (x:List Ticket×Ticket) (y:List Ticket)
    (d:y <+: x.1) :
    size (y.foldl (fun s y=> fuse (s,y)) x.2) ≤ 16*(size x+1)^2 := by
  let W:=size x
  have u {i} (a:i∈x.1) :
      size i ≤ W := (Code.size_bel a).le.trans (by unfold W; simp; omega)
  have l : y.length≤W := le_trans (List.IsPrefix.length_le d) (le_trans (duration _).le (by unfold W; simp; omega))
  have G (z: List Ticket) (s:Ticket) :
      let t:=z.foldl (fun s y=>fuse (s,y)) s
      size t ≤ size s+(cap s+6*costSum size z+4)*z.length := by
    induction z generalizing s with
    | nil=> simp
    | cons a z ih=>
      dsimp only [List.foldl_cons]; rw [costSum_cons,List.length_cons]
      specialize ih (fuse (s,a))
      dsimp only at ih
      obtain ⟨v,w⟩:=fuseS s a
      apply ih.trans
      rw [Nat.mul_add,Nat.mul_one]
      have h := Nat.mul_le_mul_right z.length
        (by omega : cap (fuse (s,a))+6*costSum size z+4≤cap s +6*(size a+costSum size z)+4)
      omega
  have b : costSum size y ≤ W := by
    obtain ⟨l,h⟩:=d
    have u := Code.costSum_le_length_size x.1
    change y++l=x.1 at h
    rw [← h,costSum_cat,List.length_append,h] at u
    unfold W; rw [size_prod]; omega
  have b1 : size x.2 ≤ W := by unfold W; rw [size_prod (x:=x)]; omega
  have b2 : cap x.2 ≤ W := le_trans (by rw [size_prod (x:=x.2)]; unfold cap; omega : cap x.2≤ size x.2) b1
  have E := G y x.2
  have P := Nat.mul_le_mul (by omega: cap x.2+6*costSum size y+4≤ W+6*W+4) l
  change _≤ 16*(W+1)^2
  nlinarith

@[fun_prop] theorem sumTicketP : Poly sumTicket := by
  unfold sumTicket
  exact ((Poly.pair (Code.Poly.identity (X:=List Ticket)) (Code.Poly.const (((false,([]:Word)),([true]:Word)):Ticket))).compose (Poly.fold_left fuseP 16 2 costTicket))
/-  Poly.compose (Poly.pair Code.Poly.identity (Code.Poly.const (((false,([]:Word)),([true]:Word)):Ticket)))
    (Poly.fold_left (by unfold fuse; have v:=easy_plus.poly; fun_prop) 16 2 costTicket) -/
end Brief

end IntegerMultiplication
end Computability
end OAI
