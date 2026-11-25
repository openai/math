import OAI.Computability.IntegerMultiplication.Code.Slice

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open _root_.OAI.Computability.IntegerMultiplication.Code.Task

/-- number of slots to add until length multiple of n+1. -/
def alignment (n : ℕ) (l : Tally) :=
  l.foldr (fun _ s => if s=0 then n else s-1) 0
@[simp] theorem vacancy (n) : alignment n []=0 := rfl
@[simp] theorem next (n) (u : Unit) (t) : alignment n (u::t)=if alignment n t=0 then n else alignment n t-1 :=
  rfl
theorem aligned (n : ℕ) (l : Tally) :
    alignment n l ≤ n ∧ (n+1) ∣ l.length + alignment n l := by
  induction l with
  | nil => simp
  | cons u l ih =>
    simp only [next,List.length_cons]
    split
    next eq =>
      rw [eq, Nat.add_zero] at ih
      exact ⟨le_rfl,(show n+1 ∣ l.length+(n+1) from Nat.dvd_add ih.2 (dvd_refl _)) |> fun v =>
        (by rwa [Nat.add_assoc,Nat.add_comm 1])⟩
    next ne => exact ⟨(Nat.sub_le ..).trans ih.1,by rw [show l.length+1+(alignment n l-1)=l.length+alignment n l by omega]; exact ih.2⟩

def charge (n : ℕ) (l : Tally) :=
  if alignment n l=0 then n else 0

private theorem cup :
    Task (X:=Tally × Tally) (fun i => if i.1=[] then i.2.length else 0) send
      (fun i => if i.1=[] then send (i.2,i.2) else send (i.1.tail,i.2)) := by
  obtain ⟨c,C,h⟩ := Task.copy (send (X:=Tally))
  refine ⟨splitRoot 0 (fun _ => .pass) (splitRoot 0 (fun _ => c)
    (splitRoot 0 (fun _ => pack 0) .pass)), 3*C+16, ?_⟩
  rintro ⟨_|⟨u,l⟩,s⟩ E r
  · simp only [ite_true]
    refine (fits_pair (fits_bit (b:=false) (c:=fun _ => c) (h s E r))).mono ?_
    have e : (send s).count=size s := rfl
    dsimp only; simp only [e,size_tally,Nat.mul_add,Nat.mul_add,← Nat.mul_assoc, Nat.mul_comm C 2]
    simp only [Nat.mul_assoc,Nat.add_mul]
    omega
  change Fits _ _ _ (pile 0 (send (l,s)) _) ((3*C+16)*(0+1))
  apply (fits_pair (fits_pair (fits_bit (b:=false) (c:=fun _ => pack 0) (fits_pack (send l) (send s) r _ _)))).mono
  omega

private theorem ticker :
    Task (X:=Tally × ℕ) (fun i => i.1.length+i.2)
      (fun i => send (i.1,tally i.2)) (fun i => send (tally (alignment i.2 i.1),tally i.2)) := by
  let f (l:Tally) (n:ℕ) := send (tally (alignment n l),tally n)
  have he : Task (fun i : {s : Unit × Tally × ℕ // True} => charge i.val.2.2 i.val.2.1 + 1)
      (fun i => .fork (send i.val.1) (f i.val.2.1 i.val.2.2))
      (fun i => f (i.val.1::i.val.2.1) i.val.2.2) := by
    let I := {s : Unit × Tally × ℕ // True}
    have h := Task.dropLeft (fun i:I => send i.val.1) (fun i => f i.val.2.1 i.val.2.2)
    let r (i:I) := (tally (alignment i.val.2.2 i.val.2.1), tally i.val.2.2)
    apply (h.compose (cup.on r)).conform _ _ _
    · intro i; simp [r,charge, tally, show ∀ (i:Unit), (send i).count=1 from fun _=>rfl,Nat.add_comm]
    · simp
    rintro ⟨⟨u,l,n⟩,_⟩; dsimp only [r, f]
    rw [next]
    apply (show ∀ i : ℕ,(if tally i=[] then send (tally n,tally n) else send ((tally i).tail,tally n))=send (tally (if i=0 then n else i-1),tally n) from ?_) _
    intro i; cases i <;> simp [tally]
  have hg := Task.foldRight (seed := fun n => send (tally n)) (D:=fun (_ : Tally) (_ : ℕ) => True)
    (p:=fun _ => send) (f:=f) (b:=fun _ => 0) (a:=fun _ l n => charge n l+1)
    (fun _ _ _ _ => trivial) (Task.tag false _) he
  simp_rw [Task.forest_send] at hg
  apply (hg.on (fun i => ⟨i,trivial⟩)).bound 16
  rintro ⟨l,n⟩
  suffices h0 : foldCost (fun _ t => charge n t+2) l ≤ 5*l.length + alignment n l + 1 by
    have := (aligned n l).1
    change 0+foldCost (fun _ t => charge n t+2) l+1 ≤ 16*(l.length+n+1)
    omega
  induction l with
  | nil => simp [foldCost]
  | cons u l ih =>
    simp only [foldCost,List.length_cons,next,charge]
    by_cases o : alignment n l=0 <;> simp [o,charge] at * <;> omega

theorem recover_tally (s : Tally) : tally s.length = s := by
  induction s with
  | nil => rfl
  | cons _ s ih => simp [ih]

def dial (z : Tally × Tally) :=
  tally (alignment z.2.length z.1)
theorem easy_dial : Easy dial := by
  have f := ticker.on (fun (i:Tally×Tally) => (i.1,i.2.length))
  simp only [recover_tally] at f
  refine (Easy.of_bound (f:=fun i : Tally × Tally => (dial i,i.2)) f 2 ?_).fstCompose
  intro i
  rw [size_prod,size_tally,size_tally]
  omega

/- Find largest of a list of tallies by one-by-one comparison against maximum
so far. Comparing against a longer accumulated maximum is *not* charged to
that maximum; it costs linear in the offered tally. -/
-- maybe calculate if needed
end Code

end IntegerMultiplication
end Computability
end OAI
