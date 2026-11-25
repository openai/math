import OAI.Computability.IntegerMultiplication.Packed.Active

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
-- or fold
private def foldO (i : Bool) (p : Bool) := (i || p,([]:Tally))
def arity (l : List Bool) := l.any id
theorem arity_easy : Easy arity := by
  suffices g : arity = fun (l : List Bool) => (machine foldO (l,false)).2 from
    g ▸ (Easy.machine (step:=foldO) ((Easy.pair easy_id (Easy.const _)))).sndCompose
  have h (l : List Bool) (v : Bool) : (machine foldO (l,v)).2=(arity l || v) := by
    induction l generalizing v with
    | nil => simp [machine_nil,arity]
    | cons a l ih =>
      rw [machine_cons,foldO]
      -- match product reduction
      obtain ⟨p,t,h⟩ : ∃ p t,machine foldO (l,a||v)=(p,t) := ⟨_,_,rfl⟩
      simp only [arity,List.any_cons,id_eq,h]
      specialize ih (a||v)
      rw [h] at ih
      simp only at ih
      simp [← Bool.or_assoc,Bool.or_comm,ih,arity]
  funext l; rw [h]; simp
end Code

namespace Packed
open Code Adic Strip
variable {H L i : ℕ}
private theorem nonz (l : Raw 2) :
    code l = 0 ↔ l.any (fun i => decide (i≠0))=false := by
  induction l with
  | nil => simp [Adic.code]
  | cons f l ih =>
    fin_cases f
    · simpa [code] using ih
    · simp [code]
private def flip_ (l : Raw 2) := veil l
private def any4 (l : Raw 2) :=
  arity ((l.drop 2).map fun i => decide (i ≠ 0))
private theorem near (l : Raw 2) : any4 l=false ↔ code l<4 := by
  have eq : any4 l=(l.drop 2).any fun i => decide (i≠0) := by apply Bool.eq_iff_iff.mpr; simp only [any4,arity,List.any_eq_true,List.mem_map]; simp
  rw [eq,← nonz]
  have q := Adic.cat (l.take 2) (l.drop 2)
  rw [List.take_append_drop] at q
  have e := limit (l.take 2)
  by_cases v : l.length≤2
  · have f : l.drop 2=[] := List.drop_eq_nil_iff.mpr v
    have hx : code l < 4 := (limit l).trans_le (le_trans (Nat.pow_le_pow_right (by decide) v) (by decide : 2^2≤4))
    simp [f, Adic.code, hx]
  rw [List.length_take,Nat.min_eq_left (by omega)] at *
  norm_num at e q
  omega

private theorem easy_4 : Easy any4 := by
  have q : Easy (fun l : Raw 2 => l.drop 2) :=
    (easy_cut ((Easy.const (tally 2)).pair easy_id)).sndCompose
  unfold any4
  exact (q.compose ((Easy.finite _).mapping)).compose arity_easy

-- segment syndrome requires deciding if guards after reversing and dropping parity are near 0 or near max
private def defect (x : Raw 2) :=
  let a := x.reverse.tail
  !any4 a || !any4 (flip_ a)

private theorem tail_eq_mirror (x : Seg L H) :
    least (mirror (guard H L x)) = flip_ (least (guard H L x)) := by
  exact (Holds.std _).single (by rw [reflects]; exact turned (Holds.std _))

theorem defect_eq (x : Seg L H) :
    defect (most ((furrow H L).cast x)) = hazard x := by
  simp only [defect,furrow_word,List.reverse_append,hazard,short]
  rw [number,number,tail_eq_mirror]
  cases g : any4 (least (guard H L x)) <;> cases h : any4 (flip_ (least (guard H L x)))
  all_goals
    have e := near (least (guard H L x)); have d := near (flip_ (least (guard H L x)))
    simp only [least] at *
    simp_all
    all_goals
      have he : ¬ code (List.reverse (most (guard H L x))) < 4 := Nat.not_lt.mpr e
      have hd : ¬ code (flip_ (List.reverse (most (guard H L x)))) < 4 := Nat.not_lt.mpr d
      simp [he, hd]

private theorem easy_defect : Easy defect := by
  have h : Easy (fun l : Raw 2 => l.reverse.tail) := by
    have h : Easy (fun l:Raw 2 => l.tail) := by
      have u := Easy.listCase (X:=Fin 2) ([]:Raw 2) Easy.snd
      have v : (fun l:Raw 2=>l.tail)=
          (fun x => List.casesOn (motive:=fun _=>Raw 2) x [] fun _ a => a) :=
        funext fun l => by cases l <;> rfl
      exact v ▸ u
    exact Easy.reverse.compose h
  let f := fun (v:Bool × Bool)=> (!v.1 || !v.2)
  have x : Easy flip_ := by unfold flip_ veil; exact (Easy.finite _).mapping
  exact ((h.compose easy_4).pair ((h.compose x).compose easy_4)).compose (Easy.finite f)

def trap (v : Dim × Raw 2) := arity ((cut v).2.1.map defect)
theorem easy_trap : Poly trap :=
  ((poly_cut.sndCompose.fstCompose).compose easy_defect.mapping.poly).compose arity_easy.poly
theorem trap_hold (x : Queue H L i) :
    trap (signs H L i,badge x) = taint x := by
  unfold trap
  rw [peeled]
  unfold taint
  apply Bool.eq_iff_iff.mpr
  simp [arity,lines]
  -- private segment remains
  apply exists_congr
  intro x_1
  exact (by
    erw [defect_eq])

def regions (p : Dim × Raw 2 × Raw 2) :=
  trap (p.1,p.2.1)||trap (p.1,p.2.2)
theorem easy_regions : Poly regions := by
  exact (((by fun_prop : Poly (fun p : Dim × Raw 2 × Raw 2 => (p.1,p.2.1))).compose easy_trap).pair
    ((by fun_prop : Poly (fun p : Dim × Raw 2 × Raw 2 => (p.1,p.2.2))).compose easy_trap)).compose
      ((Easy.finite (fun x:Bool×Bool=>x.1||x.2)).poly)
theorem zone (x : Plate H L i) :
    regions (signs H L i,badge x.2.1,badge x.2.2) = spotted x := by simp [regions,trap_hold,spotted]
end Packed

end IntegerMultiplication
end Computability
end OAI
