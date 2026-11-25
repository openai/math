import OAI.Computability.IntegerMultiplication.Net.Parallel
import OAI.Computability.IntegerMultiplication.Net.Schedule

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif
-- j=0,1,2
abbrev S := Fin 3
abbrev Keys (T : Type) := S → T
abbrev Sub (T : Type) := Fin 2 → T
variable {T : Type}
def fill (j : S) (p : Sub T) (t : T) : Keys T := Fin.insertNth j t p
def trim (j : S) (a : Keys T) : Sub T := a ∘ (j.succAbove)
@[simp] theorem trim_fill (j : S) (p : Sub T) (t : T) : trim j (fill j p t) = p := by
  ext i; simp [trim, fill]
@[simp] theorem fill_current (j : S) (p : Sub T) (t : T) : fill j p t j = t := by simp [fill]
@[simp] theorem fill_trim (j : S) (a : Keys T) : fill j (trim j a) (a j) = a := by
  unfold fill; exact Fin.insertNth_eq_iff.mpr ⟨rfl,rfl⟩
theorem fill_other (j : S) (p : Sub T) (t z : T) {k : S} (h : k ≠ j) :
    fill j p t k = fill j p z k := by
  induction k using j.succAboveCases
  · exact (h rfl).elim
  simp [fill]

abbrev Bank (T C : Type) := Keys T ⊕ Keys T ⊕ S × Sub T × Aux T C
variable {C : Type}
abbrev xW (a : Keys T) : Bank T C := Sum.inl a
abbrev yW (a : Keys T) : Bank T C := Sum.inr (.inl a)
abbrev qW (j : S) (p : Sub T) (a : Aux T C) : Bank T C :=
  Sum.inr (.inr (j,p,a))
abbrev Idler (T C : Type) (j : S) := {k : S // k ≠ j} × Sub T × Aux T C
abbrev Crate (T C : Type) (j : S) := Parallel.Row (Sub T) (Local T C) (Idler T C j)

def splitBank (j : S) : Bank T C → Crate T C j
| .inl t => .inl (trim j t,lx (t j))
| .inr (.inl t) => .inl (trim j t,ly (t j))
| .inr (.inr (k,p,a)) => if h:k=j then .inl (p,aux a) else .inr (⟨k,h⟩,p,a)
def mixBank (j : S) : Crate T C j → Bank T C
| .inl (p,.inl t) => xW (fill j p t)
| .inl (p,.inr (.inl t)) => yW (fill j p t)
| .inl (p,.inr (.inr a)) => qW j p a
| .inr (k,p,a) => qW k p a

def parcel (j : S) : Bank T C ≃ Crate T C j where
  toFun := splitBank j
  invFun := mixBank j
  left_inv := by
    rintro (_|_|⟨k,p,a⟩)
    · simp [mixBank, splitBank, lx]
    · simp [mixBank, splitBank, ly]
    by_cases h : k=j
    · subst k; simp [splitBank, mixBank, aux]
    simp [splitBank, mixBank, h]
  right_inv := by
    rintro (⟨p,(_|_|_)⟩|⟨k,p,a⟩)
    all_goals simp [mixBank, splitBank, xW, yW, qW, lx, ly, aux]
    exact k.property

@[simp] theorem parcel_app (j : S) (a : Bank T C) : parcel j a = splitBank j a := rfl
@[simp] theorem parcel_rev (j : S) (a : Crate T C j) : (parcel j).symm a = mixBank j a := rfl

namespace Pad
variable {L : Type}
/-- sequence of labelled touches (per invocation supplied labels) -/
def wrap (r : Touch T C) (l : Sub T → Local T C → L) (_j : S:=0) :
    Sub T → Hop (Local T C) L := fun p => r.hop (l p)
def nothing (l : Sub T → Local T C → L) :
    Sub T → Hop (Local T C) L := fun p => ⟨l p, fun _ _ => .none⟩
def eight (l0 l1 l2 l3 l4 l5 l6 l7 F : Sub T → Local T C → L)
    (rs : List (Touch T C)) : List (Sub T → Hop (Local T C) L) :=
  List.zipWith (fun r l => wrap r l 0) rs [l0,l1,l2,l3,l4,l5,l6,l7] ++ [nothing F]

variable [DecidableEq T] [Fintype T] [Fintype C] {R : Type} [Ring R]

omit [DecidableEq T] in
theorem ops_eval (rs : List (Touch T C)) (ls : List (Sub T → Local T C → L))
    (len : rs.length=ls.length) (F : Sub T → Local T C → L) (h : R) (z : View T C R)
    (p : Sub T) :
    ((List.zipWith (fun r l => wrap r l 0) rs ls ++ [nothing F]).map (fun a => a p)).foldl
      (fun b e => e.run h b) z.val =
      (rs.foldl (Pairing.evalStep h) z).val := by
  induction rs generalizing ls z with
  | nil =>
    simp only [List.zipWith_nil_left, List.nil_append, List.map_cons, List.map_nil,
      List.foldl_cons, List.foldl_nil]
    funext a
    simp [nothing, Hop.run]
  | cons r rs ih =>
    cases ls with
    | nil => simp at len
    | cons e ls =>
      simp only [List.zipWith_cons_cons, List.cons_append, List.map_cons,
        List.foldl_cons, wrap, Touch.run_hop]
      exact ih ls (by simpa using len) _

/-- Unassemble arbitrary bank array as family of plane inputs and idlers -/
def actSeq (j : S) (w : Bank T C → R) (p : Sub T) : View T C R :=
  View.load fun r => w (mixBank j (.inl (p,r)))
def sleepSeq (j : S) (w : Bank T C → R) (g : Idler T C j) :=
  w (mixBank j (.inr g))

omit [DecidableEq T] [Fintype T] [Fintype C] [Ring R] in
theorem toSeq (j : S) (w : Bank T C → R) :
    w = Parallel.join (fun p => (actSeq j w p).val) (sleepSeq j w) ∘ (parcel j) := by
  funext a
  obtain ⟨b,rfl⟩ := (parcel j).symm.surjective a
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  simp only [parcel_rev, actSeq, View.val_load]
  rcases b with ⟨_,_⟩|_
  all_goals rfl

theorem job_run (j : S) (J : Parallel.Job (Sub T) (Local T C) (Idler T C j) L)
    (h : R) (w : Bank T C → R) :
    (J.weave (parcel j)).logical h w =
      Parallel.join (fun p => (J.child p).logical h (actSeq j w p).val)
        (sleepSeq j w) ∘ parcel j := by
  conv_lhs => rw [toSeq j w]
  exact Parallel.Job.weave_run ..

end Pad
end Net.Motif

end IntegerMultiplication
end Computability
end OAI
