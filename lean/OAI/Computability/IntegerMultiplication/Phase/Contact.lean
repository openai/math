import OAI.Computability.IntegerMultiplication.Phase.Layout
import OAI.Computability.IntegerMultiplication.Dusk.Trail

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Code Net Net.Walsh Loom Adic Packed Strip Finset
-- fin4 instance
noncomputable section
instance : Codec Clock := inferInstanceAs (Codec (Fin 4))
instance : FiniteState Clock := inferInstanceAs (FiniteState (Fin 4))

def count4 (s : List Clock) : Clock := s.sum

theorem easy_count : Easy count4 := by
  let t := fun (i j : Clock) => (j+i, ([]:List Unit))
  have h := Easy.machine (step:=t) (easy_id (X:=List Clock) |>.pair (Easy.const 0))
  have m (s : List Clock) (j : Clock) : (machine t (s,j)).2=j+count4 s := by
    induction s generalizing j with
    | nil => rw [machine_nil]; simp [count4]
    | cons a s ih =>
      rw [machine_cons]
      obtain ⟨u,k,e⟩ : ∃ u k,machine t (s,j+a)=(u,k) := ⟨_,_,rfl⟩
      specialize ih (j+a); rw [e] at ih
      simp [t,e,count4,add_assoc] at * --?
      exact ih
  simpa only [m,zero_add] using h.sndCompose

def time (v : Tally) := count4 (fill (1:Clock) v)
@[fun_prop] theorem easy_time : Easy time :=
  (easy_fill _ easy_id).compose easy_count
@[simp] theorem timely (v : Tally) : time v=(v.length:Clock) := by
  induction v <;> simp_all [time,count4,fill,add_comm]

abbrev readX (b : Walsh.B) : Clock := Walsh.digit b
def panel (v : Script) : Clock :=
  count4 ((readX (toll v.1)) :: ((v.2.1.map toll).map (show Fin 2→Clock from readX)))
@[fun_prop] theorem easy_panel : Easy panel := by
  let q : Fin 2→Clock := readX
  have d := Easy.finite q
  have g := facile_toll
  apply Easy.compose _ easy_count
  exact (((Easy.fst.compose g).compose d).pair (((Easy.snd.compose Easy.fst).compose g.mapping).compose d.mapping)).compose Easy.cons

-- first high segment flag ends at first selected bit; then middle segments
-- terminate in successive directed bits
variable {p b k : ℕ}
theorem heard (x : Packed.slot p b k) :
    panel (cut (signs p b k,Packed.badge ((baton p b k).cast x))) =
      ∑ i, readX ((x i).1.2 : Fin 2) := by
  let r := (baton p b k).cast x
  change panel (cut (signs ..,badge r))=_
  rw [peeled]
  have s : toll (lines r).1=(x 0).1.2 := by
    change toll (most ((flag p).cast r.1))=_
    rw [flag_word, show r.1 = (x 0).1 from begins ..]
    simp [toll]
  have l : ((lines r).2.1.map toll).map (fun i=> readX (i:Fin 2)) =
      List.ofFn (fun j : Fin k=> readX ((x j.succ).1.2:Fin 2)) := by
    change ((List.ofFn (fun j => most ((furrow p b).cast (r.2.1 j)))).map toll).map _=_
    simp only [List.map_ofFn]
    apply congrArg List.ofFn
    funext a
    rw [Function.comp_apply,Function.comp_apply,toll_reads, show r.2.1 a=((x a.castSucc).2,(x a.succ).1)
      from correspond ..]
  unfold panel count4
  rw [s,l,List.sum_cons,Fin.sum_univ_succ]
  congr 1
  exact List.sum_ofFn

-- Trace assembly
variable {I : Type} {r : Regime I} (H L n : I → ℕ)
abbrev scope := fun i => Track (chunks (H i) (L i)) (n i+1)
variable (c : r.Has fun i=> signs (H i) (L i) (n i)) (y : r.Has (tally ∘ extent H L n))
include y c
abbrev pin (x : Screen p b (Fin k)) := weight (fun i => (pulse (x i)).1)
theorem sight :
    Strip.Trace r (scope H L n) (fun _ a=> send (pin a)) := by
  let X i := Packed.slot (H i) (L i) (n i)
  let a (i:I) := (baton (H i) (L i) (n i)).cast
  let b i (v:X i) := badge (a i v)
  have v : Strip.Trace r (scope H L n) (fun i v=>send (b i v)) :=
    (initiative H L n y).via (fun i=> baton ..)
  apply v.tune
  let Z := Sigma X
  let s (i:I) (t:X i) := send (b i t)
  let V := onboard r s v.meter
  have h : V.Has fun i:Z=> b i.1 i.2 := onboard_hat s v.meter
  have q : V.Has fun i:Z=> signs (H i.1) (L i.1) (n i.1) :=
    onboard_small _ v.meter _ c
  have d := (q.pair h).thenDo (poly_cut.compose easy_panel.poly)
  dsimp only [b,a] at d
  simp_rw [heard] at d; exact d
end
end Phase

end IntegerMultiplication
end Computability
end OAI
