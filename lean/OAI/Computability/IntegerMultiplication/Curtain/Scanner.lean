import OAI.Computability.IntegerMultiplication.Curtain.Lace
import OAI.Computability.IntegerMultiplication.Earth.Climate

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Curtain
open Strip Code Packed Loom Adic Earth Phase Net Net.Walsh Strip.Dims
variable {L S U : ℕ}
abbrev Attach (L S U : ℕ) := Pin (Fin L) (Fin S) (Fin U)
abbrev Solo := Tally
abbrev Alliance := Tally × Tally
abbrev Report := List Solo × List Alliance
def report (a : Attach L S U) : Report :=
  (List.ofFn (fun i=> tally (a (Sum.inl i)).val),
   List.ofFn (fun i => (tally (a (Sum.inr (i,0))).val,tally (a (Sum.inr (i,1))).val)))

noncomputable section
def skim (x : Raw 2 × Tally) := (x.1.drop x.2.length).headD 0
@[fun_prop]
theorem easy_skim : Easy skim := by
  have a : Easy (fun p : Raw 2=>p.headD 0) :=
    by simpa only [toll,List.reverse_reverse] using Easy.reverse.compose facile_toll
  exact (Easy.exchange.compose (easy_cut Easy.identity).sndCompose).compose a

def take1 (x : Raw 2 × Tally) := readX (skim x)
@[fun_prop] theorem take1_easy : Easy take1 := easy_skim.compose (Easy.finite (fun (a : Fin 2)=> readX a))
def hitch (x : Fin 2 × Fin 2) : Clock := exp2 ((x.1:B)*(x.2:B))
def take2 (x : Raw 2 × Alliance) :=
    hitch (skim (x.1,x.2.1),skim (x.1,x.2.2))
@[fun_prop] theorem take2_easy : Easy take2 := by
  have z := Easy.finite hitch
  unfold take2
  apply Easy.compose _ z; fun_prop

section
variable {T X Y : Type} [Codec T] [Codec X] [Codec Y]
-- move to Code later. lock t.map x
def stripes (f : X×T→Y) (g:X×List T) := g.2.map (fun t=> f (g.1,t))
@[fun_prop] theorem flatten_stripes (f : X × T → Y) (x0 : X) (a:T) (h : Easy f) : Poly (stripes f) := by
  let w := fun (g:X×List T)=> (g.2.map (fun _=>g.1),g.2)
  have q (p : X) (t : List T) :
      lock f x0 a (t.map (fun _=> p),t)=t.map (fun s=> f (p,s)) := by
    -- use fair map
    unfold lock
    have v := IntegerMultiplication.Code.fair (fun _=>p) id t x0 a
    simp only [List.map_id] at v
    rw [v,List.map_map]; rfl
  have e : Poly w := by
    have d :
        Poly (fun g : X×List T => (ruler g.2).map (fun _=> g.1)) :=
      ((Easy.pair (by fun_prop) Easy.fst).poly).compose chamber
    simp only [ruler,List.map_map] at d
    exact d.pair Easy.snd.poly
  unfold stripes
  simpa only [w,q,stripes] using e.compose (easy_lock f h x0 a).poly
end

def space (p : Raw 2 × Report) : Clock :=
  count4 (stripes take1 (p.1,p.2.1)++stripes take2 (p.1,p.2.2))
@[fun_prop]
theorem measure : Poly space := by
  have a := flatten_stripes take1 [] [] take1_easy
  have q := flatten_stripes take2 [] ([],[]) take2_easy
  unfold space
  apply Poly.compose _ easy_count.poly
  fun_prop

-- correctness
theorem peek0 (x : Block 2 L) (i : Fin L) :
    skim (most x,tally i.val)=(layBit L x) i := by
  unfold skim
  -- lemma list
  have q : ∀ (l:Raw 2) (n:ℕ) (h:n < l.length), (l.drop n).headD 0 = l[n] := by
    intro l; induction l with
    | nil=> simp
    | cons a l ih=> intro n h; cases n with
      | zero=> rfl
      | succ n=> exact ih n (by simpa using h)
  change ((most x).drop (tally i.val).length).headD 0=(most x)[i.val]'_
  rw [tally_length,q (most x) i (by simp)]
theorem sent (a : Attach L S U) (x : Block 2 L) :
    space (most x,report a)=Pin.q a (layBit L x) := by
  simp only [space,count4,stripes,report,List.map_ofFn,Function.comp_def,List.sum_append,Pin.q,
    Pin.dx,Pin.lo,Pin.hi,Pin.mate,Pin.alone,take1,take2,hitch,peek0]
  rw [List.sum_ofFn,List.sum_ofFn]
  rfl
end

noncomputable section
-- exported Trace exposing the most bits of any middle field at Regime cost
variable {I X Y : Type} [Codec X] [Codec Y] {r : Regime I} {A:I→Type} {s:(i:I)→Series (A i)}
theorem aims (v : (i:I)→A i→X) (h : Strip.Trace r s (fun _i a => send (v _i a)))
    (f : X→Y) (g : Poly f) : Strip.Trace r s (fun i a=>send (f (v i a))) :=
  h.tune (Regime.Has.thenDo (r:=onboard r (fun i a => send (v i a)) h.meter)
    (onboard_hat (r:=r) (fun i a => send (v i a)) h.meter : Regime.Has _ (fun i : Sigma A=> v i.1 i.2)) g)
variable (L f u : I→ℕ) (Q : (i:I)→Attach (L i) (f i) (u i))
variable (H : r.Has (tally ∘ L))
include H

theorem issues :
    Strip.Trace r (fun i=> line 2 (L i)) (fun _ a=> send (least a)) := by
  obtain ⟨C,E⟩ : ∃ C:ℕ,∀ a:Fin 2,size a+1 ≤ C :=
      ⟨∑ a:Fin 2,(size a+1),fun a => Finset.single_le_sum (f:=fun a:Fin 2 => size a+1) (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)⟩
  have hd : Dom r.scale L := (Regime.Small.extent (k:=fun x => send (tally (L x))) (r:=r) H).mono
    (fun x => by change _ ≤ size (tally _); rw [size_tally,tally_length]; omega)
  let T := fun x:I=>Block 2 (L x)
  refine ⟨Adic.terminal (p:=2) (by decide) _ H, ((Dom.const _ C).mul (hd.map (Sigma.fst:Sigma T→I)) |>.add (Dom.const _ 1)).mono ?_,
    Adic.marked (p:=2) (by decide) L H (fun x => (lineSize ..).ge)⟩
  intro x; change size _ ≤ C*_+1; simpa only [length'] using raw_size 2 C E (least x.2)

variable (D : r.Has (fun i=> report (Q i)))
include D
theorem signals :
    wish (r:=r) (fun i=>line 2 (L i)) (fun i a=> Pin.q (Q i) (layBit _ a)) := by
  let T := fun x:I=> Block 2 (L x)
  have v : Strip.Trace r (fun i=>line 2 (L i)) (fun i v=>send (most v)) := by
    have u := issues L H
    have t := aims (fun i (v:T i)=> least v) u List.reverse Easy.reverse.poly
    simpa [least] using t
  apply v.tune
  let Z := Sigma T
  let s (i:I) (t:T i) := send (most t)
  let V := onboard r s v.meter
  have h : V.Has fun i:Z=> most i.2 := onboard_hat s v.meter
  have z : V.Has fun i:Z=> report (Q i.1) := onboard_small _ v.meter _ D
  have d := (h.pair z).thenDo measure
  simp_rw [sent] at d; exact d
theorem jig (P T : I→Tape) (W : Told r P) (Y : Told r T) :
    wish (r:=r) (fun i=> comfort (P i) (T i) (L i))
      (fun i a=> Pin.q (Q i) ((locker (P i) (T i) (L i) a).1)) :=
  w_left _ _ W.station _ (w_right _ _ _ (signals L f u Q H D) Y.station)
end
end Curtain

end IntegerMultiplication
end Computability
end OAI
