import OAI.Computability.IntegerMultiplication.Spindle.Frame
import OAI.Computability.IntegerMultiplication.Spindle.Rate

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Spindle
open Code Strip Strip.Dims Loom Adic
-- Dims not open before?
variable {I J : Type} [Fintype J] {p D : ℕ}
@[simp] theorem plus (a : Tally) (l : List Tally) :
    volume D (a::l)=D^a.length+volume D l := rfl -- List.sum is foldl?
@[simp] theorem plus_acres (x : ℝ) (a : Tally) (l : List Tally) :
    acres x D (a::l)=((D:ℝ)^x)^a.length+acres x D l := by simp [acres]
@[simp] theorem nonce : volume D []=0 := rfl
private theorem asize (v : List Tally) (h : 2≤D) :
    size v ≤ 4*volume D v+1 := by
  have q : ∀ j:ℕ,j+1≤D^j := by
    intro j; induction j with
    | zero => simp
    | succ j i => rw [pow_succ]; have := Nat.mul_le_mul i h; omega
  induction v with
  | nil => simp
  | cons j v i =>
    rw [size_cons,size_tally, plus]
    specialize q j.length
    omega

structure Bounds (D p : ℕ) (l : List Tally) where
  scale : ℕ
  P : Tape
  G : Tape
  B : Tape
  solid : ∀ a, a∈P++G++B → 2≤a ∧ a≤p
  tallyOK : (P.length+G.length+B.length+2*volume D l:ℕ) ≤ scale

namespace Bounds
abbrev sector {l} (g : Bounds D p l) := SpanKey g.P g.G g.B (Block p (volume D l))
abbrev sectorS {l} (g : Bounds D p l) := stock p g.P g.G g.B (volume D l)

abbrev mint {l} (g : Bounds D p l) : List Tally × List Tally × List Tally × List Tally :=
  (l,Dims.shape g.P,Dims.shape g.G,Dims.shape g.B)
theorem sized {l} (g : Bounds D p l) (h : 2≤D) :
    size g.mint ≤ (4*p+13)*(g.scale+1) := by
  unfold mint
  rw [size_prod,size_prod,size_prod]
  have e := asize l h
  have a := Stair.entry_size (p:=p) g.P (fun a ha => (g.solid a (by simp [ha])).2)
  have b := Stair.entry_size (p:=p) g.G (fun a ha => (g.solid a (by simp [ha])).2)
  have c := Stair.entry_size (p:=p) g.B (fun a ha => (g.solid a (by simp [ha])).2)
  have u := g.tallyOK
  have hz := Nat.mul_le_mul_left (2*p+2) (show g.P.length+g.G.length+g.B.length≤g.scale by omega)
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.mul_assoc] at *
  omega

variable {a : Tally} {l : List Tally}
def narrow (h0 : 2≤p) (g : Bounds D p (a::l)) : Stair D p a.length where
  supplyLimit := g.scale
  north := g.P
  isle := field p (volume D l)++g.G
  south := field p (volume D l)++g.B
  tame m h := by
    have e : m∈field p (volume D l) ∨ m∈g.P++g.G++g.B := by
      simp at h ⊢; tauto
    exact e.elim (ivory h0 m) (g.solid m)
  lock := by
    simp only [List.length_append,field_length]
    have h := g.tallyOK
    rw [plus] at h
    omega

def retreat (h0 : 2≤p) (g : Bounds D p (a::l)) : Bounds D p l where
  scale := g.scale
  P := g.P++field p (D^a.length)
  G := g.G++field p (D^a.length)
  B := g.B
  solid m h := by
    have e : m∈field p (D^a.length) ∨ m∈g.P++g.G++g.B := by simp at h ⊢; tauto
    exact e.elim (ivory h0 m) (g.solid m)
  tallyOK := by
    simp only [List.length_append,field_length]
    have h := g.tallyOK
    rw [plus] at h
    omega

variable {t : I→List Tally} {r : Regime I} (s : (i:I)→Bounds D p (t i))
theorem kept (e : r.Has (fun i => (s i).mint)) :
    r.Has t ∧ Told r (fun i => (s i).P) ∧ Told r (fun i => (s i).G) ∧ Told r (fun i => (s i).B) := by
  let g := e.ez Easy.snd
  refine ⟨e.ez Easy.fst,⟨fun i a ha => ?_,g.ez Easy.fst⟩,⟨fun i a ha => ?_, (g.ez Easy.snd).ez Easy.fst⟩,
    fun i a ha => ?_, (g.ez Easy.snd).ez Easy.snd⟩
  all_goals exact ((s i).solid a (by simp [ha])).1

theorem wall {l : I→List Tally} (hd : 2≤D) (e : r.Has l)
    (h : Dom r.scale (volume D ∘ l)) :
    r.Has (tally ∘ volume D ∘ l) := by
  have ty := Computes.mapping (drawn D hd)
  have ge : r.Has (fun i => List.map (assembly D) (l i)) :=
    Regime.Small.chain e ⟨_, (Regime.Small.extent e).add h, ty.on l⟩
  have f : Easy (fun x : List (Tally × Code.Tree) => (x.map Prod.fst).flatten) := by
    exact Easy.fst.mapping.compose Easy.flatten
  have hz := ge.ez f
  have eq (l : List Tally) : tally (volume D l)=((l.map (assembly D)).map Prod.fst).flatten := by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [plus, List.map_cons, List.flatten_cons,← ih,assembly,Dims.mergeTally]
  simpa only [eq,Function.comp_def] using hz

variable [NeZero p]
variable (pH : 2≤p) (d : 2≤D)
include pH d
omit [NeZero p] in
theorem opened (e : r.Has (fun i => (s i).mint)) (h : Dom r.scale (fun i => (s i).scale)) :
    Station r (fun i => (s i).sectorS) :=
  let w := kept s e
  have v : Dom r.scale (volume D ∘ t) := h.mono (fun i => by
    change volume D _≤_
    have := (s i).tallyOK; omega)
  let u := Adic.terminal pH (fun i => volume D (t i)) (Bounds.wall d w.1 v)
  w.2.1.station.product (u.product (w.2.2.1.station.product (u.product w.2.2.2.station)))

omit [NeZero p] in
theorem inside_s {a : I → Tally}
    (s : (i:I)→Bounds D p (a i::t i))
    (e : r.Has (fun i => (s i).mint)) (h : Dom r.scale (fun i => (s i).scale)) :
    r.Has a ∧ r.Small (fun i => ((s i).narrow pH).ticket) ∧
      r.Has (fun i => ((s i).retreat pH).mint) := by
  obtain ⟨m,u,v,w⟩ := kept s e
  have f := m.ez (Easy.listCase (f:= fun i : Tally × List Tally => i.1) [] Easy.fst)
  change r.Has a at f
  have g := m.ez (Easy.listCase (f:= fun i : Tally × List Tally => i.2) [] Easy.snd)
  change r.Has t at g
  have hz := h.mono (fun i => (show D^(a i).length + volume D (t i) ≤ (s i).scale by
    have hs := (s i).tallyOK
    rw [plus] at hs; omega))
  let c i := (a i).length
  have ac : r.Has (tally ∘ c) := by simpa only [Function.comp_def,c,recover_tally] using f
  obtain ⟨z,B⟩ := juge D r c d ac (hz.mono (fun _ => Nat.le_add_right _ _))
  have T := Told.carrier pH (fun i => D^c i) z
  have U := Told.carrier pH (fun i => volume D (t i))
    (wall d g (hz.mono (fun _ => Nat.le_add_left _ _)))
  exact ⟨f,B.pair (u.shape.pair ((U.append v).shape.pair (U.append w).shape)),
    g.pair ((u.append T).shape.pair ((v.append T).shape.pair w.shape))⟩
end Bounds
end Spindle

end IntegerMultiplication
end Computability
end OAI
