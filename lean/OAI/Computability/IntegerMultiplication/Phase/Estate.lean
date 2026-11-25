import OAI.Computability.IntegerMultiplication.Phase.Dawn

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Shuttle Net.Tensor Net.Walsh Strip Strip.Dims Strip.Optic Code Packed Loom Dusk
open Finset

structure Estate (D e : ℕ) where
  metres : ℕ
  shade : ℕ -- w word count -1
  tops : ℕ
  foot : ℕ
  sunrise : Tape
  sunset : Tape
  radix : ∀ a∈sunrise++sunset, 2≤a ∧ a≤base
  range : sunrise.length + e*width tops foot + sunset.length + shade +1 ≤ metres
  okay : safe e (width tops foot)
namespace Estate
variable {D e : ℕ}
abbrev keys (x : Estate D e) := Base x.sunrise x.sunset (Screen x.tops x.foot (Fin e))
abbrev terrain (x : Estate D e) := plain x.sunrise x.sunset x.tops x.foot e
theorem rays (x : Estate D e) :
    (∀a∈x.sunrise, 2≤a ∧ a≤base) ∧ (∀a∈x.sunset,2≤a ∧ a≤base) := by
  simpa only [List.forall_mem_append] using x.radix

def cert (d : ℕ) (x : Estate D e) :=
  Tree.fork (beacon D d) (send (tally x.tops,tally x.foot,shape x.sunrise,shape x.sunset))

theorem pid {d : ℕ} (x : Estate D e) (h : 2 ≤ D) (z : D^d=e) :
    (x.cert d).count ≤ (2*base+28)*(x.metres+1) := by
  have v := Stair.entry_size x.sunrise (p:=base) (fun _ g=>(x.rays.1 _ g).2)
  have g := Stair.entry_size x.sunset (p:=base) (fun _ g=>(x.rays.2 _ g).2)
  have t := Stair.beacon_size D d h
  rw [z] at t
  change (beacon D d).count+size (_,_,_,_)+1 ≤ _
  simp only [size_prod,size_tally,tally_length,Nat.mul_add]
  have m := x.range
  have w₀ : 1≤width x.tops x.foot := by unfold width; omega
  have e₀ : 1≤e := z ▸ one_le_pow₀ (by omega)
  have eq : e≤e*width x.tops x.foot := Nat.le_mul_of_pos_right _ w₀
  have vq : x.tops+x.foot ≤ e*width x.tops x.foot := by unfold width at *; nlinarith
  have b := Nat.mul_le_mul_left (2*base+2)
    (show x.sunrise.length+x.sunset.length ≤ x.metres from by omega)
  -- avoid nlinarith unfolding base
  simp only [Nat.mul_add,Nat.add_mul] at b v g ⊢; omega
end Estate

noncomputable section
variable {W : Type} (D : ℕ) [Fintype W]
structure Prairie (D : ℕ) (W : Type) (k : ℕ) where
  plot : Estate D (D^k)
  radio : ℕ
  silo : plot.keys → Frame W radio k→Grain plot.shade

abbrev QuestP := Sigma (Prairie D W)

abbrev tapes (Y : QuestP (W:=W) D) := Y.2.plot -- "tapes" structure
abbrev cargo (R : Series W) (Y : QuestP (W:=W) D) :=
  skein W R Y.2.radio Y.1
abbrev goodsP (R : Series W) (Y : QuestP (W:=W) D) :=
  stripe Y.2.plot.terrain (fun x=> Loom.strip (cargo D R Y) fun v=> Dusk.mark (Y.2.silo x v))

def map_ (u : 2 ≤ D) : Regime (QuestP (W:=W) D) where
  scale t := t.2.plot.metres
  header t := t.2.plot.cert t.1
  gauge := ⟨1,2*base+28,fun t=> by simp [t.2.plot.pid u rfl]⟩

def oracle (R : Series W) : Job (QuestP (W:=W) D) where
  issue x := Tree.fork (x.2.plot.cert x.1) (goodsP D R x)
  reply x := stripe x.2.plot.terrain (fun a=> Loom.strip (cargo D R x) fun v=>
    Dusk.mark (runOn (pointed false) x.2.silo a v))

-- obtain Normal descriptor
variable {D} {I : Type}
def weak (f _g : Tally) := tally f.length -- temporary
variable {r : Regime I}
abbrev roof (Y : I→QuestP (W:=W) D) i := (Y i).2.plot.cert (Y i).1
-- in outdoor Regime, read dimensions
private theorem pieces {v w : I→Tree} (h : Regime.Small r (together v w)) :
    r.Small v ∧ r.Small w := by
  have e := h.extent
  exact ⟨h.chain ⟨_,e, (Code.Task.dropRight v w).mono (by simp [Tree.count])⟩,
    h.chain ⟨_,e,(Code.Task.dropLeft v w).mono (by simp [Tree.count]; omega)⟩⟩

variable (Y : I→QuestP (W:=W) D)
variable (h : r.Small (roof Y))
include h
omit [Fintype W] in
private theorem split_ :
    r.Small (fun i => beacon D (Y i).1) ∧
    r.Has (fun i => (tally (Y i).2.plot.tops,tally (Y i).2.plot.foot,shape (Y i).2.plot.sunrise,shape (Y i).2.plot.sunset)) := pieces h

omit [Fintype W] in
theorem profiles :
    Told r (fun i => (Y i).2.plot.sunrise) ∧ Told r (fun i => (Y i).2.plot.sunset) ∧
    r.Has (fun i=>tally (Y i).2.plot.tops) ∧ r.Has (fun i=>tally (Y i).2.plot.foot) := by
  obtain ⟨a,b⟩ := split_ Y h
  refine ⟨⟨fun i a g=>((Y i).2.plot.rays.1 _ g).1,?_⟩,⟨fun i a g=>((Y i).2.plot.rays.2 _ g).1,?_⟩,
    b.ez Easy.fst,(b.ez Easy.snd).ez Easy.fst⟩
  · exact (((b.ez Easy.snd).ez Easy.snd).ez Easy.fst)
  exact (((b.ez Easy.snd).ez Easy.snd).ez Easy.snd)
abbrev violet i := (Y i).1
omit [Fintype W] in
theorem children :
    r.Has (green ∘ violet Y) ∧ r.Has (fun i=> tally (D^violet Y i)) ∧ r.Small (trunk D ∘ violet Y) := by
  have e := (split_ Y h).1
  change r.Small (fun i=> beacon D (violet Y i)) at e
  simp_rw [nook] at e
  have i0 := pieces (v:=send ∘ green ∘ violet Y) (w:=fun i =>
    Tree.fork (send (tally (D^violet Y i))) (trunk D (violet Y i))) e
  exact ⟨i0.1,pieces i0.2⟩

omit h
theorem controlFiber (H G f : I→ℕ)
    (u : r.Has (tally ∘ H)) (z : r.Has (tally ∘ G)) (q : r.Has (tally ∘ f)) :
    r.Has (tally ∘ dect H G f) ∧ r.Has fun i => signs (H i) (G i) (f i-1) := by
  constructor
  · have y := (u.pair z).ez (show Easy (fun x:Tally×Tally=> ()::x.1++x.2) from by fun_prop)
    have s := (q.pair y).thenDo (Packed.chamber (X:=Tally))
    have a : ∀ l : Tally,tally l.length=l := by
      intro l
      symm; exact List.eq_replicate_length.mpr (by simp)
    have χ (i:I) :
        tally (dect H G f i) = List.flatten ((tally (f i)).map (fun _ : Unit=> ()::(tally (H i))++tally (G i))) := by
      let M := ()::(tally (H i))++tally (G i)
      let c := tally (f i)
      change _ = (c.map (fun _ => M)).flatten
      have E (e : Tally) : ((e.map (fun _=> M)).flatten).length=e.length*M.length := by
        induction e <;> simp_all [Nat.add_mul]; omega
      conv_rhs => rw [← a (List.flatten _),E,tally_length]
      congr 2
      simp [M,width,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] --?
    simp_rw [Function.comp_def,χ]
    exact s.ez Easy.flatten
  let dec := fun t:Tally => (cutLists ([()],t)).2
  have e := q.ez (show Easy dec from (easy_cut ((Easy.const [()]).pair easy_id)).sndCompose)
  have a (i:ℕ) : dec (tally i)= tally (i-1) := by simp [dec,cutLists,tally]
  exact u.pair (z.pair (by simpa only [Function.comp_def,a] using e))
end
end Phase

end IntegerMultiplication
end Computability
end OAI
