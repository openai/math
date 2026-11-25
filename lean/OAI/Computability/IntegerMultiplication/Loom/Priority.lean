import OAI.Computability.IntegerMultiplication.Loom.Skein
import OAI.Computability.IntegerMultiplication.Loom.Network

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Dims Adic Code
variable {J L W : Type} [DecidableEq J] [Fintype J] [Fintype W]
variable {p : ℕ} {discount : ℝ}
noncomputable section

structure Stair (D p k : ℕ) where
  supplyLimit : ℕ
  north : Tape
  isle : Tape
  south : Tape
  tame : ∀ a∈north++isle++south,2≤a ∧ a≤p
  lock : (north.length + isle.length + south.length + 2 * D ^ k : ℕ) ≤ supplyLimit

variable (p) (P G B : Tape)
abbrev SpanKey (T : Type) := Pin P × T × Pin G × T × Pin B
abbrev swapper {T : Type} (x : SpanKey P G B T) : SpanKey P G B T :=
  (x.1,x.2.2.2.1,x.2.2.1,x.2.1,x.2.2.2.2)
abbrev stock (j) := Path P (line p j) G (line p j) B
-- include descendant controllers
def beacon (D : ℕ) : ℕ → Tree
| 0 => .fork (.atom false) (.fork (send (tally 1)) (.atom false))
| k+1 => .fork (.atom true) (.fork (send (tally (D^(k+1)))) (beacon D k))
def green : ℕ→Bool
| 0 => false
| _+1 => true
def trunk (D : ℕ) : ℕ→Tree
| 0 => .atom false
| k+1 => beacon D k
@[simp] theorem nook (D k : ℕ) : beacon D k =
    .fork (.atom (green k)) (.fork (send (tally (D^k))) (trunk D k)) :=
  match k with
  | 0 => rfl
  | _+1 => rfl

variable {p}
namespace Stair
variable {D k : ℕ}
def ticket (v : Stair D p k) : Tree :=
  Tree.fork (beacon D k) (send (shape v.north,shape v.isle,shape v.south))
theorem beacon_size (D k) (h : 2≤D) : (beacon D k).count ≤ 16*D^k := by
  induction k with
  | zero => rw [pow_zero]; change 7≤16*1; decide
  | succ k ih =>
    rw [beacon,Tree.count,Tree.count,Tree.count, show (send (tally _)).count=size (tally _) from rfl,
      size_tally,tally_length,pow_succ]
    have : D^k * 2 ≤ D^k*D := Nat.mul_le_mul_left _ h
    have hi : 1≤D^k := one_le_pow₀ (by omega)
    omega
theorem entry_size (v : Tape) (h : ∀a∈v,a≤p) :
    size (shape v) ≤ (2*p+2)*v.length+1 := by
  induction v with
  | nil => simp
  | cons a v ih =>
    specialize ih (fun i hi => h _ (List.mem_cons_of_mem _ hi))
    specialize h a List.mem_cons_self
    rw [shape_cons,size_cons,size_tally,tally_length,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega
theorem entries (v : Stair D p k) :
    (∀a∈v.north,2≤a ∧ a≤p) ∧ (∀a∈v.isle,2≤a ∧ a≤p) ∧ (∀a∈v.south,2≤a ∧ a≤p) :=
  ⟨fun a ha => v.tame a (by simp [ha]),fun a ha => v.tame a (by simp [ha]),fun a ha => v.tame a (by simp [ha])⟩

theorem small (h : 2≤D) (v : Stair D p k) : v.ticket.count ≤ (2*p+24)*(v.supplyLimit+1) := by
  obtain ⟨a,b,c⟩ := v.entries
  have ha := entry_size v.north (fun i e => (a i e).2)
  have hb := entry_size v.isle (fun i e => (b i e).2)
  have hc := entry_size v.south (fun i e => (c i e).2)
  have l := v.lock
  have e := Nat.mul_le_mul_left (2*p+2) (show v.north.length+v.isle.length+v.south.length≤v.supplyLimit by omega)
  have g := beacon_size D k h
  change (beacon D k).count+size (_,_,_)+1 ≤ _
  rw [size_prod,size_prod]
  simp only [Nat.mul_add] at e ⊢
  simp only [Nat.add_mul] at *
  omega
end Stair

structure Boll (D p : ℕ) (W : Type) (k : ℕ) where
  site : Stair D p k
  cargo : ℕ
  option : SpanKey site.north site.isle site.south (Block p (D^k))→Frame W cargo k→Bead

abbrev Where (D p : ℕ) (W : Type) := Sigma (Boll D p W)

namespace Where
open Adic
variable {D : ℕ}
abbrev site (w : Where D p W) := w.2.site
abbrev plates (w : Where D p W) :=
  stock p w.site.north w.site.isle w.site.south (D^w.1)
abbrev cap (R : Series W) (w : Where D p W) (t) := strip (skein W R w.2.cargo w.1) (w.2.option t)
def government (D p : ℕ) (W : Type) (h : 2≤D) :
    Regime (Where D p W) where
  scale w := w.site.supplyLimit
  header w := w.site.ticket
  gauge := ⟨1,2*p+24, fun w => by simpa using w.2.site.small h⟩

def current (R : Series W) : Job (Where D p W) where
  issue w := .fork w.site.ticket (stripe w.plates (cap R w))
  reply w := stripe w.plates ((cap R w) ∘ swapper _ _ _)

-- polymorphic indices having Regime.Has Stair.ticket
variable {I : Type} {r : Regime I}
private theorem split_small {v w : I→Tree}
    (h : Regime.Small r (together v w)) :
    r.Small v ∧ r.Small w := by
  have e := h.extent
  exact ⟨h.chain ⟨_,e, (Task.dropRight v w).mono (by simp [Tree.count])⟩,
    h.chain ⟨_,e,(Task.dropLeft v w).mono (by simp [Tree.count]; omega)⟩⟩
theorem ticket_told (k : I→ℕ) (t : (i:I)→Stair D p (k i))
    (h : r.Small fun i => (t i).ticket) :
    Told r (fun i => (t i).north) ∧ Told r (fun i => (t i).isle) ∧ Told r (fun i => (t i).south) := by
  have he : r.Has (fun i => (shape (t i).north,shape (t i).isle,shape (t i).south)) :=
    (split_small (v:=fun i => beacon D (k i)) h).2
  exact ⟨⟨fun i a ha => ((t i).entries.1 _ ha).1,he.ez Easy.fst⟩,
    ⟨fun i a ha => ((t i).entries.2.1 _ ha).1, (he.ez Easy.snd).ez Easy.fst⟩,
    fun i a ha => ((t i).entries.2.2 _ ha).1,(he.ez Easy.snd).ez Easy.snd⟩
theorem signals (k : I→ℕ) (t : (i:I)→Stair D p (k i))
    (h : r.Small fun i => (t i).ticket) :
    r.Has (green ∘ k) ∧ r.Has (fun i => tally (D^k i)) ∧ r.Small (trunk D ∘ k) := by
  have z : r.Small (beacon D ∘ k) := (split_small (w:=fun i =>
    send (shape (t i).north,shape (t i).isle,shape (t i).south)) h).1
  have e := z
  simp only [Function.comp_def] at e
  -- rw nested beacon infinitely: nook doesn't call beacon unless trunk irreducible
  simp_rw [nook] at e
  have a := split_small (v:=send ∘ green ∘ k) (w:=fun i =>
    (Tree.fork (send (tally (D^k i))) (trunk D (k i)))) e
  exact ⟨a.1,split_small a.2⟩

theorem descendants (k : I→ℕ)
    (h : r.Small (beacon D ∘ k)) :
    r.Has (fun i => tally (D^k i)) := by
  have e := h
  simp_rw [Function.comp_def,nook] at e
  exact (split_small ((split_small (v:=send ∘ green ∘ k) (w:=fun i =>
    (Tree.fork (send (tally (D^k i))) (trunk D (k i)))) e).2)).1
omit [Fintype W] in
theorem station_t (w : I → Where D p W) (hp : 2≤p)
    (h : Regime.Small r fun i => (w i).site.ticket) :
    Station r (fun i => plates (w i)) := by
  let : NeZero p := ⟨by omega⟩
  obtain ⟨a,b,c⟩ := ticket_told (Sigma.fst ∘ w) (fun i => (w i).site) h
  have f := terminal hp (fun i => D^(w i).1) (signals (Sigma.fst ∘ w) (fun i => (w i).site) h).2.1
  exact a.station.product (f.product (b.station.product (f.product c.station)))
end Where
end
end Loom

end IntegerMultiplication
end Computability
end OAI
