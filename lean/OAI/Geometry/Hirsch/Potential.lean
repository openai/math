import OAI.Geometry.Hirsch.Legs

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.World

open Board Naming

variable {X : Type} {n : ℕ} {u : Dials} {v : u.Valid} {w : World X n} {width : ℕ} {hw : 3 ≤ width}
  (A : (w.legs width v hw).Decoration) (z : Sample u)

def occurs (x : X) := A.Occurs v z (.inl x)

theorem blank_free (x : X) (hb : w.Blank width x) : ¬occurs A z x :=
  fun hh => (w.mid_real width (u.a^u.h) hw (pow_pos (by have := v.base; omega) _) x).mp hh.1 hb

theorem permits {x : X} {d : Bool} {s : ℕ}
    (hh : ∀ g ∈ (A.round v z).charge (.inl x) d, (w.legs width v hw).w.place g = s) :
    w.Permitted width (u.a^u.h) (occurs A z) s d x := by
  intro y hy ho
  let r := A.round v z
  let b := (w.legs width v hw).w
  have hm : r.mark (.inl x) d := ⟨.inl y,hy,ho⟩
  have key := hh _ (r.charge_mem.mpr ⟨hm,rfl⟩)
  have eq := (b.middle_step (r.middle _ _ hm).1 (r.middle _ _ hm).2 d).2
  have he : b.place (.inl x) = w.index width (u.a^u.h) x := w.at_real width (u.a^u.h) hw (pow_pos (by have := v.base; omega) _) x
  exact (congrArg (· % (u.a^u.h)) hy.info.2.2.1).trans (he.symm.trans (eq.symm.trans key))

theorem expand {i j : Compressed X} {b : Budget} {path : List (Compressed X)} {par s : ℕ}
    (ht : (A.round v z).Trip Set.univ i j b path) (hd : ¬(w.legs width v hw).w.live j)
    (hh : ∀ g ∈ path, (w.legs width v hw).w.place g = s) :
    ∀ e, w.Resume width (u.a^u.h) (occurs A z) par s e (Board.Network.total u b) i := by
  induction ht with
  | @nil i b =>
    intro e
    rcases i with x | t
    swap
    · exact True.intro
    have hb : w.Blank width x := by_contra (fun h => hd (.inl h))
    have hs : w.Stop width (u.a^u.h) x := by
      by_cases hl : w.live x
      · exact .inr (by_contra fun hn => hd (.inr ⟨hl,hn⟩))
      · exact .inl hl
    exact fun hp => .done ⟨hp,fun h => (blank_free A z _ hb h).elim⟩ hs
  | @go i j k d b a path hi hm ha ht ih =>
    have cost := Board.Network.total_spend (u := u) ((w.legs width v hw).w.bound _) ha
    have tail := ih hd (fun _ h => hh _ (List.mem_append_right _ h)) d
    intro e
    rcases i with x | t
    swap
    · exact True.intro
    have ok := permits A z (fun _ h => hh _ (List.mem_append_left _ h))
    have walk : w.Resume width (u.a^u.h) (occurs A z) par s d (Board.Network.total u a) (.inl x) := by
      rcases hm with ⟨hl,rfl | hj⟩
      · exact expand_dest (blank_free A z) hl ok tail
      · rcases j with y | t
        · exact Leg.expand hj.1 ok tail
        · exact hj.1.elim
    exact fun hp => ((walk hp).redirect e).more cost

def turns (u : Dials) := Board.Network.size u*(1+(u.D u.h).step)

theorem potential (v : u.Valid) (w : World X n) (width : ℕ) (hw : 3 ≤ width) {chance : ℕ}
    (hch : 0 < chance) (hsize : 2*(u.count : ℝ) ≤ chance*u.gamma*(u.rate u.h)^2) :
    Nonempty (w.Potential (law u v) chance (turns u) width (u.a^u.h)) := by
  let base := u.a^u.h
  have hb : 0 < base := pow_pos (by have := v.base; omega) _
  let L := w.legs width v hw
  obtain ⟨A,safe,fixed,prom⟩ := Board.Legs.Decoration.exists_decoration L v
  refine ⟨⟨fun x => {z | occurs A z x},?_,?_⟩⟩
  · intro x hx
    exact Board.Legs.Decoration.dense safe fixed v ((w.mid_real width base hw hb x).mpr hx) (.inl hx) hch hsize
  intro x hx z
  obtain ⟨d,hd⟩ := w.shore_real width base hw hb hx
  obtain ⟨s,hs,j,l,hdead,ht,hh⟩ := Board.Legs.Decoration.escape prom z hd
  let par := w.block (width*base) x
  have h := expand A z (par := par) ht hdead hh false rfl
  have one : ∀ y, w.block (width*base) y = par → w.index width base y + base*par = w.block width y := by
    intro y he
    rw [← he,w.parent]; exact Nat.mod_add_div _ _
  have he : L.w.place (.inl x) = w.index width base x := w.at_real width base hw hb x
  refine ⟨s + base*par,fun h => hs (by rw [he]; have := one x rfl; omega),?_⟩
  refine (h.more (Board.Network.total_le u le_rfl)).mono ?_ (fun _ h => h)
  rintro y ⟨hy,ho⟩
  exact ⟨hy,fun hh => (one y hy).symm.trans (congrArg (· + base*par) (ho hh))⟩

end OAI.Geometry.Hirsch.Layer.World

namespace OAI.Geometry.Hirsch.Layer

theorem primary : PrimaryLemma := by
  intro m hm
  obtain ⟨u,b,bits,chance,v,hb,hi,hc,he,hkey,hs,hsize⟩ := Dials.choose m hm
  refine ⟨b,bits,chance,World.turns u,hb,hi,hc,hkey,hs,Board.Naming.Sample u,inferInstance,Board.Naming.law u v,?_⟩
  rw [he]
  exact fun _ _ w width hw => w.potential v width hw hc hsize

end OAI.Geometry.Hirsch.Layer
