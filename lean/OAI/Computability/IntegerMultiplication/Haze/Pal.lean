import OAI.Computability.IntegerMultiplication.Haze.Algebra
import OAI.Computability.IntegerMultiplication.Strip.Steps

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Haze
open Code Loom Strip Strip.Dims Net Net.Shuttle Net.Walsh Net.Tensor Phase Packed Dusk Spindle
open Finset Matrix
noncomputable section
abbrev Plan := List Tally
-- Hull descriptor:
-- Estate already handles safe etc but has range missing tops/foot term for volume zero. add K<=global in plan
variable (D : ℕ)
abbrev census := Code.volume D
structure Pal (D : ℕ) (l : Plan) where
  region : Estate D (Code.volume D l)
  reaches : width region.tops region.foot ≤ region.metres
variable {D}
namespace Pal
variable {l : Plan}
def reg (e : Pal D l) :=
  let k := e.region
  (l,tally k.tops,tally k.foot,tally k.shade,shape k.sunrise,shape k.sunset)
-- unit tags p
private theorem cardsize (v : Plan) (h : 2 ≤ D) :
    size v ≤ 4*Code.volume D v +1 := by
  have q : ∀ i:ℕ,i+1 ≤ D^i := by
    intro i
    induction i with
    | zero => simp
    | succ j ih => rw [pow_succ]; nlinarith

  induction v with
  | nil => simp -- ≤ refl defeq
  | cons a v ih =>
    rw [size_cons,size_tally,Spindle.plus]
    specialize q a.length; omega

theorem permit_s (p : Pal D l) (h : 2 ≤ D) :
    size p.reg ≤ (4*base+30)*(p.region.metres+1) := by
  let z := p.region
  have q := z.range
  unfold reg
  let h0 := z.tops
  let e : 1 ≤ width z.tops z.foot := by unfold width; omega
  have x := z.shade
  have t := Stair.entry_size (p:=base) z.sunrise (fun a h=>((z.rays.1 _ h)).2)
  have u := Stair.entry_size (p:=base) z.sunset (fun a h=>((z.rays.2 _ h)).2)
  have L := cardsize l h
  have f := Nat.le_mul_of_pos_right (census D l) e
  have g := Nat.mul_le_mul_left (2*base+2)
    (show z.sunrise.length+z.sunset.length ≤ z.metres from by omega)
  have hs : width z.tops z.foot≤z.metres := p.reaches
  unfold width at *
  rw [size_prod,size_prod,size_prod,size_prod,size_prod,size_tally,size_tally,size_tally,
    tally_length,tally_length,tally_length]
  -- p.region let
  change size l + (2*z.tops+1 +(2*z.foot+1+(2*z.shade+1+(size _ + size _ + 1)+1)+1)+1)+1 ≤ _
  change census D l ≤ _ at f
  simp only [Nat.mul_add,Nat.add_mul,census] at *
  unfold z at * -- z isn't let?
  simp only [Nat.mul_assoc] at *
  omega

abbrev H (p : Pal D l) := p.region.tops
abbrev G (p : Pal D l) := p.region.foot
abbrev P (p : Pal D l) := p.region.sunrise
abbrev V (p : Pal D l) := p.region.sunset
abbrev W (p : Pal D l) := width p.H p.G

private theorem green_a {a n} (h : a∈Adic.field 2 n) : 2≤a∧a≤base := by
  induction n with
  | zero => cases h
  | succ i ih =>
    rcases List.mem_cons.mp h with r|r
    · subst a; exact ⟨le_rfl,base_large.le⟩
    exact ih r

variable {a:Tally}
def runway (p : Pal D (a::l)) : Estate D (D^a.length) :=
  let x := p.region
  let q := dust p.H p.G (census D l)
  { metres := x.metres
    shade := x.shade
    tops := p.H
    foot := p.G
    sunrise := p.P
    sunset := q++p.V
    radix := by intro a h; have g : a∈p.P++p.V ∨ a∈q := by simp at h ⊢; tauto
                exact g.elim (fun h=>p.region.radix _ h) green_a
    range := by
      have m := p.region.range
      simp only [Spindle.plus,Nat.add_mul] at m
      simpa [q,dust, census,Nat.add_left_comm,Nat.add_assoc,Nat.add_comm] using m
    okay := safe_r (f:=Code.volume D (a::l)) (Nat.le_add_right ..) x.okay}
def hangar (p : Pal D (a::l)) : Pal D l :=
  let x := p.region
  let q := dust p.H p.G (D^a.length)
  { region := {
      metres := x.metres
      shade := x.shade
      tops := p.H
      foot := p.G
      sunrise := p.P++q
      sunset := p.V
      radix := by intro a h; have g : a∈p.P++p.V ∨ a∈q := by simp at h ⊢; tauto
                  exact g.elim (fun h=>p.region.radix _ h) green_a
      range := by
        have m := p.region.range
        simp only [Spindle.plus,Nat.add_mul] at m
        simpa [q,dust, census,Nat.add_left_comm,Nat.add_assoc,Nat.add_comm] using m
      okay := safe_r (Nat.le_add_left ..) x.okay }
    reaches := p.reaches }

-- Regime reads all attributes
variable {I : Type} {r : Regime I}
variable (h : I→Plan) (t : (i:I)→ Pal D (h i))
abbrev route_ i := send (t i).reg
variable (u : r.Small (route_ h t))
include u
theorem receipt :
    r.Has h ∧
      r.Has (tally ∘ (fun i=>(t i).H)) ∧
      r.Has (tally ∘ (fun i=>(t i).G)) ∧
      r.Has (tally ∘ (fun i=>(t i).region.shade)) ∧
      Told r (fun i=>(t i).P) ∧ Told r (fun i=>(t i).V) := by
  have U : r.Has (fun i=> (t i).reg) := u
  have v := U.ez Easy.snd; have w := v.ez Easy.snd
  have z := w.ez Easy.snd; have y := z.ez Easy.snd
  exact ⟨U.ez Easy.fst,v.ez Easy.fst,w.ez Easy.fst,z.ez Easy.fst,
    ⟨fun i a h=>((t i).region.rays.1 a h).1,y.ez Easy.fst⟩,
    ⟨fun i a h=>((t i).region.rays.2 a h).1,y.ez Easy.snd⟩⟩

omit u in
theorem bsize (g : Dom r.scale (fun i=>(t i).region.metres)) :
    Dom r.scale (Code.volume D ∘ h) := by
  refine g.mono fun i=> le_trans (Nat.le_mul_of_pos_right _ (?_ : 0<width (t i).H (t i).G))
    (by have z := (t i).region.range; change Code.volume D (h i)*width (t i).region.tops (t i).region.foot ≤ _; omega)
  unfold width; omega

theorem station (g : Dom r.scale (fun i=>(t i).region.metres)) (d : 2 ≤ D) :
    Station r (fun i=>(t i).region.terrain) := by
  obtain ⟨a,b,c,_,p,v⟩ := receipt h t u
  have f := Bounds.wall d a (bsize h t g)
  let z := census D ∘ h
  have y := (controlFiber (fun i=>(t i).H) (fun i=>(t i).G) z b c f).1
  have S := Adic.terminal (p:=2) (by decide) _ y
  let e i := haul (t i).H (t i).G (z i)
  have s := p.station.product (S.product v.station)
  have t' (i) := ((Adopt.same (layout (t i).P)).split ((e i).split (Adopt.same (layout (t i).V)))).cost
  change Station _ (fun i=> ((layout (t i).P).cart ((levels (t i).H (t i).G (z i)).cart (layout (t i).V))))
  unfold Station
  simp only -- beta
  simp_rw [t']
  exact s

end Pal
end
end Haze

end IntegerMultiplication
end Computability
end OAI
