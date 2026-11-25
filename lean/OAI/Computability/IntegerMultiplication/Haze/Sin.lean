import OAI.Computability.IntegerMultiplication.Haze.Song

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Haze
open Code Loom Strip Strip.Dims Net Net.Tensor Net.Shuttle Net.Walsh Phase Packed Dusk Spindle
open Finset
variable {D : ℕ}
noncomputable section

def icon : PathV D→Bool := fun x=> !x.1.isEmpty
abbrev ix (i : Snow D []) : PathV D := ⟨[],i⟩
theorem lit_s (x : PathV D) :
    (icon x=false→∃ i,x=ix i) ∧ (icon x=true→∃ i,x=emboss i) := by
  obtain ⟨_|⟨a,l⟩,x⟩ := x
  · exact ⟨fun _=>⟨_,rfl⟩,fun h=> Bool.noConfusion (show false=true from h)⟩
  exact ⟨fun h=> Bool.noConfusion (show true=false from h),fun _=> ⟨⟨_,_,x⟩,rfl⟩⟩
def engine_next : PathV D → Option (PathV D)
| ⟨[],_⟩ => Option.none
| ⟨a::l,x⟩=> some (phaseNext (D:=D) ⟨a,l,x⟩)

def daytime : PathV D→ℝ
| ⟨[],_⟩=>1
| ⟨a::l,x⟩=> Haze.step (D:=D) ⟨a,l,x⟩
def chargeV : PathV D→ℝ :=
  fun x => ((x.2.roof.W:ℝ)+1)*acres Motif.sigma D x.1+1
abbrev costK (x : PathV D) := x.2.roof.region.terrain.count

theorem lexer (d : 2 ≤ D) :
    let r := gov d
    Station r (fun i : PathV D=> i.2.roof.region.terrain) :=
  season id d (Regime.self (r:=gov d)) (Dom.base _)
theorem live_t (d : 2 ≤ D) :
    Alive (gov d) costK surplus (engine D).issue := by
  let Y := gov d; let X := PathV D
  have h := lexer d
  have v : Alive Y costK surplus (fun i => i.2.cap i.2.snow) :=
    shelter _ (fun i:X=> Series.natural i.2.lanes) (fun i=> i.2.roof.region.shade) _ h
      (fun i=> by rw [Series.count_natural])
  exact Rip.alivePair (Drive.started h.1) v
theorem budge (d : 2 ≤ D) :
    Rip (gov d) costK surplus (engine D).issue (send ∘ icon) := by
  let t := gov d
  refine Rip.chain (show Rip (gov d) _ _ _ t.header from (Rip.split (live_t d)).1) ?_
  have h0 : t.Has (fun i:PathV D=>i.2.roof.reg) := Regime.self (r:=t)
  have h : t.Has fun i:PathV D=>i.1 := Regime.Has.ez h0 Easy.fst
  have v := h.ez (Easy.listCase (X:=Tally) (Y:=Bool) (f:=fun _=>true) false (Easy.const _))
  have eq : icon (D:=D)=(fun i:PathV D=> List.casesOn (motive:=fun _=>Bool) i.1 false (fun _ _=>true)) := by
    funext i; obtain ⟨_|l,x⟩ := i <;> rfl
  exact Rip.header (lexer d).1 (eq ▸ v)

private theorem quick (d : 2 ≤ D) :
    let r := (gov d).pull ix
    Breeze (daytime ∘ ix) r (costK ∘ ix) (surplus ∘ ix)
      ((engine D).issue ∘ ix) ((engine D).reply ∘ ix) := by
  have H := (Rip.split (live_t d)).2
  have Q : ((engine D).reply ∘ ix) = (fun i:Snow D []=>i.cap i.snow) := by
    funext i
    change stripe _ (fun a=> strip _ (Dusk.mark ∘ runOn _ _ a))= _
    apply congrArg (stripe _)
    funext a
    apply congrArg (strip _)
    funext x
    exact congrArg Dusk.mark (congrFun (nil_r (fun a=>i.snow a x)
      (Walsh.A (gaunt i.roof.region.shade) false)) a)
  rw [Q]
  exact Breeze.launch (H.pull ix) (fun _=> le_rfl)

variable {J W L : Type} [Fintype J] [DecidableEq J] [Fintype W] (d : Guild J W L Motif.sigma)
    (R : Series W)
include d R
theorem dusty :
    let _Q := PathV (dim J)
    let r := gov (d.large.trans' (by decide : 2 ≤ 3)) -- argument below
    let O := engine (dim J)
    Breeze chargeV r costK surplus O.issue O.reply := by
  have t := d.large.trans' (by decide : 2 ≤3)
  let r := gov t
  let O := engine (dim J)
  apply spin (f:=daytime) icon (budge t) engine_next ix emboss lit_s (fun i=>rfl)
    phaseNext (fun i=>by obtain ⟨_,_,g⟩:=i; rfl) (quick _) (by
      have h : (daytime (D:=dim J) ∘ emboss)=Haze.step := by
        funext i; obtain ⟨_,_,x⟩ := i; rfl
      rw [h]; exact song d R)
  · rintro ⟨_|⟨a,l⟩,x⟩ i e
    · contradiction
    injection e with b
    subst i; exact rotate x
  · intro i; unfold chargeV acres
    have z (a : ℕ) : (0:ℝ)≤((dim J:ℝ)^Motif.sigma)^a := by positivity
    have q : 0 ≤ (List.map (fun i:Tally=> ((dim J:ℝ)^Motif.sigma)^i.length) i.1).sum := by
      apply List.sum_nonneg; intro w h; obtain ⟨i,_,rfl⟩:=List.mem_map.mp h; apply z
    positivity
  · rintro ⟨_|⟨a,l⟩,x⟩ e
    · change 1≤(_ :ℝ)*acres _ (dim J) [] + 1
      simp [acres]
    contradiction
  rintro ⟨_|⟨a,l⟩,v⟩ j h
  · contradiction
  injection h with e
  subst j
  let q : Arise (dim J) := ⟨a,l,v⟩
  have S := Haze.wind q
  change _ ∧ costK (phaseNext q) ≤ costK (emboss q) ∧
    surplus (phaseNext q) ≤ surplus (emboss q) ∧ _
  refine ⟨?_,S.record.le, S.sector.le, S.site.le⟩
  change ((v.roof.W:ℝ)+1)* acres Motif.sigma (dim J) (a::l)+1 ≥ _* _ +
    ((((Pal.W (phaseNext q).2.roof):ℝ)+1)*acres Motif.sigma (dim J) l+1)
  rw [S.node,plus_acres]
  change _ ≥ ((v.roof.W:ℝ)+1)*_+(((v.roof.W:ℝ)+1)*_+_)
  linarith

def ascent (p : Tape) (v : Tape) (h g b : ℕ) := plain p v h g b

end
end Haze

end IntegerMultiplication
end Computability
end OAI
