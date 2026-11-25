import OAI.Computability.IntegerMultiplication.Haze.Pal

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Haze
open Code Loom Strip Strip.Dims Net Net.Tensor Net.Shuttle Net.Walsh Phase Packed Dusk Spindle
open Finset Matrix
variable (D : ℕ)
structure Snow (l : Plan) where
  roof : Pal D l
  lanes : ℕ -- spectrum count
  snow : roof.region.keys → Fin lanes→ Grain roof.region.shade

abbrev PathV := Sigma (Snow D)
noncomputable section
variable {D} {l : Plan}
namespace Snow
def cap {l : Plan} (x : Snow D l) (z : x.roof.region.keys → Fin x.lanes → Grain x.roof.region.shade) :=
  stripe x.roof.region.terrain (fun a=> strip (Series.natural _) (Dusk.mark ∘ z a))
end Snow

def engine (D) : Job (PathV D) where
  issue x := Tree.fork (send x.2.roof.reg) (x.2.cap x.2.snow)
  reply x := x.2.cap (runOn (pointed false) x.2.snow)

abbrev Arise (D) := Σ a:Tally, Σ l:Plan,Snow D (a::l)
def emboss : Arise D → PathV D := fun ⟨a,l,g⟩=>⟨a::l,g⟩
def descend {a l} (x : Snow D (a::l)) : Snow D l :=
  let p := x.roof
  let B := D^a.length
  let T := census D l
  let P := p.P; let V:=p.V; let h:=p.H; let g:=p.G
  let m := hatch P V h g B T
  let n := send2 P V h g B T
  ⟨p.hangar,x.lanes,(runOn (liftA (Walsh.A (gaunt p.region.shade) false)) (x.snow ∘ m.cast)) ∘ n.cast.symm⟩

def phaseNext : Arise D → PathV D := fun ⟨_,_,g⟩=>⟨_,descend g⟩

theorem rotate {a l} (x : Snow D (a::l)) : (engine D).reply ⟨l,descend x⟩ = (engine D).reply ⟨_,x⟩ := by
  let p := x.roof
  let Q := p.hangar
  let m := hatch p.P p.V p.H p.G (D^a.length) (census D l)
  let n := send2 p.P p.V p.H p.G (D^a.length) (census D l)
  let z := x.snow
  let s := (descend x).snow
  let R := Series.natural x.lanes
  change Snow.cap (descend x) (runOn (pointed false) s) = Snow.cap x _
  change stripe _ (fun i=> strip R _) = stripe _ (fun i=> strip R _)
  erw [n.packet,m.packet]
  apply congrArg (stripe _)
  funext i
  apply congrArg (strip R)
  funext v
  let A := Walsh.A (gaunt x.roof.region.shade) false
  let y := fun i=> x.snow i v
  suffices e : spectrum p.H p.G (D^a.length + census D l) A p.P p.V y (m.cast i) =
      spectrum p.H p.G (census D l) A _ _ (fun i=> (descend x).snow i v) (n.cast i) by
    exact congrArg Dusk.mark e.symm
  calc
    _ = liftB A (liftA A (y ∘ m.cast)) i := mosaic A y i
    _ = _ := (framed_r (liftA A (y ∘ m.cast)) A i).symm

variable {I : Type} {r : Regime I}
abbrev gov (h : 2 ≤ D) : Regime (PathV D) where
  scale x := x.2.roof.region.metres
  header x := send x.2.roof.reg
  gauge := ⟨1,4*base+30,fun i=> by change Code.size _≤_; rw [pow_one]; exact (i.2.roof.permit_s h)⟩
abbrev regime_ (Y : I→PathV D) := r.Has fun i=> (Y i).2.roof.reg
variable (Y : I→PathV D) (d : 2 ≤ D)
abbrev bank i := (Y i).2.roof.region.terrain
abbrev school_ i := (Y i).2.roof.region.keys
abbrev surplus (x : PathV D) := x.2.lanes*(x.2.roof.region.shade+1)
theorem season (d : 2 ≤ D) (f : regime_ Y (r:=r)) (h : Dom r.scale (fun i => (Y i).2.roof.region.metres)) :
    Station r (bank Y) := Pal.station (Sigma.fst ∘ Y) _ f h d

structure landing (x y : PathV D) where
  site : y.2.roof.region.metres=x.2.roof.region.metres
  node : y.2.roof.W=x.2.roof.W
  record : y.2.roof.region.terrain.count=x.2.roof.region.terrain.count
  sector : surplus y=surplus x

theorem wind (x : Arise D) : landing (emboss x) (phaseNext x) := by
  rcases x with ⟨a,l,x⟩
  refine ⟨rfl,rfl,?_,rfl⟩
  let p := x.roof; let q := D^a.length; let t := census D l
  exact (send2 p.P p.V p.H p.G q t).cost.symm.trans (hatch p.P p.V p.H p.G q t).cost

end
end Haze

end IntegerMultiplication
end Computability
end OAI
