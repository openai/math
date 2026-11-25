import OAI.Computability.IntegerMultiplication.Halo.Minor
import OAI.Computability.IntegerMultiplication.Adic.Arrange

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Halo
open Param Scale Echo Cap IntegerMultiplication.Fourier Strip Dims Adic Loom Phase Hook Axon Dusk Cone Grid
open Earth Code
variable (k:ℕ)
noncomputable section
def noir : Adopt (line 2 k) (Series.natural (2^k)) := by
  let L:=line 2 k
  let v : Block 2 k≃Spot (2^k) := (layBit k).trans (localE k)
  refine ⟨v,fun {O} f=>?_⟩
  let d : Spot (2^k) → Spot (2^k) → Prop:=fun i j=>i.val<j.val
  let q:=Series.natural (2^k)
  let W:=q.explore; let H:= L.tab v
  have e : W.Pairwise d := by
    change (List.finRange _).Pairwise _
    apply List.pairwise_iff_getElem.mpr
    intro i j h t b
    simp [d,b]
  have h : H.Pairwise d :=
    List.pairwise_map.mpr ((clean 2 k).imp (by
      intro x y a
      change bold (layBit _ x)<bold (layBit _ y)
      rwa [Axon.bright,Axon.bright]))
  let : Std.Antisymm d := ⟨fun _ _ t g=> by unfold d at *; omega⟩
  let : Std.Irrefl d := ⟨fun _=>Nat.lt_irrefl _⟩
  have t : W=H := by
    apply e.eq_of_mem_iff h
    intro i
    exact ⟨fun _=> (Series.elements ..).mpr ⟨v.symm i,v.apply_symm_apply i⟩,fun _=>q.complete i⟩
  change W.map f=L.tab _
  rw [t]
  exact L.map_tab _ _

-- align amongst logical positions
set_option maxHeartbeats 45000
variable (n:ℕ)
abbrev padN := Adic.field 2 (reach n)
abbrev nilN (_:ℕ) := ([]:Tape)
abbrev altN := Hook.altitude Param.batches chunk border n
variable {n} (h:Season n)
-- batch gives equality
include h
theorem breadth : altN n=ell n := h.batch.2
abbrev tilt := finCongr (congrArg (2^· : ℕ→ℕ) (breadth h))
abbrev core : xy (altN n) (Focn n) ≃ primeV n where
  toFun x:= tilt h ∘ x
  invFun x:= (tilt h).symm ∘ x
  left_inv _x:= funext fun _i=> (tilt h).symm_apply_apply _
  right_inv _x:=funext fun _i=> (tilt h).apply_symm_apply _

def reels {a b:ℕ} (q:a=b): Adopt (Series.natural a) (Series.natural b) where
  cast:=finCongr q
  route _:=by subst b; rfl
abbrev Aeye := (noir (altN n)).thenDo (reels (congrArg (2^·:ℕ→ℕ) (breadth h)))
abbrev Ceye (n:ℕ) := noir (reach n)
abbrev Xeye := Earth.equate (Aeye h) (Focn n)
abbrev Floor (n:ℕ):=primeV n × sucV n
abbrev outline (n:ℕ) := feild nilN padN Focn Param.batches chunk border n
abbrev Psys (n:ℕ): Series (primeV n) := Track (Series.natural _) _
abbrev Csys (n:ℕ): Series (sucV n) := Series.natural _
abbrev Peace (n:ℕ): Series (dayV n) := Series.natural _
abbrev Floorplan (n:ℕ):Series (Floor n):=(Psys n).cart (Csys n)
def alignFloor : Adopt (outline n) (Floorplan n) :=
  let D := ((Adopt.omitL _ : Adopt (outline n) _))
  D.thenDo ((Xeye h).split (Ceye n))

abbrev clause (n:ℕ) := residue nilN padN Focn Param.batches chunk border n
abbrev skirt0 (n :ℕ) := rowL nilN padN Focn Param.batches chunk border n
abbrev transform (v : clause n) : Floor n :=
  (core h (pixel v.2), (Ceye n).cast v.1.2)

theorem floor_eq (v) :
    (alignFloor h).cast v=transform h (skirt0 n v) := by
  refine Prod.ext ?_ rfl
  funext i
  change (Xeye h).cast _ i= _
  rw [installs]
  rfl

-- serialization grouped and flat
abbrev coda (n:ℕ)(a:Farm n):= Dusk.mark ∘ a
abbrev throat (h:Season n)(f:Tri n→ Tree):Tree :=
  stripe (Floorplan n) fun v=> stripe (Peace n) fun z=>f (uX h v.1 v.2 z)
abbrev singlet (h: Season n) (x:Farm n) :=
  throat h (send ∘ coda n x)
abbrev walk (h: Season n): Series (Tri n):= ((Floorplan n).cart (Peace n)).via
  ((Equiv.prodAssoc (primeV n) (sucV n) (dayV n)).trans (prism h).symm)
abbrev flat (h:Season n) (x:Farm n):Tree:=
  stripe (walk h) (send ∘ coda n x)

abbrev dimensions (n:ℕ):=Hook.pos nilN padN Focn Param.batches chunk border n
abbrev harness (x:Farm n): Datum nilN padN Focn Param.batches chunk border Scale.W (T:=dayV) n :=
  fun v z=>x (uX h (transform h v).1 (transform h v).2 z)
theorem plate (x:Farm n):
    stripe (outline n) (fun v:dimensions n=> stripe (Peace n) (fun z=>
      send (Dusk.mark ((harness h x) (skirt0 _ v) z))))=singlet h x := by
  rw [show singlet h x=stripe _ _ from rfl,(alignFloor h).packet]
  -- use extent
  apply congrArg (stripe _)
  funext a
  change _=stripe (Peace n) (fun z=> send (coda n x (uX h ((alignFloor h).cast a).1 ((alignFloor h).cast a).2 z)))
  rw [floor_eq h]
  rfl
end
end Halo

end IntegerMultiplication
end Computability
end OAI
