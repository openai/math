import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalEffective

/-! # The selected repair instruction stream on native packed payloads -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Physical

open Interchange StageScript Matrix SwapSpectrum
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Port IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  InterchangeSlots InterchangeSpectralFibre Support RectangleAtlas CommonRegisters Space InterchangeROM

variable {R L V U D B H : Type} [Field R] [Fintype U] [Fintype V]
  [DecidableEq L] [Fintype L] [Fintype B] [Fintype H] {r : B → Rectangle L}
  {a b m : ℕ} [NeZero b] {A : RectangleAtlas r a} {P G S : Tape} {f : ℕ}

abbrev Positions (P G S : Tape) (a m b f : ℕ) := Keys P G S (Fin (a+m+a)) (Block b f)

def flags (u : Positions P G S a m b f) (j : Fin m) : Bool :=
  let s := RepairSchedule.mainSlots a m
  decide ((numerical u (s j)).2 < (numerical u (s j)).1)

def directions (back : Bool) (half : R) (x : Positions P G S a m b f → R) :
    Positions P G S a m b f → R :=
  let axes := (List.finRange m).map (RepairSchedule.mainSlots a m)
  (if back then axes.reverse else axes).foldl
    (fun v j => InterchangeSpectralRequest.advance back half j v) x

def stagePayload (F : Frame A m b) (I J : H → L) (M : Matrix H H R) (t : Spec R V U m) :
    Bank R L (Positions P G S a m b f × D) V → Bank R L (Positions P G S a m b f × D) V :=
  eval (withPayload D (extendLayout P G S (F.layout f))).perm (stageBank r I J t M)

def swapPayload (x : Bank R L (Positions P G S a m b f × D) V) :
    Bank R L (Positions P G S a m b f × D) V := fun w z =>
  x w (swapMain (RepairSchedule.mainSlots a m) z.1,z.2)

/-- A whole packed row moves in one recursive transfer, with its payload index preserved. -/
theorem schedule_payload_of_pull [DecidableEq V] [DecidableEq R] (I J : H → L)
    (g : StageRoute.Layout r (Fin m) (Positions P G S a m b f))
    (pull : ∀ (j : Fin m) (v : L) z, (g.S j v).symm (g.T j v z) = InterchangeSpectralRequest.swapAt (mainRank a j) z)
    (M : Matrix H H R) (hM : (rectangleMatrix (K := R) r).submatrix id J * M *
      (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (t : Spec R V U m) (d : ℕ) (half : R) (hh : 2*half=1) (ht : accepts t d half = true)
    (x : Bank R L (Positions P G S a m b f × D) V) :
    schedule t half (flags ∘ Prod.fst) (lift (directions false half)) (lift (directions true half))
      ((eval (withPayload D g).perm (stageBank r I J t M))^[d]) x = swapPayload x := by
  funext w z i
  let s := RepairSchedule.mainSlots a m
  let k := key s (numerical z.1) z.1.1 z.1.2.2.1 z.1.2.2.2.2
  let u := numerical z.1 ∘ s
  have hs : k u = z.1 := key_self s z.1
  have hp (j : Fin m) (v : L) (y : Address (Fin m) (Fin (b^f))) :
      (g.S j v).symm (g.T j v (k y)) = k (swap j y) :=
    (pull j v (k y)).trans (key_swap s _ _ _ _ y j).symm
  let kp := withPayloadKey k z.2
  have ht' (y : Address (Fin m) (Fin (b^f))) : flags (kp y).1 = addressSign y := by
    funext j
    simp [kp,withPayloadKey,flags,s,k,key,numerical,InterchangeSpectralRequest.key,addressSign]
  have hf := lift_key (directions false half) _ k
    (forward_key s _ _ _ _ half hh (List.finRange m)) z.2
  have hb := lift_key (directions true half) _ k
    (inverse_key s _ _ _ _ half hh (List.finRange m)) z.2
  have h := schedule_on_fibre t d half hh (flags ∘ Prod.fst) _ _ _ kp w
    (fun y => stageBank_iterate r I J t M hM (withPayload D g) kp (withPayload_pull g k z.2 swap hp) y w d)
    hf hb ht' x
  have hout := congrFun (congrFun h i) u
  rw [run_correct _ _ _ hh ht] at hout
  change schedule t half _ _ _ _ x w (k u,z.2) i = x w (k (SwapRepair.swapAll u),z.2) i at hout
  have hz := key_swapAll s (numerical z.1) z.1.1 z.1.2.2.1 z.1.2.2.2.2 u
  change k (SwapRepair.swapAll u) = swapMain s (k u) at hz
  simpa only [hz,hs,swapPayload,Prod.mk.eta,s] using hout

theorem schedule_payload [DecidableEq V] [DecidableEq R] (F : Frame A m b) (I J : H → L)
    (M : Matrix H H R) (hM : (rectangleMatrix (K := R) r).submatrix id J * M *
      (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (t : Spec R V U m) (d : ℕ) (half : R) (hh : 2*half=1) (ht : accepts t d half = true)
    (x : Bank R L (Positions P G S a m b f × D) V) :
    schedule t half (flags ∘ Prod.fst) (lift (directions false half)) (lift (directions true half))
      ((stagePayload F I J M t)^[d]) x = swapPayload x :=
  schedule_payload_of_pull I J (extendLayout P G S (F.layout f))
    (fun j v => F.native_pull j v P G S f) M hM t d half hh ht x

/-- Combining per-leaf tape proofs checks the actual generated command through
its public packet entry point, for arbitrary packed records and background tape. -/
theorem command_payload [DecidableEq V] [DecidableEq R] (F : Frame A m b) (I J : H → L)
    (M : Matrix H H R) (hM : (rectangleMatrix (K := R) r).submatrix id J * M *
      (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (t : Spec R V U m) (d : ℕ) (half : R) (hh : 2*half=1) (ht : accepts t d half = true)
    (wide : Bank R L (Positions P G S a m b f × D) V → List Tree)
    (short : Bank R L (Positions P G S a m b f × D) U → List Tree)
    (n : ℕ) (hw : ∀ x, (wide x).length = n)
    (leaf : Leaf → List Tree → List Tree) (dom : Leaf → List Tree → Prop)
    (charge : Leaf → List Tree → Allowance) (c : Leaf → Cmd) (header : Tree) (env : Env)
    (act : Realizes leaf dom charge c header env)
    (sem : LeafSemantics leaf t half (flags ∘ Prod.fst) (lift (directions false half))
      (lift (directions true half)) (stagePayload F I J M t) wide short)
    (good : LeafDomains dom wide short)
    (x : Bank R L (Positions P G S a m b f × D) V) (deck : Deck) (base : ℕ) (bg : DeckCap base deck) :
    let budget := allowance leaf charge header (steps n d) (wide x)
    BoundedFits env (command c (steps n d)) (pile 0 (packet header (wide x)) deck)
      (pile 0 (packet header (wide (swapPayload x))) deck) budget.time (base+budget.cap) budget.depth := by
  have h := command_bounded act _ _ (ready_steps sem good n hw d x) deck base bg
  dsimp only at h ⊢
  rwa [run_steps sem n hw, schedule_payload F I J M hM t d half hh ht] at h

end InterchangeROMRepair.Physical

end

end NearSquareRoot
end Computability
end OAI
