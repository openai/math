import OAI.Computability.NearSquareRoot.InterchangeNode

/-! # Clearing the endpoint workspace before the first descent -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeFrame

variable {I F : Type} {b : ℕ} [NeZero b]

/-- Perform both short-field swaps and expose the paired field bank. A
recursive solver may now overwrite the entire stream. Its output already
is the parent's final reply in the native byte order. -/
theorem expose (a m : ℕ) (xs : I → Request b) (hb : 2 ≤ b) (hn : 0 < positions a m)
    (digit : F → Tree) [Finite F]
    (ok : ∀ i, Packed digit (xs i)) :
    ∃ v : (i : I) → domain (b:=b) (J:=Fin (positions a m)) (north xs b) (aisle a m xs)
        (south a m xs) (localWidth a m xs) i → Tree,
      Manifest _ (payloadWidth xs) v ∧ (∀ i k, record digit (payloadWidth xs i) (v i k)) ∧
      Rip (regime xs) (fun i => (xs i).rows.count) (payloadWidth xs)
        ((job b).issue ∘ xs) (together (regime xs).header (stackRun (centerRows a m xs b) v)) ∧
      (∀ i, stripe (centerRows a m xs b i) (v i ∘ swapper _ _ _) = (job b).reply (xs i)) := by
  let ord := order a m
  let n := positions a m
  let f := localWidth a m xs
  let t := localTail a m xs
  let P i := (xs i).before
  let G i := (xs i).between
  let B i := (xs i).after_
  let mesh i := expanded ord b 1 (f i) (t i) (P i) (G i) (B i)
  let mid i := axis ord b 1 (f i) (t i) (P i) (G i) (B i)
  let toCenter (i : I) : Adopt (mesh i) (centerRows a m xs b i) := (mid i).view
  let whole i := parent ord b 1 (f i) (t i) (P i) (G i) (B i)
  let eq i := width_eq (ok i).2.1 n
  let canonical i := widthView (b:=b) (P i) (G i) (B i) (eq i).symm
  let home (i : I) : Adopt (mesh i) (xs i).rows := (whole i).thenDo (canonical i)
  let initial i := (xs i).contents ∘ (home i).cast
  let top i := leading (J:=Fin n) b 1 (f i) (t i) (P i) (G i) (B i)
  let low i := trailing (J:=Fin n) b 1 (f i) (t i) (P i) (G i) (B i)
  let pivot i := center (J:=Fin n) b 1 (f i) (t i) (P i) (G i) (B i)
  let ready i := initial i ∘ top i ∘ low i
  let v i := ready i ∘ (toCenter i).cast.symm
  have hv := packed_manifest digit xs ok
  refine ⟨v,hv.shift _,fun i k => (ok i).2.2 _,?_,?_⟩
  · have reach := endpoint_fields_told xs hb n
    obtain ⟨hp,hg,hs⟩ := shapes_told xs fun i => (ok i).1
    have lead := Request.bounded_axis_fleet n hb mesh _ _ _ (fun _ => 1) (payloadWidth xs)
      (fun i => leadingAxis ord b 1 (f i) (t i) (P i) (G i) (B i)) (Regime.fixed (tally 1))
      (hp.append Told.nil) (reach.1.append (hg.append Told.nil)) (reach.1.append hs)
      (fun _ => hn) top (fun i => leading_cast ord b 1 (f i) (t i) (P i) (G i) (B i))
      initial (hv.shift _)
    have trail := Request.bounded_axis_fleet n hb mesh _ _ _ t (payloadWidth xs)
      (fun i => trailingAxis ord b 1 (f i) (t i) (P i) (G i) (B i)) (tail_has xs n)
      (hp.append reach.2) (Told.nil.append (hg.append reach.2)) (Told.nil.append hs)
      (fun i => (tail_lt _ hn).le) low (fun i => trailing_cast ord b 1 (f i) (t i) (P i) (G i) (B i))
      (fun i => initial i ∘ top i) (hv.shift _)
    have run := Fleet.chain lead trail (fun _ => rfl)
    have shape := center_told xs hb (fun i => (ok i).1) n
    have cst := layoutRows_station (b:=b) ord (north xs b) (aisle a m xs) (south a m xs) f
      hb (lane_has xs n) shape.1 shape.2.1 shape.2.2
    have st : Station (regime xs) mesh := by
      unfold Station at *
      simp_rw [(toCenter _).cost]
      exact cst
    have keep := Drive.fetch st.1 ((hv.shift (fun i => (home i).cast)).lives st)
    have both := keep.twice run
    have old : stackRun mesh initial = fun i => stripe (xs i).rows (xs i).contents :=
      funext fun i => ((home i).packet _).symm
    have new : stackRun (centerRows a m xs b) v = stackRun mesh ready := by
      funext i
      change stripe (centerRows a m xs b i) (v i) = _
      rw [(toCenter i).packet]
      exact congrArg (stripe _) (funext fun k => congrArg (ready i) ((toCenter i).cast.symm_apply_apply k))
    have number : (fun i => (mesh i).count) = fun i => (xs i).rows.count :=
      funext fun i => (home i).cost
    change Rip _ (fun i => (mesh i).count) _ (together _ (stackRun mesh initial))
      (together _ (stackRun mesh ready)) at both
    rw [number,old,← new] at both
    exact both
  · intro i
    change stripe _ _ = stripe _ _
    rw [(toCenter i).packet,(home i).packet]
    apply congrArg (stripe _)
    funext k
    apply congrArg ((xs i).contents)
    have central := center_cast ord b 1 (f i) (t i) (P i) (G i) (B i) k
    change (home i).cast (top i (low i ((mid i).view.cast.symm (swapper _ _ _ ((mid i).view.cast k))))) =
      swapper _ _ _ ((home i).cast k)
    rw [← central,(mid i).view.cast.symm_apply_apply]
    have split := parent_cast ord b 1 (f i) (t i) (P i) (G i) (B i) k
    have swap := widthView_swap (b:=b) (P i) (G i) (B i) (eq i).symm ((whole i).cast k)
    exact (congrArg (canonical i).cast split).trans swap

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
