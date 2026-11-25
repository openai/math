import OAI.Computability.IntegerMultiplication.Wave.Local

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Wave
open Param Scale Halo Strip Code Dims Adic Cap Loom Staff Brief Carry Echo Well Moira Bureau
variable {I:Type}(n:I→ℕ)(h:∀i,Season (n i))(a:(i:I)→Direction (n i))
noncomputable section
abbrev Signa(i:I)(x:α n a i):Tree:=send (markNum (X0 n a true) (countK n a) i x)
theorem imprint (x:Sigma (α n a)):
    Bits.value (markNum (X0 n a true) (countK n a) x.1 x.2)=((X0 n a true x.1).index x.2).val := by
  rw [markNum,Bits.value_short, Nat.mod_eq_of_lt] -- args
  rw [← shadow_ n a]
  exact Fin.isLt _
include h
abbrev Evidence := Strip.Trace (joltB n a) (X0 n a true) (Signa n a)
theorem evidence: Evidence n a :=
  let g:=guideQ n a; let p:=digitQ n a
  marks _ _ (shadow_ n a) (status_ n h a g p)
abbrev Packr := PiScale n a (Signa n a) (evidence n h a)
abbrev sZ(i:I):=modulus (n i) (a i)
abbrev rLabel (i:I)(x:α n a i):= wheel (criterion (n i)) (a i) (modulus (n i)) x
abbrev offset (i:I)(x:α n a i)(v:Bool):ℕ:=
  (bif v then Atoll.debt (sZ n a i) (rLabel n a i x) else rLabel n a i x)%(sZ n a i)
abbrev Ticket:= Tally×Tally
abbrev receipt (v:Bool)(i:I)(x:α n a i):Ticket := (Code.tally (sZ n a i),Code.tally (offset n a i x v))
abbrev Per(x:Sigma (α n a)):= Pprice n a x.1
private theorem binary_r {m:Sigma (α n a)→ℕ} (H:Figure (Packr n h a) m)
    (t:∀ x,(m x:ℝ)≤ Per n a x):
    Carries (Per n a) (Packr n h a).header (fun x=>send (Code.tally (m x))) := by
  obtain ⟨c,e,u⟩:=H
  have V:= Regime.Small.cooked (r:=Packr n h a) (a:=fun i=>send (c i))
    (show Regime.ripe (r:=Packr n h a) (Per n a) from ⟨fun x=>priceP n h a x.1,fun k=>by
      obtain ⟨j,v⟩:=(per_cost n h a).2 k; exact ⟨j,fun i=> v i.1⟩⟩) e
  have D:= rice.on c
  simp only [u] at D
  obtain ⟨j,U⟩:= V.out
  refine V.sequence ⟨V.budget,_,D,j+2,fun i=>?_⟩
  specialize U i; change (size (c i):ℝ)≤_ at U
  specialize t i; push_cast; linarith [V.budget i]

include h
theorem cash (v:Bool):
    Carries (Per n a) (Packr n h a).header (fun x=> send (receipt n a v x.1 x.2)) := by
  let d:=joltB n a
  let c:=Packr n h a
  let p:= fun i:Sigma (α n a)=>i.1
  let g:=guideQ n a
  let V:=digitQ n a
  have w: Figure c (fun i=> ((X0 n a true i.1).index i.2).val) :=
    ⟨_,(onboard_hat (Signa n a) (evidence n h a).meter),imprint n a⟩
  have E:= driver n a (Signa n a) (evidence n h a) V g h (symB n a) (joltQ n a) (symbolV n h a) w
  have Y:Figure c (sZ n a ∘ p) := by
    obtain ⟨x,e,t⟩ := g.size_ n V
    exact ⟨x ∘ p,onboard_small (Signa n a) _ (send ∘ x) e,fun i=> t i.1⟩
  have H : Figure c (fun i=> offset n a i.1 i.2 v):= by
    cases v
    · exact E.modded Y
    exact (Y.subtracted (E.modded Y)).modded Y
  have M (i:I) : (sZ n a i:ℝ) ≤ Pprice n a i:=
    (show (sZ n a i:ℝ)≤ L0 n a i by exact_mod_cast Echo.pitch (h i) _).trans (costS n h a i)
  exact (binary_r n h a Y (fun x=>M x.1)).twice (binary_r n h a H (fun x=>
    (show (offset n a x.1 x.2 v:ℝ) ≤ sZ n a x.1 by exact_mod_cast
      (Nat.mod_lt _ (Nat.pos_of_neZero _)).le).trans (M x.1)))

variable {r:Regime I}(T:Origin n r)(A:Realizes r (fun i=> (a i).val))
include T A
variable {p:I→Tree}(U:close n p)
include U
theorem issue (v:Bool):
    Mix n r p (stackRun (X0 n a true) (fun i p=>send (receipt n a v i p))) := by
  let s:=X0 n a true
  let N(i:I):=(s i).count
  have q:=evidence n h a
  obtain ⟨k,l⟩ := Rip.coalesce (s:=X0 n a true) (fun i _=> (joltB n a).header i) (Signa n a)
    (clones q.valid (fun _=>le_refl _) _ Regime.self) q.offer
  let d i (x:α n a i):=(Packr n h a).header ⟨i,x⟩
  change Carries _ _ (stackRun s d) at l
  obtain ⟨c,x⟩:= (per_cost n h a).2 k
  have L : ∀ i, mass (joltB n a) N (fun _=>0) k i ≤ c * token n i := fun i=>by
    specialize x i; unfold mass; push_cast at *; rw [zero_add,← allot n h a i]
    change _≤ (c:ℝ)*(↑(N i)*Pprice n a i)
    rw [mul_left_comm]; gcongr
  have S:= Well.start T U (assembly n a T A)
  apply (S.chain (l.times (chargep n) c L)).chain
  have E:=liftoff s d (fun i p=>send (receipt n a v i p)) (Pprice n a) (cash n h a v)
  exact E.times (chargep n) 2 (fun i=>by
    change ((X0 n a true i).count:ℝ)*Pprice n a i+1≤_
    rw [allot n h a]
    push_cast; linarith [chargep n i])

end
end Wave

end IntegerMultiplication
end Computability
end OAI
