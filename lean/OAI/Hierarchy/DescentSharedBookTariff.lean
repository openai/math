import OAI.Hierarchy.DescentShortBookScan

namespace OAI
/-! # Cost of computing the common host rank chart -/
namespace Hierarchy.DescentSharedBookScan
open DescentFallbackRankRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap : ℕ}

private theorem guard (B : Chart) (j : Fin D) (action : Expr) (xs : List (Fin D)) :
    (unlessSeen (side B j) action (xs.map (side B))).work=action.work+30*xs.length := by
  induction xs with
  | nil=>simp [unlessSeen]
  | cons i xs ih=>
    change 14+14+1+(unlessSeen (side B j) action (xs.map (side B))).work+1=_
    rw [ih,List.length_cons]
    omega

private theorem one (B : Chart) (limit : ℕ) (z : Fin D×Fin cap) (which : Bool) :
    let query:=if which then some (slot B,ctl B .destShape) else none
    (testSlot (side B) (shapes B) limit query z).work≤2000+30*D := by
  dsimp only
  have presses : (prior z.1).length≤D:=by
    simpa [prior,Finset.length_toList] using (Finset.card_filter_le (s:=Finset.univ) (fun i : Fin D=>i<z.1))
  have action (q : Option (Expr×Expr)) : (testSlot (side B) (shapes B) limit q z).work=
      14+1+1+((shapes B z).work+1+1+(pass (side B z.1) (shapes B z) q).work+1+30*(prior z.1).length)+1 := by
    unfold testSlot
    change 14+1+1+(unlessSeen _ _ _).work+1=_
    rw [guard]
    rfl
  have sh : (shapes B z).work=67 := rfl
  have ps : (pass (side B z.1) (shapes B z) (some (slot B,ctl B .destShape))).work≤1500 := by
    norm_num [DescentFallbackRankRAM.pass, DescentPairedKeyComparison.earlier, DescentPairedKeyComparison.tail,
      DescentPairedKeyComparison.high, Expr.work, sh, show (side B z.1).work = 14 from rfl,
      show (slot B).work = 22 from rfl, show (ctl B .destShape).work = 7 from rfl]
  have no : (pass (side B z.1) (shapes B z) none).work=1 := rfl
  cases which <;> simp only [Bool.false_eq_true,ite_false,ite_true,action,sh,no] <;> omega

private theorem invoice (B : Chart) (D cap H : ℕ) (which : Bool) :
    let q:=if which then some (slot B,ctl B .destShape) else none
    (measure (side B) (shapes B) H (Δ:=D) (cap:=cap) q).work≤1+(D*cap)*(2001+30*D) := by
  intro q
  have subtotal (xs : List (Fin D×Fin cap)) :
      (foldSum (xs.map (testSlot (side B) (shapes B) H q))).work≤1+xs.length*(2001+30*D) := by
    induction xs with
    | nil=>simp [foldSum,Expr.work]
    | cons z zs ih=>
      have each : (testSlot (side B) (shapes B) H q z).work≤2000+30*D:=one B H z which
      change (testSlot (side B) (shapes B) H q z).work+
        (foldSum (zs.map (testSlot (side B) (shapes B) H q))).work+1≤_
      rw [List.length_cons,Nat.succ_mul]
      omega
  simpa only [DescentFallbackRankRAM.measure,Finset.length_toList,Finset.card_univ,Fintype.card_prod,
    Fintype.card_fin] using subtotal Finset.univ.toList

theorem shared_work (B : Chart) (D cap H d : ℕ) :
    (record B H D cap d).work≤10000*(D+1)^2*(cap+1) := by
  let score:=expr B H D cap
  have all :=invoice B D cap H false
  have prior:=invoice B D cap H true
  simp only [Bool.false_eq_true,ite_false,ite_true] at all prior
  have ew : score.work≤39+2*((D*cap)*(2001+30*D)) := by
    change 7+1+(measure (side B) (shapes B) H (Δ:=D) (cap:=cap) none).work+
      (22+1+1+(measure (side B) (shapes B) H (Δ:=D) (cap:=cap) (some (slot B,ctl B .destShape))).work+1)+1≤_
    omega
  change score.work+1+score.work+1+1≤_
  calc
    _≤2*(39+2*((D*cap)*(2001+30*D)))+3:=by omega
    _≤_:=by ring_nf;omega

theorem shared_cheap (B : Chart) (D cap H d w out rows : ℕ) :
    CheapCode (body B H D cap w d out rows) := @scan_cheap _ _ _ _

end
end Hierarchy.DescentSharedBookScan

end OAI
