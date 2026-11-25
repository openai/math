import OAI.Hierarchy.DescentPackedFlowReturn
import OAI.Hierarchy.DescentPackedFlowRAM

namespace OAI
/-! # Publish both true endpoint contributions in every packed directed port word -/
namespace Hierarchy.DescentPackedFlowPair
open DescentSIMDLookup DescentPackedColony DescentPackedFlowReturn ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {D H J M r b w : ℕ}

def add (x y : Cell (b*r)) : Cell (b*r) :=
  encode b r (fun j=>(encode b r).symm x j+(encode b r).symm y j)

private theorem zeroE (b r : ℕ) : encode b r (fun _=>0)=0 := by
  apply Fin.ext
  simp [encode]

private theorem digits_zero (b r : ℕ) : (encode b r).symm 0=fun _=>0 := by
  rw [←zeroE b r,Equiv.symm_apply_apply]

theorem add_zero : add (0:Cell (b*r)) 0=0 := by simp [add,digits_zero,zeroE]

def gather (C : Index) (P : Ports D) (bank : Fin D→Bank) (T : DescentPackedZip.Tables)
    (H : ℕ) (i : Fin D) (acc : Expr) (j : Fin D) :=
  T.read acc (gated C P (bank j) H i j)

def expr (C : Index) (P : Ports D) (bank : Fin D→Bank) (T : DescentPackedZip.Tables)
    (H : ℕ) (i : Fin D) :=
  (List.finRange D).foldl (gather C P bank T H i) (.lookup (bank i) .row)

def paid (next : Fin H→Fin D→Option (Fin H)) (X : Fin H→Fin J→Fin D→Fin r→ℕ)
    (v : Fin H) (g : Fin J) (i : Fin D) (x : Fin r) :=
  X v g i x+∑j : Fin D,(back next v i j).elim 0 (fun u=>X u g j x)

theorem paid_at (next : Fin H→Fin D→Option (Fin H)) (X : Fin H→Fin J→Fin D→Fin r→ℕ)
    (v u : Fin H) (g : Fin J) (i j : Fin D) (x : Fin r)
    (forward : next v i=some u) (reverse : next u j=some v)
    (once : ∀t,next u t=some v→t=j) :
    paid next X v g i x=X v g i x+X u g j x := by
  unfold paid
  congr 1
  rw [Finset.sum_eq_single j]
  · simp [back,forward,reverse]
  · intro s _ other
    have miss : next u s≠some v:=fun e=>other (once s e)
    simp [back,forward,miss]
  · simp

private theorem fold_add (qs : List (Fin D)) (f : Fin D→Cell (b*r)) (acc : Cell (b*r)) (x : Fin r) :
    (encode b r).symm (qs.foldl (fun n j=>add n (f j)) acc) x =
      (encode b r).symm acc x+(qs.map (fun j=>(encode b r).symm (f j) x)).sum := by
  induction qs generalizing acc with
  | nil=>simp
  | cons j qs ih =>
    rw [List.foldl_cons, ih (add acc (f j))]
    simp only [List.map_cons, List.sum_cons, add, Equiv.symm_apply_apply, add_assoc]

theorem merge (next : Fin H→Fin D→Option (Fin H)) (X : Fin H→Fin J→Fin D→Fin r→ℕ)
    (v : Fin H) (g : Fin J) (i : Fin D) :
    let packed (t : Fin H) (j : Fin D):=encode b r (fun x=>(X t g j x:Cell b))
    (List.finRange D).foldl (fun acc j=>add acc ((back next v i j).elim 0 (fun t=>packed t j))) (packed v i)=
      encode b r (fun x=>(paid next X v g i x:Cell b)) := by
  intro packed
  apply (encode b r).symm.injective
  funext x
  rw [Equiv.symm_apply_apply,fold_add]
  have one (j : Fin D) : (encode b r).symm ((back next v i j).elim 0 (fun t=>packed t j)) x=
      (((back next v i j).elim 0 (fun t=>X t g j x):ℕ):Cell b) := by
    cases old:back next v i j <;> simp [packed,digits_zero]
  simp only [one,packed,Equiv.symm_apply_apply,paid,Nat.cast_add,Nat.cast_sum]
  congr 1

theorem native (C : Index) (P : Ports D) (bank : Fin D→Bank) (T : DescentPackedZip.Tables)
    (next : Fin H→Fin D→Option (Fin H)) (X : Fin H→Fin J→Fin D→Fin r→ℕ)
    (out : ℕ) (i : Fin D) (m : Memory w) (header : Header C out m D H J M)
    (fit : ∀j,Accessible P (bank j) H J M w out) (old : Mounted P next m J M)
    (rows : ∀j,Reads (bank j) (fun v g=>encode b r (fun x=>(X v g j x:Cell b))) M m)
    (zip : WordRoom T (b*r) (b*r) M w out) (fixed : DescentPackedZip.Static T (add (b:=b) (r:=r)) M m)
    (ends : out+H*chunks J M<2^w) :
    let e:=expr C P bank T H i
    let dst:=image out (H*chunks J M) e m
    (scan w out (H*chunks J M) e).Exec m dst (4+H*chunks J M*(2*e.work+4)) ∧
      (∀p : Row H J M,dst (out+(row H J M p).val)=
        ((data (fun v g=>encode b r (fun x=>(paid next X v g i x:Cell b))) p).val:Word w)) ∧
      CheapCode (scan w out (H*chunks J M) e) := by
  intro e dst
  let pk (v : Fin H) (g : Fin J) (j : Fin D):=encode b r (fun x=>(X v g j x:Cell b))
  have iter (qs : List (Fin D)) (u : Expr) (acc : Fin H→Fin J→Cell (b*r)) (ok : u.Fits w out)
      (real : DescentPackedZip.Source u acc M m) :
      (qs.foldl (gather C P bank T H i) u).Fits w out ∧
        DescentPackedZip.Source (qs.foldl (gather C P bank T H i) u)
        (fun v g=>qs.foldl (fun a j=>add a ((back next v i j).elim 0 (fun t=>pk t g j))) (acc v g)) M m := by
    induction qs generalizing u acc with
    | nil=>exact ⟨ok,real⟩
    | cons j qs ih=>
      have valid:=safe C P (bank j) out m i j header (fit j)
      have one:=source C P (bank j) out next i j m header (fit j) old (fun v g=>pk v g j) (rows j)
      exact ih _ _ (zip.safe _ _ ok valid) (DescentPackedZip.read_data _ _ _ out (zip.issue _ _ ok valid)
        _ add_zero m fixed _ _ real one)
  have read:=DescentPackedZip.source_column (bank i) out (fit i).source m _ (fit i).srcRoom (rows i)
  obtain ⟨fits,word⟩:=iter (List.finRange D) (.lookup (bank i) .row) (fun v g=>pk v g i)
    ⟨(fit i).source,trivial⟩ read
  have values : (fun (v : Fin H) (g : Fin J) => (List.finRange D).foldl
      (fun a j=>add a ((back next v i j).elim 0 (fun t=>pk t g j))) (pk v g i)) =
      (fun v g=>encode b r (fun x=>(paid next X v g i x:Cell b))) := by
    funext v g
    exact merge (b:=b) next X v g i
  have output : DescentPackedZip.Source e
      (fun v g=>encode b r (fun x=>(paid next X v g i x:Cell b))) M m := by
    rw [←values]
    exact word
  refine ⟨scan_exec _ _ _ _ fits ends,?_,@scan_cheap _ _ _ _⟩
  intro p
  exact (ProtocolRAMGeneratedWrite.read_image out (H*chunks J M) e m (row H J M p)).trans (output p)

theorem cost (C : Index) (P : Ports D) (bank : Fin D→Bank) (T : DescentPackedZip.Tables) (H : ℕ) (i : Fin D) :
    (expr C P bank T H i).work≤7+121*D := by
  have bound (qs : List (Fin D)) (u : Expr) :
      (qs.foldl (gather C P bank T H i) u).work≤u.work+121*qs.length := by
    induction qs generalizing u with
    | nil=>simp
    | cons j qs ih=>
      have step:=ih (gather C P bank T H i u j)
      have nextWork : (gather C P bank T H i u j).work =
          u.work + (gated C P (bank j) H i j).work + 11 :=
        DescentPackedZip.work T u (gated C P (bank j) H i j)
      have count:=DescentPackedFlowReturn.cost C P (bank j) (H:=H) i j
      simp only [List.foldl_cons,List.length_cons]
      omega
  simpa [expr,Expr.work] using bound (List.finRange D) (.lookup (bank i) .row)

end
end Hierarchy.DescentPackedFlowPair

end OAI
