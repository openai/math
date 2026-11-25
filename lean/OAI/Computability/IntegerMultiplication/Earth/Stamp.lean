import OAI.Computability.IntegerMultiplication.Earth.Charge

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Earth
open Code Loom Strip Strip.Dims Net Net.Tensor Net.Walsh Phase Packed Haze Dusk Adic
open Matrix Finset
noncomputable section
private def each {S T} (s : Series S) (t : Series T) (e : Adopt s t) :
    (n:ℕ) → Adopt (Track s n) (Track t n)
| 0 => (sealZero _).thenDo (sealZero _).back
| n+1 => ((Loom.step s n).thenDo (e.split (each s t e n))).thenDo
    (Loom.step t n).back
private theorem per {A B} (s : Series A) (t : Series B) (e : Adopt s t)
    (n : ℕ) (x : Fin n → A) :
    (each s t e n).cast x=e.cast ∘ x := by
  induction n with
  | zero => ext i; exact i.elim0
  | succ n ih =>
    let a := Loom.join.symm x |>.2
    change Loom.join (_, (each s t e n).cast a)=_
    rw [ih]
    funext i
    refine Fin.cases ?_ (fun i=>?_) i
    · rfl
    exact Loom.tail_j .. -- target mismatch tail_j yields value fin tail defeq

variable {P V:Tape} {K N:ℕ}
abbrev fieldK p v K n := Base p v (Fin n → Block 2 K)
abbrev rangeK p v K n := Phase.order p v (Track (line 2 K) n)
def connector (P V:Tape) (n) (j : Fin K) :
    Adopt (plain P V j.val (K-j.val-1) n)
      (rangeK P V K n) :=
  (Adopt.same _).split ((each _ _ (letter j) n).split (Adopt.same _))
@[simp] theorem contract (j : Fin K) (x : Base P V (Screen j.val (K-j.val-1) (Fin N))) :
    (connector P V N j).cast x = (x.1,(letter j).cast ∘ x.2.1,x.2.2) := by
  change (x.1,(each _ _ _ _).cast _,x.2.2)=_
  rw [per]

abbrev Duo (N K : ℕ) := Fin N × Fin K
/-- row-major address bits -/
def file (P V:Tape) (K n) : Lens (fieldK P V K n) (Addr (Duo n K)) (Pin P × Pin V) where
  toFun x := (fun i=> layBit K (x.2.1 i.1) i.2,x.1,x.2.2)
  invFun x := (x.2.1,(fun i=> (layBit K).symm (fun j=>x.1 (i,j))),x.2.2)
  left_inv x := by simp
  right_inv x := by simp
def spray (j : Fin K) (n : ℕ) := (connector P V n j).cast.symm.trans (target ..)
def route (j : Fin K) (N) : Fin N ↪ Duo N K := ⟨fun i=>(i,j), fun _ _ h=>Prod.ext_iff.mp h |>.1⟩
theorem exposed (j : Fin K) :
    Expose (file P V K N) (spray (P:=P) (V:=V) j N) (route j N) := by
  let u := connector P V N j
  let n := K-j.val-1
  let f := file P V K N
  let a := spray (P:=P) (V:=V) j N
  let q := route j N
  have e x : a (u.cast x) = target P V _ _ (Fin N) x := by
    change target _ _ _ _ _ (u.cast.symm (u.cast x)) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨fun i=>?_,fun i l=>?_⟩
  · obtain ⟨i,rfl⟩ := u.cast.surjective i
    change (a _).1=_
    rw [e,contract]
    funext k
    exact (step_q j _).symm
  have sw (u v) : (u,v)∉ Finset.univ.map q ↔ v≠j := by
    simp [q,route,Prod.ext_iff,eq_comm]; aesop
  obtain ⟨i,rfl⟩ := u.cast.surjective i
  obtain ⟨l,rfl⟩ := u.cast.surjective l
  change (a _).2=(a _).2 ↔ _ ∧ _
  rw [e,e,contract,contract]
  obtain ⟨i,x,l_i⟩ := i
  obtain ⟨p,y,l_j⟩ := l
  change (i,(fun i=> (pulse (x i)).2),l_i)=(p,(fun i=>(pulse (y i)).2),l_j) ↔
    (i,l_i)=(p,l_j) ∧ ∀ t,t∉Finset.univ.map q→_
  simp only [Prod.ext_iff]
  constructor
  · rintro ⟨f,g,h⟩
    refine ⟨⟨f,h⟩,?_⟩
    rintro ⟨z,w⟩ q
    exact (office j (x z) (y z)).1 (congrFun g z) w ((sw _ _).1 q)
  rintro ⟨⟨f,h⟩,g⟩
  refine ⟨f,funext fun z=> (office j (x z) (y z)).2 fun q m=>g (z,q) ((sw _ _).2 m), h⟩

variable {R : Type} [CommRing R] (M : Tensor.Mat B R)
theorem involve (i : Fin K) (x : fieldK P V K N→R) :
    let e := connector P V N i
    let q := Strip.Optic.operate (target P V i.val (K-i.val-1) (Fin N)) (Tensor.mat (fun _=>M)) (x ∘ e.cast) ∘ e.cast.symm
    q = Strip.Optic.operate (file P V K N) (patch M (color_r (route i N))) x := by
  rw [← Earth.stretch (route i N) (file P V K N) _ (exposed i)]
  rfl

theorem occupied (i : Fin K) (v : Duo N K) :
    color_r (route i N) v=true ↔ v.2=i := by
  cases v
  simp [color_r,route,Prod.ext_iff,eq_comm]; aesop

abbrev playK (j : Fin K) :=
  Strip.Optic.operate (spray (P:=P) (V:=V) j N) (mat (fun (_:Fin N)=>M))
def ready (_X : Finset (Fin K)) : fieldK P V K N→R→ R := fun _=>id -- reinsert
def combos (X : Finset (Fin K)) := Strip.Optic.operate (file P V K N)
  (patch M (fun i=> decide (i.2 ∈ X)))

theorem patch_t (X : Finset (Fin K)) (i : Fin K) (h : i∉X)
    (x : fieldK P V K N→R) :
    combos (P:=P) (V:=V) (N:=N) M (Insert.insert i X) x = combos M X (playK M i x) := by
  rw [playK,stretch (route i N) _ _ (exposed i) M,combos,combos,Strip.Optic.dot]
  congr 2
  unfold patch
  rw [Tensor.multiply]
  apply congrArg Tensor.mat
  funext j
  simp only [occupied i j,decide_eq_true_eq,Finset.mem_insert]
  by_cases e : j.2=i <;> simp [e,h]

@[simp] theorem combos_nil :
    combos (K:=K) (P:=P) (V:=V) (N:=N) M ∅ = id := by
  simp [combos,patch,Tensor.unit, Strip.Optic.one]

@[simp] theorem combos_all :
    combos (K:=K) (P:=P) (V:=V) (N:=N) M Finset.univ =
    Strip.Optic.operate (file P V K N) (Tensor.mat (fun _=>M)) := by simp [combos,patch]
end
end Earth

end IntegerMultiplication
end Computability
end OAI
