import OAI.Computability.IntegerMultiplication.Loom.Thread

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Strip Dims
variable {X J : Type} (s : Series X)

-- reopen private via note? use Series.explore with index? Eq:
def sealZero : Adopt (Track s 0) Series.one :=
  (Adopt.turn _ _).back

def jack {m n} (e : m=n) : Adopt (Track s m) (Track s n) :=
  e ▸ Adopt.same _
theorem jack_n {m n} (e : m=n) (x : Fin m→X) (i : Fin m) :
    (jack s e).cast x (i.cast e) = x i := by subst n; rfl

def spire (n : ℕ) : (m : ℕ) →
    Adopt ((Track s m).cart (Track s n)) (Track s (m+n))
| 0 =>
  ((sealZero s).split (Adopt.same _)).thenDo
    ((Adopt.omitL (Track s n)).thenDo (jack s (Nat.zero_add n).symm))
| m+1 =>
  (((step s m).split (Adopt.same _)).thenDo
    ((Adopt.rotate _ _ _).thenDo ((Adopt.same s).split (spire n m)))).thenDo
    ((step s (m+n)).back.thenDo (jack s (by omega)))

variable {m n : ℕ}
-- state both orientations via left access and right access.
theorem spire_n (x : Fin m→X) (y : Fin n→X) :
    (∀i:Fin m,(spire s n m).cast (x,y) (Fin.castAdd n i)=x i) ∧
    (∀i:Fin n,(spire s n m).cast (x,y) (Fin.natAdd m i)=y i) := by
  induction m with
  | zero =>
    refine ⟨fun i => i.elim0,fun i => ?_⟩
    change (jack s _).cast y _=_
    rw [show Fin.natAdd 0 i = i.cast (Nat.zero_add _).symm by apply Fin.ext; simp ]
    exact jack_n s _ y i
  | succ m ih =>
    obtain ⟨e,f⟩ := ih (Loom.join.symm x |>.2)
    let v := Loom.join.symm x |>.2
    let a := (spire s n m).cast (v,y)
    let q : Fin (m+n+1) → X := Loom.join (x 0,a)
    have t : m+n+1=m+1+n := by omega
    change (∀i,(jack _ t).cast q _=_) ∧ (∀i,(jack _ t).cast q _=_)
    constructor
    · intro i; refine Fin.cases ?_ (fun j => ?_) i
      · rw [show Fin.castAdd n (0:Fin (m+1)) = (0:Fin (m+n+1)).cast t from rfl, jack_n]; rfl
      rw [show Fin.castAdd n j.succ = (Fin.castAdd n j).succ.cast t from rfl,jack_n]
      simpa only [q,Loom.tail_j,Loom.leave,a,v] using e j -- q unneeded
    intro i
    rw [show Fin.natAdd (m+1) i = (Fin.natAdd m i).succ.cast t by apply Fin.ext; simp only [Fin.val_natAdd,Fin.val_cast,Fin.val_succ]; omega,
      jack_n]
    simpa only [q,Loom.tail_j] using f i

def sheet (n : ℕ) : (m : ℕ) →
    Adopt (Track (Track s n) m) (Track s (m*n))
| 0 =>
  (sealZero _).thenDo ((sealZero _).back.thenDo (jack s (Nat.zero_mul n).symm))
| m+1 => ((step _ _).thenDo ((Adopt.same (Track s n)).split (sheet n m))).thenDo
    ((spire s (m*n) n).thenDo (jack s (by ring)))

theorem sheet_no (x : Fin m→Fin n→X) (i : Fin m) (k : Fin n) :
    (sheet s n m).cast x (finProdFinEquiv (i,k)) = x i k := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    let a := Loom.join.symm x |>.2
    let v := (sheet s n m).cast a
    have h : n+m*n=(m+1)*n := by ring
    change (jack s h).cast ((spire s (m*n) n).cast (x 0,v)) _=_
    obtain ⟨z,e⟩ := spire_n s (x 0) v -- left n right m*n
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [show finProdFinEquiv (0,k) = (Fin.castAdd (m*n) k).cast h by
          apply Fin.ext
          change _+n*0=_
          simp,
        jack_n,z]
    rw [show finProdFinEquiv (i.succ,k) = (Fin.natAdd n (finProdFinEquiv (i,k))).cast h by
        apply Fin.ext
        change k.val+n*(i.val+1)= n+(k.val+n*i.val)
        ring, jack_n,e]
    exact ih _ i

def curl (f : J ≃ Fin m) (n : ℕ) :
    Adopt (threads (Track s n) f) (Track s (m*n)) :=
  (pullback _ _).thenDo (sheet s n m)

theorem curl_p (f : J ≃ Fin m) (x : J→Fin n→X) (i : J) (k : Fin n) :
    (curl s f n).cast x (finProdFinEquiv (f i,k)) = x i k := by
  change (sheet s n m).cast _ _ = _
  rw [sheet_no]
  change x (f.symm _) _=_
  rw [f.symm_apply_apply]

def place_ (f : J≃Fin m) (n : ℕ) : J × Fin n ≃ Fin (n*m) :=
  ((f.prodCongr (Equiv.refl _)).trans finProdFinEquiv).trans (finCongr (Nat.mul_comm m n))
-- exponent succ
def han (f : J ≃ Fin m) (n : ℕ) :
    Adopt (threads (Track s n) f) (Track s (n*m)) :=
  (curl s f n).thenDo (jack s (Nat.mul_comm ..))
theorem handled (f : J≃Fin m) (x : J→Fin n→X) (i : J) (k : Fin n) :
    (han s f n).cast x (place_ f n (i,k))=x i k := by
  change (jack s (Nat.mul_comm ..)).cast ((curl s f n).cast x) (Fin.cast (Nat.mul_comm ..) _) = _
  rw [jack_n]; exact curl_p ..
end Loom

end IntegerMultiplication
end Computability
end OAI
