import OAI.ThreeFlat.Diagonal.HistoryPortLayout

namespace OAI
/-! # Address of an actual half-port bit in a stage's contiguous owner rows -/

namespace ThreeFlat.Diagonal.HistoryContraction.PortLayout

noncomputable section

open MotifBinaryPacking

variable {S : Shape} {Pins F : Type*} [CommSemiring F] (L : PortLayout S Pins)

private theorem same_position {d : ℕ} {n : Fin d → ℕ} {i j : Fin d}
    (hi : i = j) (x : Fin (n i)) (y : Fin (n j)) (hx : x.val = y.val) :
    finSigmaFinEquiv (n := n) ⟨i,x⟩ = finSigmaFinEquiv ⟨j,y⟩ := by
  subst j
  cases (Fin.ext hx : x = y)
  rfl

def portBit (u : S.Site) (a : S.graph.Port u) (b : Fin (L.width a.1.1)) : Fin (L.halfBits u) :=
  let i := (L.port u).symm a
  let eq := congrArg (fun a : S.graph.Port u => L.width a.1.1) ((L.port u).apply_symm_apply a)
  finSigmaFinEquiv ⟨i,Fin.cast eq.symm b⟩

theorem portBit_read (u : S.Site) (z : S.Half u) (a : S.graph.Port u) (b : Fin (L.width a.1.1)) :
    L.encode u z (L.portBit u a b) = L.binary a.1.1 (z a) b := by
  obtain ⟨i,rfl⟩ := (L.port u).surjective a
  let f (q : (i : Fin (L.count u)) × Fin (L.lengths u i)) := L.binary (L.port u q.1).1.1 (z (L.port u q.1)) q.2
  have pos : L.portBit u ((L.port u) i) b = finSigmaFinEquiv (n := L.lengths u) ⟨i,b⟩ :=
    same_position ((L.port u).symm_apply_apply i) _ _ rfl
  rw [pos]
  exact congrArg f (finSigmaFinEquiv.symm_apply_apply ⟨i,b⟩)

variable {R : Rewrite S F} {t : Fin R.count} (count : (R.target t).Site → ℕ)
    (ord : ∀ v, Fin (count v) ≃ {u // R.owner t u = v})

def oldBit (v : (R.target t).Site) (u : {u // R.owner t u = v}) (a : S.graph.Port u.val) (b : Fin (L.width a.1.1)) :
    Fin (L.hidden count ord v) :=
  let i := (ord v).symm u
  let eq := congrArg (fun u : {u // R.owner t u = v} => L.halfBits u.val) ((ord v).apply_symm_apply u)
  finSigmaFinEquiv ⟨i,Fin.cast eq.symm (L.portBit u.val a b)⟩

theorem oldBit_read (v : (R.target t).Site) (u : {u // R.owner t u=v})
    (a : S.graph.Port u.val) (b : Fin (L.width a.1.1)) (g : Fin (L.hidden count ord v) → Bool) :
    g (L.oldBit count ord v u a b) = L.binary a.1.1 (L.decode count ord v g u a) b := by
  obtain ⟨i,rfl⟩ := (ord v).surjective u
  have pos : L.oldBit count ord v ((ord v) i) a b =
      finSigmaFinEquiv (n := L.oldWidths count ord v) ⟨i,L.portBit ((ord v) i).val a b⟩ :=
    same_position ((ord v).symm_apply_apply i) _ _ rfl
  rw [pos]
  rw [←L.portBit_read]
  let f := Equiv.piCongrLeft (fun a : {u // R.owner t u=v} => S.Half a.val) (ord v)
  let half (j : Fin (count v)) := (L.encode (ord v j).val).symm ((flatten (L.oldWidths count ord v)).symm g j)
  have hu := congrArg (fun q => q i) (f.symm_apply_apply half)
  change L.decode count ord v g (ord v i) = half i at hu
  rw [hu]
  unfold half
  exact (congrFun ((L.encode (ord v i).val).apply_symm_apply ((flatten (L.oldWidths count ord v)).symm g i)) _).symm

end

end ThreeFlat.Diagonal.HistoryContraction.PortLayout

end OAI
