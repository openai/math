import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Paid tests of old and six-party target addresses at the receiving site -/
namespace Hierarchy.DescentPackedActorMask
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D K cap a b M H r w : ℕ}

abbrev actors (D cap : ℕ) := D*(1+cap*6)
abbrev nodes (D K cap : ℕ) := D*(K+cap*6)

private theorem enc_zero (c l : ℕ) : encode c l (fun _=>0)=0 := by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin l=>(0:Cell c))).val=0
  simp []

/-- Address zero is padding. A donor publishes one address for its previous
site and one for each role of each matched first-grain slot. -/
def target (a W : ℕ) (wanted : Cell a) (issued : Cell (a*W)) : Cell (1*W) :=
  encode 1 W (fun j=>if wanted≠0 ∧ (encode a W).symm issued j=wanted then 1 else 0)

theorem target_zero (a W : ℕ) : target a W 0 0=0 := by simp [target,enc_zero]

def oldAddress (cap : ℕ) (donor : Fin D) : Fin (actors D cap) :=
  finProdFinEquiv (donor,finSumFinEquiv (Sum.inl (0:Fin 1)))
def bornAddress (donor : Fin D) (t : Fin (cap*6)) : Fin (actors D cap) :=
  finProdFinEquiv (donor,finSumFinEquiv (Sum.inr t))

/-- The entry count is read from the old donor's book. The role slot has one
stored scalar node exactly when its issued target equals this receiving site. -/
def bitAt (K : ℕ) (mask : Fin (actors D cap)→Cell 1) (counts : Fin D→Cell b)
    (j : Fin (nodes D K cap)) : Cell 1 :=
  let rc:=finProdFinEquiv.symm j
  match finSumFinEquiv.symm rc.2 with
  | Sum.inl (n : Fin K) => if n.val < (counts rc.1).val then mask (oldAddress cap rc.1) else 0
  | Sum.inr (t : Fin (cap*6)) => mask (bornAddress rc.1 t)

def occupied (D K cap b : ℕ) (mask : Cell (1*actors D cap)) (counts : Cell (b*D)) : Cell (1*nodes D K cap) :=
  encode 1 _ (bitAt K ((encode 1 _).symm mask) ((encode b D).symm counts))

theorem occupied_zero (D K cap b : ℕ) : occupied D K cap b 0 0=0 := by
  have e : (encode 1 (actors D cap)).symm 0=fun _=>0 := (encode ..).injective (by simp [enc_zero])
  unfold occupied
  rw [e,←enc_zero 1 (nodes D K cap)]
  congr 1
  funext j
  obtain ⟨⟨d,i⟩,rfl⟩:=finProdFinEquiv.surjective j
  obtain ⟨s,rfl⟩:=finSumFinEquiv.surjective i
  cases s <;> simp [bitAt]

theorem held (wanted : Cell a) (live : wanted≠0) (addr : Fin (actors D cap)→Cell a)
    (count : Fin D→Cell b) (j : Fin (nodes D K cap)) :
    digit 1 j.val (occupied D K cap b (target a _ wanted (encode a _ addr)) (encode b D count)).val =
      (bitAt K (fun i=>if addr i=wanted then 1 else 0) count j).val := by
  have masks : (fun i=>if wanted≠0 ∧ addr i=wanted then (1:Cell 1) else 0)=
      fun i=>if addr i=wanted then 1 else 0 :=by
    funext i
    by_cases hit : addr i=wanted
    · rw [ite_eq_left ⟨live,hit⟩,ite_eq_left hit]
    · rw [ite_eq_right (fun h=>hit h.2),ite_eq_right hit]
  simp only [occupied,target,digit_encode,Equiv.symm_apply_apply]
  rw [masks]

abbrev target_run (T : Tables) (req fields : Expr) (out : ℕ)
    (fit : DescentPackedZip.Fits T req fields a (a*actors D cap) M out w) (room : out+H*chunks r M<2^w)
    (x : Fin H→Fin r→Cell a) (y : Fin H→Fin r→Cell (a*actors D cap)) :=
  DescentPackedZip.spec T req fields out fit room (target a (actors D cap)) (target_zero ..) x y

abbrev occupied_run (T : Tables) (flags counts : Expr) (out : ℕ)
    (fit : DescentPackedZip.Fits T flags counts (1*actors D cap) (b*D) M out w) (room : out+H*chunks r M<2^w)
    (x : Fin H→Fin r→Cell (1*actors D cap)) (y : Fin H→Fin r→Cell (b*D)) :=
  DescentPackedZip.spec T flags counts out fit room (occupied D K cap b) (occupied_zero ..) x y

end
end Hierarchy.DescentPackedActorMask

end OAI
