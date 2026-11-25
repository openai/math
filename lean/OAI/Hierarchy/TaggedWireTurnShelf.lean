import OAI.Hierarchy.TaggedBinaryBarrelTurns
import OAI.Hierarchy.TaggedWideHost
import OAI.ThreeFlat.Routing.CompareWord

namespace OAI
/-! # Fixed per-site router for the five ordinary native turn columns -/

noncomputable section
namespace Hierarchy.WireTelescope.TurnShelf
open ThreeFlat Routing Tagged
open scoped Classical BigOperators

/-- `e` low bits select within a port, and `p` high bits select a local port.
Both incoming and outgoing ports have permanent indices in this same shelf. -/
abbrev Aperture (p e : ℕ) := Row p × Row e
abbrev Control (p e : ℕ) := Fin (e+p+1) ⊕ (Bool × (Fin e ⊕ Fin p))
abbrev Pin (r p e : ℕ) := (Fin r × Control p e) ⊕ Aperture p e

def width (p e : ℕ) := 2^p*2^e

private theorem room (p e : ℕ) : width p e≤2^(e+p+1) := by
  unfold width
  rw [pow_succ,pow_add,Nat.mul_comm (2^p) (2^e)]
  omega

/-- Actual native fields, in the same units as the terminal count and
prefix emitter. All-zero unused rows enable no equality. -/
structure RowData (p e : ℕ) where
  role : Bool→Row p
  start : Bool→Row e
  live : Row (e+p+1)

variable {r p e : ℕ}

def header (z : RowData p e) : Control p e→Bool :=
  Sum.elim ((addressEquiv _).symm z.live)
    (fun bi=>Sum.elim ((addressEquiv _).symm (z.start bi.1)) ((addressEquiv _).symm (z.role bi.1)) bi.2)

def pins (z : Fin r→RowData p e) (v : Aperture p e→Bool) : Pin r p e→Bool :=
  Sum.elim (fun i=>header (z i.1) i.2) v

/-- The upper role address and the lower native start are wired directly
to different barrel address pins. The data plane is shared among all gates. -/
def wiring (t : Fin r) : BinaryBarrelTurns.Pin (e+p+1) (e+p) (width p e)→Pin r p e ⊕ Bool
  | .inl j=>.inl (.inl (t,.inl j))
  | .inr (b,.inl j)=>.inl (.inl (t,.inr (b,finSumFinEquiv.symm j)))
  | .inr (_, .inr j)=>.inl (.inr (finProdFinEquiv.symm j))

def network (F : Type*) [Field F] (r p e : ℕ) :=
  WideHost.localFamily (A:=fun _ : Fin r=>BinaryBarrelTurns.Pin (e+p+1) (e+p) (width p e))
    (fun _=>BinaryBarrelTurns.network F (e+p) (room p e)) (wiring (p:=p) (e:=e))

def reads (z : RowData p e) (field : Aperture p e→Bool) (side : Bool)
    (j : Fin z.live.val) (fit : (z.start side).val+z.live.val≤2^e) : Bool :=
  field (z.role side,⟨(z.start side).val+j.val,by have:=j.isLt;omega⟩)

theorem value (F : Type*) [Field F] (z : Fin r→RowData p e) (v : Aperture p e→Bool)
    (fit : ∀ i b,((z i).start b).val+(z i).live.val≤2^e) :
    TypedWiring.value (network F r p e) (pins z v)=
      if ∀ i,∀ j : Fin (z i).live.val,reads (z i) v false j (fit i false)=
        reads (z i) v true j (fit i true) then 1 else 0 := by
  let flat := fun j : Fin (width p e)=>v (finProdFinEquiv.symm j)
  let ctrl := fun (i : Fin r) (b : Bool)=>Fin.append ((addressEquiv _).symm ((z i).start b))
    ((addressEquiv _).symm ((z i).role b))
  have atPins (i : Fin r) : Sum.elim (pins z v) id ∘ wiring i =
      BinaryBarrelTurns.pins ((addressEquiv _).symm (z i).live) (ctrl i) (fun _=>flat) := by
    funext q
    rcases q with j|⟨b,j|j⟩
    · rfl
    · induction j using Fin.addCases with
      | left j=>simp [wiring,pins,header,BinaryBarrelTurns.pins,ctrl]
      | right j=>simp [wiring,pins,header,BinaryBarrelTurns.pins,ctrl]
    · rfl
  have addr (i : Fin r) (b : Bool) : wordValue (ctrl i b)=
      ((z i).start b).val+2^e*((z i).role b).val := by
    unfold ctrl
    rw [wordValue_append]
    simp only [wordValue_addressEquiv,Equiv.apply_symm_apply]
  have shift (i : Fin r) (b : Bool) (j : Fin (width p e)) (live : j.val<(z i).live.val) :
      Barrel.shift flat (wordValue (ctrl i b)) j=reads (z i) v b ⟨j.val,live⟩ (fit i b) := by
    let u : Row e := ⟨((z i).start b).val+j.val,by have := fit i b;omega⟩
    let entry := finProdFinEquiv ((z i).role b,u)
    have loc : j.val+wordValue (ctrl i b)=entry.val := by
      rw [addr]
      change _=u.val+2^e*((z i).role b).val
      dsimp [u]
      omega
    unfold Barrel.shift
    rw [dite_eq_left (show j.val+wordValue (ctrl i b)<width p e by rw [loc]; exact entry.isLt)]
    have idx : (⟨j.val+wordValue (ctrl i b),by rw [loc];exact entry.isLt⟩ : Fin (width p e))=entry := Fin.ext loc
    simp only [flat,idx,entry,Equiv.symm_apply_apply]
    rfl
  rw [network,WideHost.localFamily_eval]
  simp only [wordValue_addressEquiv] at shift
  simp_rw [atPins,BinaryBarrelTurns.value,wordValue_addressEquiv,Equiv.apply_symm_apply]
  rw [Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h i j
    have full : j.val<width p e := by
      have positive : 0<2^p := pow_pos (by decide) _
      have room' := Nat.le_mul_of_pos_left (2^e) positive
      have lim:=fit i false
      exact j.isLt.trans_le (by change _≤2^p*2^e;omega)
    let k : Fin (width p e) := ⟨j.val,full⟩
    exact ((shift i false k j.isLt).symm.trans (h i k j.isLt)).trans (shift i true k j.isLt)
  · intro h i j live
    exact ((shift i false j live).trans (h i ⟨j.val,live⟩)).trans (shift i true j live).symm

theorem size (F : Type*) [Field F] (r p e : ℕ) :
    (network F r p e).cells+(network F r p e).internal≤r*(2308*width p e*(e+p+2)) := by
  rw [network,WideHost.localFamily_size]
  have one := BinaryBarrelTurns.size F (e+p) (room p e)
  simpa [Nat.max_eq_right (Nat.le_succ _)] using
    Finset.sum_le_sum (s:=Finset.univ) (fun (_ : Fin r) _=>one)

end Hierarchy.WireTelescope.TurnShelf

end
end OAI
