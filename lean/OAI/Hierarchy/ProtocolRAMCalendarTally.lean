import OAI.Hierarchy.ProtocolRAMCalendarWriteInputs

namespace OAI
/-! # One physical tally and its native register validation before all post columns -/

namespace Hierarchy.ProtocolRAM.PurchaseStage
open Computability.VPVNP.BurstRAM PrivateRAM Calendar.PostLayout
open scoped Classical
variable {w q d : ℕ}

private theorem native_ready (ps : List Pass) (m : Memory w) (runs : ∀p∈ps,p.Fits w) :
    AuditReady (columns ps) m := by
  induction ps generalizing m with
  | nil=>trivial
  | cons p ps ih=>
    exact ⟨runs p (List.mem_cons_self ..),ih _ (fun r hr=>runs r (List.mem_cons_of_mem _ hr))⟩

private theorem native_order (ps : List Pass) : OrderedTallies (columns ps) := by
  induction ps with
  | nil=>trivial
  | cons p ps ih=>exact ih

private theorem native_zero (ps : List Pass) : verdict (columns ps)=.lit 0 := by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>exact ih

/-- All selector words, including malformed ones, go through the same native
counting instructions. The check's Boolean result has no bearing on whether
the bank reads and the following native column passes are defined. -/
theorem placed_audit (L : Dispatch) (raw : Repair q d) (first bits : ℕ)
    (h : SnapshotReads L (place L raw first bits) (first+2^bits))
    (endWord : (place L raw first bits).verdict+1<2^w)
    (alphabet : q≤2^w) (copies : raw.batch.copies<2^w) (sum : q*raw.batch.copies<2^w) :
    let B:=place L raw first bits
    (∀m : Memory w,AuditReady (audits L B) m) ∧ OrderedTallies (audits L B) ∧
      (verdict (audits L B)).Fits w B.verdict := by
  intro B
  have base : startColumns first bits L.candidates≤B.verdict := Nat.le_add_right ..
  have final : B.verdict<2^w := (Nat.le_succ B.verdict).trans_lt endWord
  have keys : B.keys<2^w := by
    change first+2^bits<_
    unfold startColumns at base
    omega
  have shape : Board L B w:=placed_board L raw first bits w h keys
  have rows (p : Pass) (hp : p∈writes L B) : p.out+p.rows≤B.verdict:=shape.flagAfter p hp
  have afterKeys (p : Pass) (hp : p∈writes L B) : B.tally+1<p.out := by
    obtain ⟨j,_,eq,_⟩:=listed L raw first bits p hp
    rw [eq]
    change first+2^bits+L.candidates+1<startColumns first bits L.candidates+j*L.candidates
    unfold startColumns
    omega
  have readyRows (p : Pass) (hp : p∈writes L B) : p.Fits w := by
    have tail:=(rows p hp).trans_lt final
    have order:=afterKeys p hp
    have start : B.keys≤p.out := by
      change first+2^bits≤p.out
      change first+2^bits+L.candidates+1<p.out at order
      omega
    exact ⟨p.term.fits_of_inputEnd ((h.inputs p hp).trans start) (by omega),tail⟩
  have tally : B.tally+2=startColumns first bits L.candidates := rfl
  have check : (inspection L B).Fits w := by
    refine ⟨Expr.fits_of_inputEnd _ (h.ballot.ifAdmitted (.lit 0) (.lit 1) (Nat.zero_le _) (Nat.zero_le _)) keys,?_,
      (tally.le.trans base).trans_lt final,alphabet,copies,sum⟩
    exact le_rfl
  refine ⟨fun m=>⟨check,native_ready _ _ readyRows⟩,⟨?_,native_order _⟩,?_⟩
  · intro u hu
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hu
    exact afterKeys p hp
  · change (Expr.branch .eq (.lookup ⟨B.tally+1,0⟩ (.lit 0)) (.lit 0) (verdict (columns (writes L B)))
      (.lit 1)).Fits w B.verdict
    rw [native_zero]
    apply Expr.fits_of_inputEnd _ _ final
    change max (max (max (B.tally+1+1) 0) 0) (max 0 0)≤B.verdict
    omega

end Hierarchy.ProtocolRAM.PurchaseStage

end OAI
