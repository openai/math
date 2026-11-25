import OAI.Hierarchy.DescentResetStemSample
import OAI.Hierarchy.DescentResetStemKeyKernel

namespace OAI
/-! # A short physical lookup key for an old reset stem -/

namespace Hierarchy.DescentResetStemKey
open DescentSIMDLookup DescentFallbackPeriod DescentContacts
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap field L n r : ℕ}

def panel (v : Packet D L cap n r field) (lo : Fin L) (slot : Fin (2*cap)) :=
  fields (v (.inl (.inl lo))) (v (.inr (.inl (lo,slot)))) (fun j=>v (.inl (.inr (j,lo))))

def parse (D cap field : ℕ) : Decoder D field := fun x=>
  (DescentSignedCableCodec.decode D cap (x.val:ℕ)).map (fun chip=>(chip.neighbor,chip.target))

theorem parse_zero (D cap field : ℕ) : parse D cap field 0=none := by
  have dead : DescentSignedCableCodec.decode D cap 0=none := by
    rw [←DescentSignedCableCodec.empty (D:=D) (cap:=cap),DescentSignedCableCodec.decode_encode]
  simp [parse,dead]

theorem decode_ticket (v : Packet D L cap n r field) (s : Bool) (i : Fin L) (j : Fin (2*cap)) :
    (ticket (parse D cap field) s (panel v i j)).map (fun k=>(DescentFallbackShapeTable.decode r (2^n) k.1,k.2)) =
      DescentResetStemDecoder.sample v s i j := by
  cases ch : signed v i j with
  | none =>
    have dead : parse D cap field ((panel v i j) (0 : Fin (D+1)).succ)=none := by
      change (signed v i j).map _=none
      rw [ch]; rfl
    unfold ticket remote
    rw [dead]
    simp [DescentResetStemDecoder.sample,arrival,ch]
  | some chip =>
    have live : parse D cap field ((panel v i j) (0 : Fin (D+1)).succ)=some (chip.neighbor,chip.target) := by
      change (signed v i j).map _=_
      rw [ch]; rfl
    have who : ((panel v i j) chip.neighbor.succ.succ).val=peer v chip.neighbor i := rfl
    have localRead : ((panel v i j) 0).val=localWord v i := rfl
    unfold ticket remote
    rw [live]
    by_cases hit : chip.target=s
    · by_cases present : 0< peer v chip.neighbor i
      · have nz : panel v i j chip.neighbor.succ.succ ≠ 0 := by
          intro atZero
          have h := congrArg Fin.val atZero
          rw [who] at h
          exact Nat.ne_of_gt present (by simpa only [Fin.val_zero] using h)
        simp [who,hit,present,nz,localRead,DescentResetStemDecoder.sample,arrival,ch]
      · have zero : panel v i j chip.neighbor.succ.succ = 0 := by
          apply Fin.ext
          rw [who]
          simpa only [Fin.val_zero] using Nat.eq_zero_of_not_pos present
        simp [hit,present,zero,localRead,DescentResetStemDecoder.sample,arrival,ch]
    · simp [hit,DescentResetStemDecoder.sample,arrival,ch]

/-- At every occupied physical row the key decodes back to the observed short
terminal and routing mode. A missing row has precisely zero. -/
theorem number_read (v : Packet D L cap n r field) (s : Bool) (i : Fin L) (j : Fin (2*cap)) :
    let z:=ticket (parse D cap field) s (panel v i j)
    (word (parse D cap field) s (panel v i j)).val=z.elim 0 (fun k=>1+2*k.1+k.2.toNat) ∧
    z.map (fun k=>(DescentFallbackShapeTable.decode r (2^n) k.1,k.2))=DescentResetStemDecoder.sample v s i j :=
  ⟨word_val ..,decode_ticket ..⟩

/-- The physical low shape digit is the exact inverse address of the decoded
endpoint, even before the legal-geometry bounds on its depth are applied. -/
theorem cell_decode (r Y x : ℕ) :
    DescentFallbackShapeTable.cell r (DescentFallbackShapeTable.decode r Y x)=x := by
  have tag : DescentRosterOrder.optionDigit (DescentFallbackShapeTable.decode r Y x).2=x%(Y+1) := by
    by_cases pos : 0< x%(Y+1)
    · simp only [DescentFallbackShapeTable.decode,dite_eq_left pos]
      change x%(Y+1)-1+1=x%(Y+1)
      omega
    · simp only [DescentFallbackShapeTable.decode,dite_eq_right pos]
      change 0=x%(Y+1)
      omega
  have inner : x/(Y+1)/2^r*2^r+x/(Y+1)%2^r=x/(Y+1) := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod _ _
  unfold DescentFallbackShapeTable.cell
  rw [tag]
  change (x/(Y+1)/2^r*2^r+x/(Y+1)%2^r)*(Y+1)+x%(Y+1)=x
  rw [inner,Nat.mul_comm]
  exact Nat.div_add_mod _ _

theorem sample_address (v : Packet D L cap n r field) (s : Bool) (i : Fin L) (j : Fin (2*cap)) :
    (word (parse D cap field) s (panel v i j)).val =
      (DescentResetStemDecoder.sample v s i j).elim 0
        (fun k=>1+2*DescentFallbackShapeTable.cell r k.1+k.2.toNat) := by
  rw [word_val,←decode_ticket]
  cases key : ticket (parse D cap field) s (panel v i j) with
  | none => rfl
  | some k => simp [code,cell_decode]

end
end Hierarchy.DescentResetStemKey

end OAI
