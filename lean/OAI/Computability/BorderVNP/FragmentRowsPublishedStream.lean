import OAI.Computability.BorderVNP.FragmentRows
import OAI.Computability.BorderVNP.PackedCableColumns
import OAI.Computability.BorderVNP.PackedDirectoryRowFields

/-! # The public fragment scans consume the genuinely published seven-word rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM Packing Diagonal.ExternalSew.Fragments
open DiagonalResidueRAM (word_val)

/-- Reading all counted seven-word records after publication gives the original
chronological directory, including empty and unused rows. -/
theorem rows_from_published {w : ℕ} (old : Memory w) (head base : ℕ) (D : Directory.Layout)
    (pp lp : ℕ → ℕ × ℕ) (m : ℕ → ℕ) (original : readings old (head+8)=base) (apart : head+9<base)
    (room : (D.directory pp lp).length<2^w)
    (fit : ∀ i : Fin (D.directory pp lp).length, ∀ x ∈ (D.directory pp lp)[i.val].words, x<2^w) :
    let rows := D.directory pp lp
    let published := readings (Directory.ISA.publish old head base rows)
    let f := Layout.fromFrame head m
    m (head+8)=published (head+8) → m (head+9)=published (head+9) →
    (∀ a, base≤a → a<base+7*rows.length → m a=published a) →
    (List.range f.count).map (f.row m)=rows := by
  intro rows published f ptr count keep
  have samePtr := CableTriples.published_outside old head base rows (head+8) (by omega) (.inl (by omega))
  have baseEq : f.deliveries=base := ptr.trans ((congrArg Fin.val samePtr).trans original)
  have lenEq : f.count=rows.length := count.trans
    ((congrArg Fin.val (Directory.ISA.publish_read old head base rows apart).1).trans (word_val _ _ room))
  have demand (i : Fin rows.length) : f.row m i.val=rows[i.val] := by
    have atCol (k : ℕ) (hk : k<7) : m (base+7*i.val+k)=published (base+7*i.val+k) :=
      keep _ (by omega) (by have := i.isLt; omega)
    have first : m (base+7*i.val)=published (base+7*i.val) := atCol 0 (by decide)
    change Transmission.DataWriter.demandAt m (f.deliveries+7*i.val)=_
    rw [baseEq]
    have same : Transmission.DataWriter.demandAt m (base+7*i.val)=
        Transmission.DataWriter.demandAt published (base+7*i.val) := by
      simp only [Transmission.DataWriter.demandAt,first,atCol 1 (by decide),atCol 2 (by decide),
        atCol 3 (by decide),atCol 4 (by decide),atCol 5 (by decide),atCol 6 (by decide)]
    exact same.trans (Nat.mul_comm i.val 7 ▸ Transmission.DataWriter.demandAt_published old head base rows apart i (fit i))
  apply List.ext_getElem
  · simp [lenEq]
  · intro i hi hj
    simpa using demand ⟨i,hj⟩


/-- Later stages may change the cube banks while preserving the two directory frame
fields and the populated seven-word interval. The fragment emitter then reads exactly
the original chronological placement list, including when that list is empty. -/
theorem stream_from_published {w : ℕ} (old : Memory w) (head base : ℕ) (D : Directory.Layout)
    (pp lp : ℕ → ℕ × ℕ) (m : ℕ → ℕ) (original : readings old (head+8)=base) (apart : head+9<base)
    (room : (D.directory pp lp).length<2^w)
    (fit : ∀ i : Fin (D.directory pp lp).length, ∀ x ∈ (D.directory pp lp)[i.val].words, x<2^w) :
    let rows := D.directory pp lp
    let published := readings (Directory.ISA.publish old head base rows)
    let f := Layout.fromFrame head m
    m (head+8)=published (head+8) → m (head+9)=published (head+9) →
    (∀ a, base≤a → a<base+7*rows.length → m a=published a) →
    f.stream m=Diagonal.ExternalSew.Fragments.stream f.host m (fun c => m (f.supplied+c)) rows := by
  intro rows published f ptr count keep
  exact congrArg (Diagonal.ExternalSew.Fragments.stream f.host m (fun c => m (f.supplied+c)))
    (rows_from_published old head base D pp lp m original apart room fit ptr count keep)

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
