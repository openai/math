import OAI.ThreeFlat.Diagonal.FoldTrace
import OAI.ThreeFlat.Diagonal.NativeTrace
import OAI.ThreeFlat.Diagonal.FoldDiagonal

namespace OAI
/-! # The folded entry network for an actual native executable and public advice -/

namespace ThreeFlat.Diagonal.FoldTrace
open Computability.VPVNP BurstRAM PrivateRAM RAMMemory RAM TraceBitHeader
variable {F : Type*} [Fintype F] [Field F] {w pcs regs slots A k S fuel dep : ℕ}

/-- A finite prefix followed by an infinitely zero-padded continuation. -/
def prepend {n : ℕ} (bits : Fin n → Bool) (tail : ℕ → Bool) (i : ℕ) :=
  if h : i<n then bits ⟨i,h⟩ else tail (i-n)

@[simp] theorem prepend_head {n : ℕ} (bits : Fin n → Bool) (tail : ℕ → Bool) (j : Fin n) :
    prepend bits tail j.val=bits j := by simp [prepend,j.isLt]

@[simp] theorem prepend_after {n : ℕ} (bits : Fin n → Bool) (tail : ℕ → Bool) (a : ℕ) :
    prepend bits tail (n+a)=tail a := by simp [prepend]

def suffix {len : ℕ} (payload : Fin A → Bool) (text : Fin len → Bool) :=
  prepend payload (prepend text (fun _=>false))

theorem header_after (x : Fin k → Bool) (fixed : ℕ → Bool) (a : ℕ) :
    header x fixed (2+k+a)=fixed a := by simp [header,show ¬2+k+a<2 by omega]

theorem header_code {len : ℕ} (x : Fin k → Bool) (payload : Fin A → Bool) (text : Fin len → Bool)
    (j : Fin len) : header x (suffix payload text) (2+k+A+j.val)=text j := by
  rw [Nat.add_assoc (2+k),header_after]
  simp [suffix]

theorem header_after_code {len : ℕ} (x : Fin k → Bool) (payload : Fin A → Bool) (text : Fin len → Bool)
    (j : ℕ) : header x (suffix payload text) (2+k+A+len+j)=false := by
  rw [show 2+k+A+len+j=2+k+(A+(len+j)) by omega,header_after]
  simp [suffix]

theorem header_installed {len : ℕ} (x : Fin k → Bool) (payload : Fin A → Bool) (text : Fin len → Bool) :
    (fun i : Fin S=>header x (suffix payload text) i.val)=
    advicePins (2+k+A) text (header x (suffix payload text)) := by
  funext i
  unfold advicePins
  split
  next hit =>
    let j : Fin len := ⟨i.val-(2+k+A),hit.2⟩
    have pos : 2+k+A+j.val=i.val := by dsimp [j]; omega
    simpa only [pos] using header_code x payload text j
  next => rfl

theorem entry_memory {len : ℕ} (x : Fin k → Bool) (payload : Fin A → Bool) (text : Fin len → Bool)
    (space : 2+k+A+len≤S) :
    memoryWithAdvice (2+k+A) text (initialMemory S (fun i=>binaryWord w (header x (suffix payload text) i)))=
      fun a=>binaryWord w (header x (suffix payload text) a) := by
  funext a
  by_cases h : a<S
  · let i : Fin S := ⟨a,h⟩
    have eqn := adviceWords_inside (w:=w) (2+k+A) text (header x (suffix payload text)) i
    rw [←header_installed] at eqn
    exact eqn
  · have far : 2+k+A+len≤a := by omega
    rw [memoryWithAdvice_outside _ _ _ (Or.inr far)]
    simp only [initialMemory,h,ite_false]
    obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le far
    rw [hz,header_after_code]
    rfl

noncomputable def native (M : Machine w pcs regs slots)
    (fit : NativeTrace.Fits M S (2+k+A) dep fuel) (hF : Fintype.card F≤2^w)
    (state : Word w) (payload : Fin A → Bool) : BitNetwork F k :=
  network (NativeTrace.network M fit hF state) k (suffix payload (NativeTrace.executable M))

/-- Its only open pins are the folded entry and the two catalytic indices.
Reading the fixed suffix executes exactly the public program stored there. -/
theorem native_value (M : Machine w pcs regs slots)
    (fit : NativeTrace.Fits M S (2+k+A) dep fuel) (hF : Fintype.card F≤2^w)
    (state : Word w) (payload : Fin A → Bool) (x : Fin k → Bool) :
    (native M fit hF state payload).eval x=
      RAM.value (FieldCode.ofCardLe hF) M fuel state
        (fun a=>binaryWord w (header x (suffix payload (NativeTrace.executable M)) a)) := by
  rw [native,eval,header_installed,NativeTrace.installed,entry_memory x payload _ fit.mount]

/-- The actual native full-entry masses form precisely the matrix to which the
diagonal rank comparison applies, with the two indices in the original order. -/
theorem native_matrix {L teams p B : ℕ} (M : Machine w pcs regs slots)
    (fit : NativeTrace.Fits M S (2+(L*teams*p+2*B)+A) dep fuel) (hF : Fintype.card F≤2^w)
    (state : Word w) (payload : Fin A → Bool) (pins : Fin L → Fin teams → Fin p → Bool) :
    ApproximateImage.foldMatrix (B:=B) (native M fit hF state payload) pins =
      fun x y=>RAM.value (FieldCode.ofCardLe hF) M fuel state (fun a=>binaryWord w
        (header (fun i=>match (FoldInput.rowMajor (L:=L) (copies:=teams) (p:=p) (B:=B)).symm i with
          | .inl ((t,c),j) => pins t c j
          | .inr (b,j) => if b then y j else x j)
          (suffix payload (NativeTrace.executable M)) a)) := by
  funext x y
  unfold ApproximateImage.foldMatrix
  rw [native_value]
  apply congrArg (RAM.value (FieldCode.ofCardLe hF) M fuel state)
  funext a
  apply congrArg (binaryWord w)
  apply congrArg (fun input : Fin (L*teams*p+2*B)→Bool =>
    header input (suffix payload (NativeTrace.executable M)) a)
  funext i
  obtain ⟨z,rfl⟩ := (FoldInput.rowMajor (L:=L) (copies:=teams) (p:=p) (B:=B)).surjective i
  rcases z with ⟨⟨t,c⟩,j⟩ | ⟨b,j⟩ <;> simp

end ThreeFlat.Diagonal.FoldTrace

end OAI
