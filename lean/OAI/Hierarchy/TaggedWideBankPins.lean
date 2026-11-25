import OAI.Hierarchy.TaggedShorterNetwork

namespace OAI
/-! # Static pins of a packed bank in the reported native host -/

namespace Hierarchy.Tagged.WideStack
open ThreeFlat Routing Spill
open TaggedShorterNetwork TaggedShorterCompaction
variable {S D d w : ℕ} {V P : Type}

section
variable (read : Fin S × Bool → Fin D → P)
    (pool : Fin S→V) (mask : Fin S×Bool→Fin D→V)
    (idPin : Fin S×Bool→Fin D→Fin d→V) (data : P→Fin w→V)

/-- Only the candidate's supergroup and side index the data aperture.
Two candidate batches of the same supergroup read physically identical
data pins. All masks and link IDs come from their own reported board cells. -/
def bankPin : Input S D (d+w)→V
  | .inl s => pool s
  | .inr (s,b,i,none) => mask (s,b) i
  | .inr (s,b,i,some j) => Fin.addCases (idPin (s,b) i) (data (read (s,b) i)) j

theorem read_bankPin (x : V→Bool) :
    x ∘ bankPin read pool mask idPin data =
      input read (fun p=>x ∘ data p) (x ∘ pool) (fun sb i=>x (mask sb i))
        (fun sb i=>x ∘ idPin sb i) := by
  funext p
  rcases p with s|⟨s,b,i,_|j⟩
  · rfl
  · rfl
  · refine Fin.addCases (fun a=>?_) (fun a=>?_) j <;>
      simp [bankPin,input,Fin.append,Function.comp_def]

/-- The post-memory low bits of the mask and pool words and the ID prefix
bind every control pin of the real component at once. -/
theorem bankPin_of_readbacks (x : V→Bool)
    (dataBits : P→Bits w) (occupied : Fin S→Bool) (marked : Fin S×Bool→Fin D→Bool)
    (ids : Fin S×Bool→Fin D→Bits d) (payload : ∀ p j,x (data p j)=dataBits p j)
    (occ : ∀ s,x (pool s)=occupied s) (mark : ∀ sb i,x (mask sb i)=marked sb i)
    (idsRead : ∀ sb i j,x (idPin sb i j)=ids sb i j) :
    x ∘ bankPin read pool mask idPin data=input read dataBits occupied marked ids := by
  rw [read_bankPin]
  congr 1
  · funext p j; exact payload p j
  · funext s; exact occ s
  · funext sb i; exact mark sb i
  · funext sb i j; exact idsRead sb i j
end

end Hierarchy.Tagged.WideStack

end OAI
