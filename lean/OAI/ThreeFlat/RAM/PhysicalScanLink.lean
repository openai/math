import OAI.ThreeFlat.RAM.PhysicalScanFrame
import OAI.ThreeFlat.RAM.ContinuationLink

namespace OAI
/-! # Linking the dense word generator to other finite native instruction tables -/

namespace ThreeFlat.RAM.DescriptorExpr

open Computability.VPVNP.BurstRAM
variable {w k K n : ℕ}

def Op.mapPublic (φ : Fin k → Fin K) : Op w k n → Op w K n
  | .literal v => .literal v
  | .parameter i => .parameter (φ i)
  | .binary b i j => .binary b i j
  | .load i => .load i
  | .select b i j x y => .select b i j x y

def Term.mapPublic (φ : Fin k → Fin K) : {n : ℕ} → Term w k n → Term w K n
  | _,.result j => .result j
  | _,.bind o e => .bind (o.mapPublic φ) (e.mapPublic φ)

@[simp] theorem Term.binds_mapPublic (φ : Fin k → Fin K) (e : Term w k n) :
    (e.mapPublic φ).binds=e.binds := by induction e <;> simp [mapPublic, binds, *]

@[simp] theorem Term.labels_mapPublic (φ : Fin k → Fin K) (e : Term w k n) :
    (e.mapPublic φ).labels=e.labels := by simp [Term.labels_eq]

@[simp] theorem Term.eval_mapPublic (φ : Fin k → Fin K) (e : Term w k n)
    (data : Fin K → Word w) (m : Memory w) (v : Fin n → Word w) :
    (e.mapPublic φ).eval data m v = e.eval (data ∘ φ) m v := by
  induction e with
  | result j => rfl
  | bind o b ih => cases o <;> simp [mapPublic,Op.mapPublic,eval,Op.eval,ih]

end ThreeFlat.RAM.DescriptorExpr

namespace ThreeFlat.RAM.PhysicalScan

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan DescriptorExpr ContinuationLink

variable {w k P R K : ℕ}

def linkedFrame (e : Term w k 1) (pc : Fin (6+e.labels) ↪ Fin P)
    (reg : Fin (4+e.binds) ↪ Fin R) (φ : Fin k → Fin K) (exit : Fin P) :
    Frame (e.mapPublic φ) P R where
  pc i := pc (i.cast (by simp))
  reg := (Fin.castAddEmb e.binds).trans reg
  temp := ((Fin.castLEEmb (by simp) : Fin (e.mapPublic φ).binds ↪ Fin e.binds).trans
    (Fin.natAddEmb 4)).trans reg
  fresh := by
    intro i j equal
    have he := congrArg Fin.val (reg.injective equal)
    change i.val=4+j.val at he
    have := i.isLt
    omega
  exit := exit

def block (e : Term w k 1) (lo n : ℕ) : Block w (6+e.labels) (4+e.binds) k where
  first := (0 : Fin 6).castAdd e.labels
  emit pc reg φ exit j := (linkedFrame e pc reg φ exit).emit lo (lo+n) (j.cast (by simp))

theorem advance_block (e : Term w k 1) (lo n : ℕ) (stop : lo+n<2^w)
    (pc : Fin (6+e.labels) ↪ Fin P) (reg : Fin (4+e.binds) ↪ Fin R)
    (φ : Fin k → Fin K) (exit : Fin P) (M : Machine w P R K)
    (installed : (block e lo n).Installed M pc reg φ exit)
    (c : Config w P R) (m₀ : Memory w) (start : c.pc=pc (block e lo n).first) (word : ℕ → Word w)
    (correct : ∀ (a : Word w) (m : Memory w), lo ≤ a.val → a.val < lo+n →
      agreesOutside lo (lo+n) m m₀ → e.eval (M.publicData ∘ φ) m (fun _ => a) = word a.val) :
    ∃ steps ≤ 4+n*(2*e.binds+4), ∃ out : Config w P R, out.pc=exit ∧
      advance M.program steps c m₀ = some (out,fillSegment lo n word m₀) := by
  let A := linkedFrame e pc reg φ exit
  have rom (i : Fin (6+(e.mapPublic φ).labels)) : M.code (A.pc i)=A.emit lo (lo+n) i := by
    let j : Fin (6+e.labels) := i.cast (by simp)
    have same : j.cast (by simp : 6+e.labels=6+(e.mapPublic φ).labels) = i := Fin.ext rfl
    have hi := installed j
    change M.code (A.pc i)=A.emit lo (lo+n) (j.cast (by simp)) at hi
    rwa [same] at hi
  have begins : c.pc=A.drv 0 := start
  have done : A.exit=exit := rfl
  simpa only [Term.binds_mapPublic,done] using A.advance M lo n stop rom c m₀ begins word
    (fun a m h u untouched => by simpa using correct a m h u untouched)

end ThreeFlat.RAM.PhysicalScan

end OAI
