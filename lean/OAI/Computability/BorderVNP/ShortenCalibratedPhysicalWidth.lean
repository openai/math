import OAI.Computability.BorderVNP.ShortenCompiledPhysicalSource
import OAI.Computability.BorderVNP.ShortenCompiledAt

/-!
# Compiled physical sample traces at an externally supplied word width

Predecessor and successor records can share one public word width across
the full epoch. Every width that accommodates the count bank and scores
yields the calibrated physical trace, with explicit gate costs at that width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Cover.Frame Cover.AddressCircuit Epoch Crossing Packing PreparedBins PackMotions PublicPopulation Hecke
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D n N : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)

/-- The actual cable histogram and the same selector that realizes the calibrated
constant compose with one tile-volume factor per child. The physical trace
decodes the bits of this composite on each admissible classified input. -/
theorem classifiedTraceAtWidth_frames (compiled : CompiledAt.{u} B n N) :
    ∃ P A p C e : ℕ, 0 < P ∧ ∀ (d r k : ℕ) (_ : 0 < d) (_ : 1 ≤ r) (_ : d+1 = r+2*n) (hk : 0 < k)
      {Data : Type*} [Fintype Data] (sites rows nameWidth H w : ℕ) (home : Fin rows → Fin k)
      (field : FieldBit (↥S) (Cube D) (d+1+2*n) → Data),
      let vol := Fintype.card (Cube D → Deck (d+1))
      P < 2^w → H < 2^w → packRunWidth vol P k H ≤ w →
      ∃ (table : Frame (Classified Data (↥B.types) sites rows nameWidth w) (B.SelectionTables n (d+1) w k))
        (selector : Frame (B.SelectionTables n (d+1) w k) (B.SelectionPins n (d+1) w k)),
        (∀ T, rows ≤ T → w ≤ Nat.clog 2 (T+1) →
          (selector.subst table).size ≤ 1+(rows+k*(vol+1))*A*(Nat.clog 2 (T+vol+2)+1)^p +
            (1+k*(vol*C*(d+1+w+1)^e))) ∧
        ∀ {Port : Type} {bits : Port → ℕ} {K : Type u} (child : Fin k → PlacedPack D Port bits K (Cube D) (d+2*n))
          (L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child)),
          (∀ i a, (child i).active a = true → dist ((child i).midpoint a) ((child i).site ((child i).pack.layout.src a)) ≤
            dist ((child i).site ((child i).pack.layout.src a)) ((child i).site ((child i).pack.layout.dst a))/2) →
          ∀ (slot : (parallelPacks (fun i => (child i).pack)).layout.Edge ↪ Fin rows) (_ : ∀ a, home (slot a) = a.1)
            (x : Classified Data (↥B.types) sites rows nameWidth w → Bool),
            PhysicalReads B (factorEnum D) (by omega) field (fun i => (child i).pack) (fun i => (child i).active)
              (childSites child) L slot x →
            (∀ i, (∑ a, (child i).pack.layout.width a) ≤ H) →
            B.PhysicalTrace child L selector (table.eval x) hk N ∧
              (selector.subst table).eval x = selector.eval (table.eval x) := by
  obtain ⟨A,p,tables⟩ := classifiedTablesAtWidth B (factorEnum D) (candidateEnum D n)
  obtain ⟨P,C,e,hP,make⟩ := compiled
  refine ⟨P,A,p,C,e,hP,?_⟩
  intro d r k hd hr level hk Data instData sites rows nameWidth H w home field vol den hH width
  obtain ⟨table,hs,reads⟩ := tables r (d+1) hr level w k sites rows nameWidth home field
  obtain ⟨selector,ht,run⟩ := make d k w hd hk den
  refine ⟨table,selector,?_,?_⟩
  · intro T hrows hw
    rw [Frame.subst_size]
    exact Nat.add_le_add (hs T hrows hw) ht
  · intro Port bits K child L midpoint slot owner x input cap
    obtain ⟨hz,hcount⟩ := reads (fun i => (child i).pack) (fun i => (child i).active) (childSites child)
      L slot owner x input H hH cap
    exact ⟨run child L midpoint (table.eval x) H hz hcount width,funext (Frame.subst_eval selector table x)⟩

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
