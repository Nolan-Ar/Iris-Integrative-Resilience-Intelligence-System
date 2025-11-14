/-
  Théorème des Contrats Clos
  Regroupe plusieurs garanties fondamentales d’IRIS :
  - inviolabilité des transactions,
  - distribution effective du RU,
  - conservation de la valeur.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import IrisAxioms.iris_axioms

open IrisAxioms

namespace IrisTheoremes

/--
Théorème des contrats clos :
simple regroupement de trois axiomes IRIS clés.
-/
theorem contrat_clos :
    -- Inviolabilité des transactions
    (∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx) ∧
    -- Distribution effective du RU
    (∀ (U_t : ℝ) (beneficiaires : List CompteUtilisateur) (alloc : CompteUtilisateur → ℝ),
        (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
        (beneficiaires.attach.map (fun ⟨cu, _⟩ => alloc cu)).sum = U_t) ∧
    -- Conservation de la valeur fondamentale
    (∀ (v : Valeurs), 0 ≤ v.V ∧ 0 ≤ v.D) := by
  constructor
  · exact A3_inviolabilite_transactions
  constructor
  · intro U_t beneficiaires alloc h_pos
    exact A12_distribution_RU U_t beneficiaires alloc h_pos
  · intro v
    exact A10_conservation_thermodynamique v.V v.D

/-- Les transactions sont toujours valides et signées. -/
theorem transactions_toujours_valides :
    ∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx :=
  (contrat_clos).left

/-- Le revenu universel est toujours distribué intégralement. -/
theorem RU_toujours_distribue :
    ∀ (U_t : ℝ) (beneficiaires : List CompteUtilisateur) (alloc : CompteUtilisateur → ℝ),
      (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
      (beneficiaires.attach.map (fun ⟨cu, _⟩ => alloc cu)).sum = U_t :=
  (contrat_clos).right.left

/-- La valeur vivante et le passif D restent non négatifs. -/
theorem valeurs_toujours_positives :
    ∀ (v : Valeurs), 0 ≤ v.V ∧ 0 ≤ v.D :=
  (contrat_clos).right.right

/--
Version étendue qui ajoute deux autres axiomes :
- absence d’émission par la dette,
- exclusion stricte de U des comptes entreprise.
-/
theorem contrat_clos_etendu :
    -- Inviolabilité de base
    (∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx) ∧
    -- Distribution effective
    (∀ (U_t : ℝ) (beneficiaires : List CompteUtilisateur) (alloc : CompteUtilisateur → ℝ),
        (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
        (beneficiaires.attach.map (fun ⟨cu, _⟩ => alloc cu)).sum = U_t) ∧
    -- Conservation fondamentale
    (∀ (v : Valeurs), 0 ≤ v.V ∧ 0 ≤ v.D) ∧
    -- Absence d'émission par dette
    (∀ (U_t V_on ρ : ℝ) (T N : ℕ),
        (0 ≤ ρ ∧ ρ ≤ 0.3) → (0 < T ∧ 0 < N) → 0 ≤ V_on →
        U_t = (1 - ρ) * V_on / ((T : ℝ) * (N : ℝ)) ∧ 0 ≤ U_t) ∧
    -- Exclusion stricte de U pour entreprises
    (∀ (ce : CompteEntreprise), 0 ≤ ce.tresorerie_V) := by
  constructor
  · exact A3_inviolabilite_transactions
  constructor
  · exact A12_distribution_RU
  constructor
  · intro v
    exact A10_conservation_thermodynamique v.V v.D
  constructor
  · exact A2_absence_emission_dette
  · exact A4_exclusion_U_entreprise

end IrisTheoremes

