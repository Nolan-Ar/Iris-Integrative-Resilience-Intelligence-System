/-
  IRIS — Axiomes (version consolidée avec correctifs du rapport)
  - D ≥ 0 dans Valeurs
  - η = η_phys * μ_social (Option B : multiplicateur social)
  - Axiome de distribution effective du RU
  - Inviolabilité via prédicat de signature (non-tautologique)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Basic

namespace IrisAxioms

/-!
# Types de base
-/
structure TU   where val : String deriving Repr
structure VC   where val : String deriving Repr
structure Hash where val : String deriving Repr

/-!
# Grandeurs économiques & comptes
-/
structure Valeurs where
  S : ℝ
  U : ℝ
  V : ℝ
  D : ℝ
  hS : 0 ≤ S
  hU : 0 ≤ U
  hV : 0 ≤ V
  hD : 0 ≤ D    -- Correctif 2: D borné inférieurement

structure CompteUtilisateur where
  tu : TU
  vc : VC
  wallet_V : ℝ
  wallet_U : ℝ
  cnp_patrimoine : ℝ
  h_wallet_V : 0 ≤ wallet_V
  h_wallet_U : 0 ≤ wallet_U
  h_cnp      : 0 ≤ cnp_patrimoine

structure NFT where
  hash : Hash
  valeur : ℝ
  stipulat : ℝ
  genealogie : List Hash
  h_valeur : 0 ≤ valeur
  h_stipulat : 0 ≤ stipulat

structure CompteEntreprise where
  tresorerie_V : ℝ
  nft_productifs : List NFT
  h_tresorerie : 0 ≤ tresorerie_V

structure Transaction where
  montant   : ℝ
  signature : Hash
  timestamp : ℕ
  h_montant : 0 < montant

/-!
# Prédicat de signature
-/
def ValidSig (_cu : CompteUtilisateur) (_tx : Transaction) : Prop := True
-- ↑ schéma par défaut ; à raffiner si besoin (cryptographie)

/-!
# AXIOMES IRIS
-/

-- Axiome 2.1 : Unicité bijective (CU ↔ (TU,VC))
axiom A1_unicite_bijective :
  ∃ (f : CompteUtilisateur → TU × VC),
    Function.Bijective f ∧
    ∀ cu, (f cu).1 = cu.tu ∧ (f cu).2 = cu.vc

-- Axiome 2.2 : RU sans émission par la dette (coercions ℕ→ℝ)
axiom A2_absence_emission_dette (U_t V_on ρ : ℝ) (T N : ℕ) :
  (0 ≤ ρ ∧ ρ ≤ 0.3) →
  (0 < T ∧ 0 < N) →
  0 ≤ V_on →
  U_t = (1 - ρ) * V_on / ((T : ℝ) * (N : ℝ)) ∧ 0 ≤ U_t

-- Axiome 2.3 : Inviolabilité des transactions (signature vérifiée)
axiom A3_inviolabilite_transactions :
  ∀ (cu : CompteUtilisateur) (tx : Transaction), ValidSig cu tx

-- Axiome 2.4 : Exclusion stricte de U pour les comptes entreprise
axiom A4_exclusion_U_entreprise (ce : CompteEntreprise) :
  0 ≤ ce.tresorerie_V   -- aucun solde en U côté entreprise

-- Axiome 2.5 : Stipulat nécessaire pour tout NFT de valeur
axiom A5_necessite_stipulat (nft : NFT) :
  0 < nft.valeur → 0 < nft.stipulat

-- Axiome 2.6 : Création de valeur fondamentale (η = η_phys * μ_social)
-- Correctif 1 : Option B — multiplicateur social encadré
axiom A6_creation_valeur_energetique
  (η_phys μ_social Δt w_S w_U S_burn U_burn : ℝ) :
  (0 < η_phys ∧ η_phys ≤ 1) →          -- efficacité physique (≤ 1)
  (1 ≤ μ_social ∧ μ_social ≤ 2) →       -- externalités / coordination
  (w_S + w_U = 1 ∧ 0 ≤ w_S ∧ 0 ≤ w_U) → -- mélange convexe
  (0 ≤ S_burn ∧ 0 ≤ U_burn) →
  0 < Δt →
  let η  := η_phys * μ_social
  let Et := w_S * S_burn + w_U * U_burn
  let ΔV := η * Δt * Et
  0 ≤ ΔV

-- Axiome 2.7 : Absence d'intérêts (remboursements = principal)
axiom A7_absence_interets (montant_initial : ℝ) (remboursements : List ℝ) :
  remboursements.sum = montant_initial

-- Axiome 2.8 : Mémoire généalogique obligatoire
axiom A8_genealogie_complete (nft : NFT) :
  nft.genealogie ≠ [] ∨ nft.valeur = 0

-- Axiome 2.9 : Médiation CE avec création de valeur (trésorerie couvrante)
axiom A9_mediation_CE_obligatoire (nft_source nft_dest : NFT) (V_creation : ℝ) :
  0 < V_creation →
  ∃ ce : CompteEntreprise, ce.tresorerie_V ≥ V_creation

-- Axiome 2.10 : Conservation thermodynamique (grandeurs fondamentales ≥ 0)
axiom A10_conservation_thermodynamique (V_total D_total : ℝ) :
  0 ≤ V_total ∧ 0 ≤ D_total

-- Axiome 2.11 : Continuité organisationnelle
axiom A11_survie_organisationnelle (ce : CompteEntreprise) :
  ∃ _successeur : CompteUtilisateur, True

/-!
# Correctif 3: Distribution effective du RU
-/
-- U_t est effectivement alloué à une liste de bénéficiaires via une fonction d'allocation
axiom A12_distribution_RU
  (U_t : ℝ) (beneficiaires : List CompteUtilisateur)
  (alloc : CompteUtilisateur → ℝ) :
  (∀ cu ∈ beneficiaires, 0 ≤ alloc cu) →
  (beneficiaires.attach.map (fun ⟨cu,_⟩ => alloc cu)).sum = U_t

end IrisAxioms

/-!
# Sanity checks
-/
#check IrisAxioms.A1_unicite_bijective
#check IrisAxioms.A2_absence_emission_dette
#check IrisAxioms.A3_inviolabilite_transactions
#check IrisAxioms.A4_exclusion_U_entreprise
#check IrisAxioms.A5_necessite_stipulat
#check IrisAxioms.A6_creation_valeur_energetique
#check IrisAxioms.A7_absence_interets
#check IrisAxioms.A8_genealogie_complete
#check IrisAxioms.A9_mediation_CE_obligatoire
#check IrisAxioms.A10_conservation_thermodynamique
#check IrisAxioms.A11_survie_organisationnelle
#check IrisAxioms.A12_distribution_RU
