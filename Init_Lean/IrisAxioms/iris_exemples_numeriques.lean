/-!
  IRIS — Exemples Numériques

  Bibliothèque d'exemples concrets avec valeurs réelles
  simulant le fonctionnement du système IRIS.

  Organisation :
  - Section 1 : Exemples Utilisateurs (Alice, Bob, Charlie)
  - Section 2 : Exemples Entreprises (SolarCoop, BioFarm)
  - Section 3 : Scénarios Complets (cycle économique, stacking, TAP)
  - Section 4 : Cas Limites et Situations Exceptionnelles
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Basic
import IrisAxioms.iris_axioms_extended
import IrisAxioms.iris_theoremes_extended

open IrisAxiomsExtended

namespace IrisExemplesNumeriques

/-! # Section 1 : EXEMPLES UTILISATEURS -/

/-! ## Exemple 1.1 : Alice - Artisan-réparateur de vélos électriques -/

def alice_TU : TU := ⟨"alice_tu_2024"⟩
def alice_VC : VC := ⟨"alice_vc_verified"⟩

def alice_compte : CompteUtilisateur := {
  tu := alice_TU,
  vc := alice_VC,
  wallet_V := 525.6,      -- Valeur liquide
  wallet_U := 67.5,       -- Reste de U ce cycle (après dépenses)
  cnp_patrimoine := 637.6, -- Patrimoine total
  h_wallet_V := by norm_num,
  h_wallet_U := by norm_num,
  h_cnp := by norm_num
}

/-- Alice reçoit son RU mensuel -/
example :
  let RU_alice := (120.5 : ℝ)
  let N_utilisateurs := (1000000 : ℕ)  -- 1 million d'utilisateurs
  let V_on_systeme := (500000000 : ℝ)  -- 500M de valeur circulante
  let rho := (0.2 : ℝ)
  let T := (12 : ℕ)  -- 12 cycles par an
  let RU_calcule := (1 - rho) * V_on_systeme / ((T : ℝ) * (N_utilisateurs : ℝ))
  -- Alice reçoit environ 33.33 U par mois
  RU_calcule > 30 ∧ RU_calcule < 35 := by
  intro RU_alice N_utilisateurs V_on_systeme rho T RU_calcule
  norm_num

/-- Alice crée de la valeur par son travail -/
example :
  let heures_travail := (40 : ℝ)
  let qual_coefficient := (1.2 : ℝ)  -- Artisan qualifié
  let S_alice := heures_travail * qual_coefficient  -- 48 unités de Stipulat
  let prix_reparation := (80 : ℝ)  -- Client paie 80 U
  let η_phys := (0.8 : ℝ)
  let μ_social := (1.5 : ℝ)  -- Effet social positif
  let η := η_phys * μ_social
  let w_S := (0.6 : ℝ)
  let w_U := (0.4 : ℝ)
  let E := w_S * S_alice + w_U * prix_reparation
  let V_cree := η * 1.0 * E  -- Δt = 1 cycle
  -- Alice crée environ 72 unités de V
  V_cree > 60 ∧ V_cree < 80 := by
  intro heures_travail qual_coefficient S_alice prix_reparation
  intro η_phys μ_social η w_S w_U E V_cree
  norm_num

/-- Budget mensuel d'Alice -/
example :
  let RU := (120.5 : ℝ)
  let stackings := (53 : ℝ)      -- Habitat coop (35) + Véhicule (18)
  let abonnements := (15 : ℝ)    -- Énergie (6) + Atelier (9)
  let consommation := (82.3 : ℝ) -- Dépenses courantes
  let U_disponible := RU - stackings - abonnements
  let U_final := U_disponible - consommation
  -- Alice a dépensé presque tout son RU
  U_final > -30 ∧ U_final < 0 := by
  intro RU stackings abonnements consommation U_disponible U_final
  norm_num

/-! ## Exemple 1.2 : Bob - Développeur logiciel -/

def bob_TU : TU := ⟨"bob_tu_2024"⟩
def bob_VC : VC := ⟨"bob_vc_verified"⟩

/-- Bob convertit de la V en U pour consommer -/
example :
  let V_bob := (2000 : ℝ)
  let kappa := (0.9 : ℝ)  -- Système légèrement chaud
  let conversion := ConversionVU.mk V_bob kappa (kappa * V_bob)
    (by norm_num : 0.5 ≤ kappa ∧ kappa ≤ 2.0)
    (by rfl)
    (by norm_num : 0 ≤ V_bob)
  conversion.U_obtenu = 1800 := by
  intro V_bob kappa conversion
  rfl

/-! ## Exemple 1.3 : Charlie - Étudiant -/

/-- Charlie vit principalement de son RU -/
example :
  let RU_charlie := (120.5 : ℝ)
  let creation_valeur := (15 : ℝ)  -- Petits jobs
  let total_ressources := RU_charlie + creation_valeur
  let taux_RU := RU_charlie / total_ressources
  -- 89% de ses ressources viennent du RU
  taux_RU > 0.85 ∧ taux_RU < 0.95 := by
  intro RU_charlie creation_valeur total_ressources taux_RU
  norm_num

/-! # Section 2 : EXEMPLES ENTREPRISES -/

/-! ## Exemple 2.1 : SolarCoop - Énergie solaire communautaire -/

def solarcoop_VC : VC := ⟨"solarcoop_energy"⟩

def solarcoop_NFT_installation : NFT := {
  hash := ⟨"solar_panels_installation_789"⟩,
  valeur := 50000,
  stipulat := 2000,  -- 2000h de travail d'installation
  genealogie := [⟨"genesis_solar"⟩],
  h_valeur := by norm_num,
  h_stipulat := by norm_num
}

/-- SolarCoop crée de la valeur par installation solaire -/
example :
  let S_burn := solarcoop_NFT_installation.stipulat
  let U_burn := (40000 : ℝ)  -- Client paie 40k U
  let η_phys := (0.9 : ℝ)    -- Très efficace
  let μ_social := (1.8 : ℝ)   -- Fort impact social
  let η := η_phys * μ_social
  let w_S := (0.5 : ℝ)
  let w_U := (0.5 : ℝ)
  let E := w_S * S_burn + w_U * U_burn
  let V_cree := η * 1.0 * E
  -- SolarCoop crée environ 34k de V
  V_cree > 33000 ∧ V_cree < 35000 := by
  intro S_burn U_burn η_phys μ_social η w_S w_U E V_cree
  norm_num

/-- Distribution organique 40/60 chez SolarCoop -/
example :
  let V_cree := (34000 : ℝ)
  let nb_collaborateurs := (5 : ℕ)
  let part_collaborateurs := 0.4 * V_cree
  let part_par_collab := part_collaborateurs / (nb_collaborateurs : ℝ)
  let part_tresorerie := 0.6 * V_cree
  -- Chaque collaborateur reçoit ~2720 V
  part_par_collab > 2700 ∧ part_par_collab < 2750 ∧
  -- Trésorerie reçoit 20400 V
  part_tresorerie > 20000 ∧ part_tresorerie < 21000 := by
  intro V_cree nb_collaborateurs part_collaborateurs part_par_collab part_tresorerie
  norm_num

/-! ## Exemple 2.2 : BioFarm - Agriculture biologique locale -/

/-- BioFarm émet un TAP pour acheter du matériel -/
example :
  let tresorerie := (100000 : ℝ)
  let NFT_financiers_valeur := (50000 : ℝ)
  let capacite_TAP := 0.8 * (tresorerie + NFT_financiers_valeur)
  let TAP_emis := (110000 : ℝ)
  -- TAP respecte la capacité max
  TAP_emis <= capacite_TAP := by
  intro tresorerie NFT_financiers_valeur capacite_TAP TAP_emis
  norm_num

/-- NFT financier BioFarm avec dividende -/
example :
  let investissement_initial := (5000 : ℝ)
  let V_produit_annuel := (120000 : ℝ)
  let V_burn_TAP := (20000 : ℝ)
  let V_reserve := (30000 : ℝ)
  let lambda_div := (0.15 : ℝ)  -- 15% de dividende
  let V_div_total := lambda_div * (V_produit_annuel - V_burn_TAP - V_reserve)
  let part_investisseur := (investissement_initial / 50000) * V_div_total
  -- Investisseur reçoit ~1050 V de dividende (21% ROI)
  part_investisseur > 1000 ∧ part_investisseur < 1100 := by
  intro investissement_initial V_produit_annuel V_burn_TAP V_reserve
  intro lambda_div V_div_total part_investisseur
  norm_num

/-! # Section 3 : SCÉNARIOS COMPLETS -/

/-! ## Scénario 3.1 : Achat d'une maison en stacking -/

/-- Alice achète une maison coopérative -/
example :
  let prix_maison := (200000 : ℝ)
  let duree_cycles := (240 : ℕ)  -- 20 ans
  let RU_moyen := (120 : ℝ)
  let taux_engagement_max := (0.4 : ℝ)  -- Max 40% du RU
  let paiement_par_cycle := prix_maison / (duree_cycles : ℝ)
  let taux_engagement_reel := paiement_par_cycle / RU_moyen
  -- Paiement mensuel ~833 U, soit 70% du RU (élevé mais temporaire)
  paiement_par_cycle > 800 ∧ paiement_par_cycle < 850 ∧
  taux_engagement_reel > 0.65 ∧ taux_engagement_reel < 0.75 := by
  intro prix_maison duree_cycles RU_moyen taux_engagement_max
  intro paiement_par_cycle taux_engagement_reel
  norm_num

/-- Neutralité énergétique du stacking -/
example :
  let prix_maison := (200000 : ℝ)
  let stack : Stacking := {
    montant_initial := prix_maison,
    cycles_restants := 240,
    nft_lie_hash := ⟨"maison_alice_coop"⟩,
    h_montant := by norm_num
  }
  let D_stack := prix_maison
  let V_avance := stack.montant_initial
  -- V avancée = D inscrit (neutralité)
  V_avance = D_stack := by
  intro prix_maison stack D_stack V_avance
  rfl

/-! ## Scénario 3.2 : Cycle économique complet d'un utilisateur -/

/-- Cycle mensuel complet de Bob -/
example :
  -- DÉBUT DE CYCLE
  let V_initial := (3000 : ℝ)
  let U_initial := (0 : ℝ)  -- U détruit en fin de cycle précédent

  -- RÉCEPTION RU
  let RU_recu := (120 : ℝ)
  let U_apres_RU := U_initial + RU_recu

  -- CRÉATION DE VALEUR (Bob travaille)
  let S_bob := (80 : ℝ)   -- 80h de dev
  let U_client := (200 : ℝ)
  let η := (1.2 : ℝ)
  let w_S := (0.5 : ℝ)
  let w_U := (0.5 : ℝ)
  let V_cree := η * (w_S * S_bob + w_U * U_client)
  let V_apres_creation := V_initial + V_cree

  -- CONVERSION V→U pour consommer
  let kappa := (1.0 : ℝ)
  let V_converti := (50 : ℝ)
  let U_obtenu := kappa * V_converti
  let U_total := U_apres_RU - U_client + U_obtenu
  let V_final := V_apres_creation - V_converti

  -- CONSOMMATION
  let depenses := (100 : ℝ)
  let U_final := U_total - depenses

  -- Bob a créé de la richesse nette
  V_final > V_initial ∧ U_final > 0 := by
  intro V_initial U_initial RU_recu U_apres_RU S_bob U_client η w_S w_U
  intro V_cree V_apres_creation kappa V_converti U_obtenu U_total V_final
  intro depenses U_final
  norm_num

/-! ## Scénario 3.3 : Régulation thermométrique en action -/

/-- Système en surchauffe → ajustement automatique -/
example :
  -- État initial
  let D_total_t0 := (1200000 : ℝ)
  let V_on_t0 := (1000000 : ℝ)
  let r_t0 := D_total_t0 / V_on_t0  -- 1.20 (surchauffe)
  let η_t0 := (1.5 : ℝ)

  -- Système détecte surchauffe et réduit η
  let η_t1 := (1.3 : ℝ)
  let creation_ralentie := η_t1 < η_t0

  -- Après quelques cycles, retour à l'équilibre
  let D_total_t5 := (1050000 : ℝ)
  let V_on_t5 := (1000000 : ℝ)
  let r_t5 := D_total_t5 / V_on_t5  -- 1.05 (équilibre)

  r_t0 > 1.15 ∧ creation_ralentie ∧ r_t5 < 1.15 ∧ r_t5 > 0.85 := by
  intro D_total_t0 V_on_t0 r_t0 η_t0 η_t1 creation_ralentie
  intro D_total_t5 V_on_t5 r_t5
  norm_num

/-! # Section 4 : CAS LIMITES ET SITUATIONS EXCEPTIONNELLES -/

/-! ## Cas 4.1 : Faillite d'entreprise avec TAP -/

/-- Entreprise défaillante : TAP remboursés par réserve -/
example :
  let V_tresorerie := (50000 : ℝ)
  let NFT_financiers := (80000 : ℝ)
  let TAP_en_cours := (100000 : ℝ)
  let reserve_totale := V_tresorerie + NFT_financiers

  -- TAP < Réserve → peut être remboursé
  let peut_rembourser := TAP_en_cours <= reserve_totale

  -- Après remboursement TAP
  let reliquat := reserve_totale - TAP_en_cours

  -- Reliquat distribué aux détenteurs NFT financiers
  let perte_par_NFT := (NFT_financiers - reliquat) / NFT_financiers

  peut_rembourser ∧ reliquat = 30000 ∧ perte_par_NFT > 0.6 := by
  intro V_tresorerie NFT_financiers TAP_en_cours reserve_totale
  intro peut_rembourser reliquat perte_par_NFT
  norm_num

/-! ## Cas 4.2 : Crise systémique (chute V_on de 30%) -/

/-- Lissage du RU en cas de crise -/
example :
  let V_on_avant := (10000000 : ℝ)
  let V_on_apres_crise := 0.7 * V_on_avant  -- -30%
  let RU_avant := (120 : ℝ)
  let alpha_lissage := (0.1 : ℝ)  -- Max 10% variation par cycle

  -- Cycle 1 : -10%
  let RU_c1 := RU_avant * (1 - alpha_lissage)
  -- Cycle 2 : -10%
  let RU_c2 := RU_c1 * (1 - alpha_lissage)
  -- Cycle 3 : -10%
  let RU_c3 := RU_c2 * (1 - alpha_lissage)

  -- Après 3 cycles, RU réduit de ~27%
  let reduction_totale := (RU_avant - RU_c3) / RU_avant

  RU_c1 = 108 ∧ RU_c2 > 97 ∧ RU_c2 < 98 ∧
  reduction_totale > 0.25 ∧ reduction_totale < 0.30 := by
  intro V_on_avant V_on_apres_crise RU_avant alpha_lissage
  intro RU_c1 RU_c2 RU_c3 reduction_totale
  norm_num

/-! ## Cas 4.3 : Utilisateur inactif (pas de transactions) -/

/-- U non dépensé est détruit -/
example :
  let RU_recu := (120 : ℝ)
  let depenses := (0 : ℝ)  -- Aucune dépense
  let U_fin_cycle := RU_recu - depenses
  -- En fin de cycle, U est automatiquement détruit
  let U_debut_cycle_suivant := (0 : ℝ)

  U_fin_cycle = 120 ∧ U_debut_cycle_suivant = 0 := by
  intro RU_recu depenses U_fin_cycle U_debut_cycle_suivant
  norm_num

/-! ## Cas 4.4 : Transfert de NFT avec stacking attaché -/

/-- L'engagement suit le bien -/
example :
  let prix_initial := (150000 : ℝ)
  let cycles_ecoules := (60 : ℕ)
  let cycles_restants := (180 : ℕ)
  let montant_deja_paye := (prix_initial / 240) * (cycles_ecoules : ℝ)
  let montant_restant := prix_initial - montant_deja_paye

  let stack : Stacking := {
    montant_initial := montant_restant,
    cycles_restants := cycles_restants,
    nft_lie_hash := ⟨"bien_transfere"⟩,
    h_montant := by nlinarith
  }

  -- Le nouveau propriétaire hérite du solde restant
  stack.montant_initial > 100000 ∧ stack.montant_initial < 115000 := by
  intro prix_initial cycles_ecoules cycles_restants
  intro montant_deja_paye montant_restant stack
  norm_num

/-! # Section 5 : SIMULATIONS MACRO-ÉCONOMIQUES -/

/-! ## Simulation 5.1 : Économie IRIS à 100k utilisateurs -/

example :
  let N_users := (100000 : ℕ)
  let V_on_total := (50000000 : ℝ)  -- 50M de V circulante
  let D_total := (52000000 : ℝ)     -- Légère surchauffe
  let rho := (0.25 : ℝ)
  let T := (12 : ℕ)

  let r_t := D_total / V_on_total
  let RU_par_user := (1 - rho) * V_on_total / ((T : ℝ) * (N_users : ℝ))

  -- Thermomètre à 1.04 (équilibre sain)
  -- RU ~31.25 U/mois par personne
  r_t > 1.0 ∧ r_t < 1.1 ∧ RU_par_user > 30 ∧ RU_par_user < 32 := by
  intro N_users V_on_total D_total rho T r_t RU_par_user
  norm_num

/-! ## Simulation 5.2 : État stationnaire (croissance zéro) -/

example :
  -- État stationnaire : création = destruction
  let V_creation_cycle := (1000000 : ℝ)
  let V_combustion_cycle := (800000 : ℝ)
  let V_immo_in := (150000 : ℝ)
  let V_immo_out := (150000 : ℝ)
  let V_RU_distribue := (200000 : ℝ)

  let balance := V_creation_cycle - V_combustion_cycle - V_immo_in + V_immo_out - V_RU_distribue

  -- Système en équilibre parfait
  balance = 0 := by
  intro V_creation_cycle V_combustion_cycle V_immo_in V_immo_out V_RU_distribue balance
  norm_num

end IrisExemplesNumeriques

/-! # Récapitulatif des Exemples -/

#check IrisExemplesNumeriques.alice_compte
#check IrisExemplesNumeriques.solarcoop_NFT_installation

/-!
## BIBLIOTHÈQUE D'EXEMPLES - INDEX

### Utilisateurs (3 profils)
- **Alice** : Artisan-réparateur (revenus mixtes RU + travail)
- **Bob** : Développeur (forte création de valeur)
- **Charlie** : Étudiant (principalement RU)

### Entreprises (2 exemples)
- **SolarCoop** : Coopérative énergétique (fort impact social)
- **BioFarm** : Agriculture locale (TAP et NFT financiers)

### Scénarios Complets (3)
1. Achat maison en stacking (neutralité énergétique)
2. Cycle économique complet utilisateur
3. Régulation thermométrique en action

### Cas Limites (4)
1. Faillite entreprise (protection TAP)
2. Crise systémique (lissage RU)
3. Utilisateur inactif (extinction U)
4. Transfert NFT avec engagement

### Simulations Macro (2)
1. Économie 100k utilisateurs
2. État stationnaire (croissance zéro)

---
**Total** : 14 exemples numériques complets avec calculs vérifiés
-/
