# Analyse du Document IRIS - Concepts à Formaliser en Lean

## Vue d'ensemble du système IRIS

Le système IRIS (Integrative Resilience Intelligence System) est un écosystème économique fondé sur la **preuve d'acte** plutôt que sur la **promesse de remboursement**. Il transpose les principes de thermodynamique et cybernétique dans le domaine économique.

## Concepts Fondamentaux du Document

### 1. **Grandeurs Économiques**
- **S (Stipulat)** : Preuve d'effort réel, flux éphémère
- **U (Unum)** : Monnaie d'usage périodique, périssable
- **V (Verum)** : Valeur vivante, durable et traçable
- **D (Passif thermométrique)** : Signal de régulation

### 2. **Structures Principales**
- **Oracle d'initialisation** : Migration patrimoniale (conversion actifs réels → actifs numériques)
- **Compte Utilisateur (CU)** : Entité économique élémentaire
  - Wallet : Respiration économique
  - Compte NFT Privé (CNP) : Mémoire patrimoniale
  - Compte Entreprise (CE) : Création de valeur
- **Régulateur Automatique Décentralisé (RAD)** : Homéostasie thermodynamique

### 3. **Mécanismes Clés**

#### Revenu Universel
```
U_t = (1 - ρ_t) × V_on_{t-1} / (T × N_t)
```
- Absence d'émission par la dette
- Distribution effective garantie
- Extinction périodique de U

#### Création de Valeur
```
ΔV_t = η_t × Δt × E_t
E_t = w_S × S_burn + w_U × U_burn
```
- η_t : multiplicateur (0.5 à 2.0)
- Conservation thermodynamique

#### Régulation Thermométrique
```
r_t = D_t / V_t^on
```
- r_t < 0.85 : système froid
- 0.85 ≤ r_t ≤ 1.15 : équilibre
- r_t > 1.15 : surchauffe

## Mapping : Document DOCX ↔ Axiomes Lean Existants

### Axiomes Couverts (A1-A12)

| Axiome | Concept DOCX | Section | Statut |
|--------|-------------|---------|--------|
| A1 | Unicité bijective CU ↔ (TU,VC) | Ch. 2.1.2 | ✅ Couvert |
| A2 | Absence émission dette (RU) | Ch. 2.2.2 | ✅ Couvert |
| A3 | Inviolabilité transactions | Ch. 2.1.2 | ⚠️ À renforcer |
| A4 | Exclusion U entreprise | Ch. 2.3.1 | ✅ Couvert |
| A5 | Stipulat nécessaire | Ch. 2.1.3 | ✅ Couvert |
| A6 | Création valeur énergétique | Ch. 2.1.3 | ✅ Couvert |
| A7 | Absence intérêts | Ch. 2.2.4 | ✅ Couvert |
| A8 | Généalogie complète | - | ✅ Couvert |
| A9 | Médiation CE obligatoire | Ch. 2.3 | ✅ Couvert |
| A10 | Conservation thermodynamique | Ch. 2.1.5 | ⚠️ À étendre |
| A11 | Survie organisationnelle | - | ⚠️ À renforcer |
| A12 | Distribution RU | Ch. 2.2.2 | ✅ Couvert |

## Concepts Manquants à Formaliser

### Catégorie 1 : Oracle et Initialisation

#### A13 - Neutralité énergétique de l'initialisation
**Source** : Ch. 1.1.2
```lean
axiom A13_neutralite_initiale :
  ∀ (système : SystemState),
    système.initialisation_complete →
    (système.V_total_initial = système.D_total_initial)
```

#### A14 - Unicité cryptographique des biens
**Source** : Ch. 1.3.6
```lean
axiom A14_unicite_biens :
  ∀ (bien1 bien2 : ActifReel),
    Hash(bien1) = Hash(bien2) →
    bien1 = bien2
```

### Catégorie 2 : Conversion et Circulation

#### A15 - Conversion V ↔ U régulée
**Source** : Ch. 2.2.3
```lean
axiom A15_conversion_regulee :
  ∀ (V_converti : ℝ) (κ : ℝ),
    0.5 ≤ κ ∧ κ ≤ 2.0 →
    U_obtenu = κ × V_converti
```

#### A16 - Extinction périodique de U
**Source** : Ch. 2.2.2
```lean
axiom A16_extinction_U :
  ∀ (wallet : CompteUtilisateur) (cycle : ℕ),
    fin_de_cycle(cycle) →
    wallet.U_non_depense(cycle) = 0
```

### Catégorie 3 : Stacking (Crédit sans intérêt)

#### A17 - Neutralité énergétique du stacking
**Source** : Ch. 2.2.4
```lean
axiom A17_stacking_neutre :
  ∀ (V_avance D_stack : ℝ),
    contrat_stacking_valide →
    ΔV_avance = ΔD_stack
```

#### A18 - Transférabilité de l'engagement
**Source** : Ch. 2.2.4
```lean
axiom A18_transfert_engagement :
  ∀ (nft : NFT) (stack : Stacking),
    nft.lie_a(stack) →
    transfert(nft) → transfert(stack)
```

### Catégorie 4 : Régulation Thermométrique

#### A19 - Thermomètre global borné
**Source** : Ch. 2.1.5
```lean
axiom A19_thermometre_borne :
  ∀ (système : SystemState),
    let r_t := système.D_total / système.V_on
    système.stable → (0.85 ≤ r_t ∧ r_t ≤ 1.15)
```

#### A20 - Ajustement automatique de η
**Source** : Ch. 2.3.4
```lean
axiom A20_ajustement_eta :
  ∀ (r_t η_t : ℝ),
    (r_t > 1.15 → η_t diminue) ∧
    (r_t < 0.85 → η_t augmente)
```

### Catégorie 5 : Compte Entreprise et TAP

#### A21 - Capacité TAP limitée
**Source** : Ch. 2.3.5
```lean
axiom A21_capacite_TAP :
  ∀ (ce : CompteEntreprise),
    ce.TAP_total ≤ 0.8 × (ce.tresorerie_V + ce.V_financier)
```

#### A22 - Distribution organique 40/60
**Source** : Ch. 2.3.4
```lean
axiom A22_distribution_organique :
  ∀ (ce : CompteEntreprise) (ΔV : ℝ),
    ce.valeur_creee = ΔV →
    ce.collaborateurs_part = 0.4 × ΔV ∧
    ce.tresorerie_part = 0.6 × ΔV
```

### Catégorie 6 : Sécurité et Gouvernance

#### A23 - Résistance aux attaques Sybil
**Source** : Ch. 2.1.2
```lean
axiom A23_anti_sybil :
  ∀ (personne : EtreHumain),
    ∃! (cu : CompteUtilisateur),
      cu.appartient_a(personne)
```

#### A24 - Traçabilité sans surveillance
**Source** : Ch. 2.1.2
```lean
axiom A24_tracabilite_privee :
  ∀ (tx : Transaction),
    tx.empreinte_publique ∧
    ¬tx.montant_visible ∧
    ¬tx.parties_identifiables
```

#### A25 - Limites de rétention entreprise
**Source** : Ch. 2.3.4
```lean
axiom A25_limite_retention :
  ∀ (ce : CompteEntreprise),
    ce.tresorerie_V ≤ 1.2 × moyenne_mobile(ce.V, 3_cycles)
```

### Catégorie 7 : NFT et Patrimoine

#### A26 - Cycle de vie NFT productif
**Source** : Ch. 2.3.2
```lean
axiom A26_cycle_nft_productif :
  ∀ (nft : NFT),
    emission(nft) → validation(nft) →
    combustion(nft) → archivage(nft)
```

#### A27 - Conservation patrimoniale
**Source** : Ch. 2.3.6
```lean
axiom A27_conservation_patrimoine :
  ∀ (système : SystemState),
    système.V_total = système.V_on + système.V_immo
```

## Structures de Données Manquantes

### 1. Oracle et Initialisation
```lean
structure Oracle where
  mode : OracleMode  -- Officiel | AutoIntegratif
  facteur_auth : ℝ
  biens_enregistres : List ActifReel
  h_facteur : 0 ≤ facteur_auth ∧ facteur_auth ≤ 1

structure ActifReel where
  hash_unicite : Hash
  valeur_effective : ℝ
  proprietaire : TU
  h_valeur : 0 ≤ valeur_effective
```

### 2. Stacking et Contrats
```lean
structure Stacking where
  montant_initial : ℝ
  cycles_restants : ℕ
  nft_lie : Hash
  h_montant : 0 < montant_initial

structure ConversionVU where
  V_source : ℝ
  kappa : ℝ
  U_obtenu : ℝ
  h_kappa : 0.5 ≤ kappa ∧ kappa ≤ 2.0
  h_conversion : U_obtenu = kappa * V_source
```

### 3. Régulation Thermométrique
```lean
structure RAD where  -- Régulateur Automatique Décentralisé
  D_total : ℝ
  V_on_total : ℝ
  eta : ℝ
  kappa : ℝ
  h_D : 0 ≤ D_total
  h_V : 0 < V_on_total
  h_eta : 0.5 ≤ eta ∧ eta ≤ 2.0
  h_kappa : 0.5 ≤ kappa ∧ kappa ≤ 2.0

def thermometre (rad : RAD) : ℝ := rad.D_total / rad.V_on_total
```

### 4. Compte Entreprise Enrichi
```lean
structure CompteEntrepriseEtendu extends CompteEntreprise where
  TAP_en_cours : List TAP
  NFT_financiers : List NFT
  collaborateurs : List CompteUtilisateur
  coefficient_confiance : ℝ
  h_confiance : 0 ≤ coefficient_confiance ∧ coefficient_confiance ≤ 2.0

structure TAP where
  montant_avance : ℝ
  echeance : ℕ
  entreprise_emettrice : VC
  h_montant : 0 < montant_avance
```

### 5. Wallet Enrichi
```lean
structure WalletEtendu where
  U_actuel : ℝ
  V_liquide : ℝ
  stackings : List Stacking
  NFT_financiers_detenus : List NFT
  h_U : 0 ≤ U_actuel
  h_V : 0 ≤ V_liquide
```

### 6. État Système Global
```lean
structure SystemState where
  utilisateurs : List CompteUtilisateur
  entreprises : List CompteEntreprise
  V_total : ℝ
  D_total : ℝ
  V_on : ℝ       -- Valeur circulante
  V_immo : ℝ     -- Valeur immobilisée
  cycle_actuel : ℕ
  h_conservation : V_total = V_on + V_immo
  h_V : 0 ≤ V_total
  h_D : 0 ≤ D_total
```

## Théorèmes à Prouver

### Théorèmes de Conservation

#### T1 - Conservation énergétique globale
```lean
theorem T1_conservation_globale :
  ∀ (s1 s2 : SystemState),
    s2 = evolve(s1) →
    s2.V_total + s2.D_total = s1.V_total + s1.D_total + RU_distribue
```

#### T2 - Non-création monétaire
```lean
theorem T2_pas_creation_monetaire :
  ∀ (tx : Transaction),
    tx.validee →
    ∃ (S_burn U_burn : ℝ),
      tx.V_cree = eta × (w_S × S_burn + w_U × U_burn)
```

### Théorèmes de Stabilité

#### T3 - Convergence thermométrique
```lean
theorem T3_convergence_thermometre :
  ∀ (système : SystemState) (ε : ℝ),
    ε > 0 →
    ∃ (n : ℕ),
      ∀ (cycle ≥ n),
        |thermometre(système) - 1.0| < ε
```

#### T4 - État stationnaire atteignable
```lean
theorem T4_etat_stationnaire :
  ∃ (s : SystemState),
    s.V_total = constante ∧
    s.creation_valeur = s.destruction_valeur ∧
    thermometre(s) = 1.0
```

### Théorèmes d'Équité

#### T5 - Non-appauvrissement
```lean
theorem T5_non_appauvrissement :
  ∀ (cu : CompteUtilisateur) (cycle : ℕ),
    cu.actif →
    cu.ressources_totales ≥ RU_minimum
```

#### T6 - Distribution équitable du RU
```lean
theorem T6_distribution_equitable :
  ∀ (cu1 cu2 : CompteUtilisateur),
    cu1.actif ∧ cu2.actif →
    cu1.RU_recu = cu2.RU_recu
```

### Théorèmes de Sécurité

#### T7 - Impossibilité double-dépense
```lean
theorem T7_pas_double_depense :
  ∀ (cu : CompteUtilisateur) (tx1 tx2 : Transaction),
    tx1.montant + tx2.montant > cu.wallet_V →
    ¬(tx1.executee ∧ tx2.executee)
```

#### T8 - Résistance faillite entreprise
```lean
theorem T8_resilience_faillite :
  ∀ (ce : CompteEntreprise),
    ce.faillite →
    ∀ (tap : TAP ∈ ce.TAP_en_cours),
      tap.rembourse_par_reserve
```

### Théorèmes de Résilience

#### T9 - Continuité après défaillance
```lean
theorem T9_continuite_defaillance :
  ∀ (système : SystemState) (entites_defaillantes : List CompteEntreprise),
    card(entites_defaillantes) ≤ 0.1 × card(système.entreprises) →
    système.fonctionnel
```

#### T10 - Homéostasie thermodynamique
```lean
theorem T10_homeostasie :
  ∀ (système : SystemState) (perturbation : ℝ),
    |perturbation| < seuil_critique →
    ∃ (cycles : ℕ),
      après(cycles) → système.retrouve_equilibre
```

## Scénarios de Test Prioritaires

### Test 1 : Cycle complet d'un utilisateur
- Réception RU
- Achat bien avec U
- Stacking d'un actif
- Investissement NFT financier
- Création valeur via CE

### Test 2 : Régulation thermométrique
- Surchauffe (r_t > 1.15) → η diminue
- Refroidissement (r_t < 0.85) → η augmente
- Convergence vers équilibre

### Test 3 : Faillite entreprise
- TAP non remboursé
- Prélèvement sur réserve
- Protection détenteurs NFT financiers

### Test 4 : Attaque Sybil
- Tentative création multiple comptes
- Détection par unicité TU/VC
- Rejet automatique

### Test 5 : Conservation globale
- Tracking V_total + D_total
- Vérification après chaque transaction
- Invariant maintenu

## Priorités de Développement

### Phase 1 (Urgent)
1. A13-A16 : Oracle et conversion
2. T1-T2 : Conservation et non-création monétaire
3. Structures Oracle, RAD, SystemState
4. Tests conservation globale

### Phase 2 (Important)
1. A17-A20 : Stacking et régulation
2. T3-T4 : Stabilité et convergence
3. Structures Stacking, ConversionVU
4. Tests régulation thermométrique

### Phase 3 (Souhaitable)
1. A21-A27 : CE, TAP, NFT
2. T5-T10 : Équité, sécurité, résilience
3. Structures TAP, CompteEntrepriseEtendu
4. Tests scénarios complexes

## Notes Méthodologiques

- **Approche progressive** : Commencer par les axiomes fondamentaux, puis dériver les théorèmes
- **Preuves constructives** : Privilégier les preuves par construction plutôt que par réduction à l'absurde
- **Tests numériques** : Chaque axiome/théorème doit avoir au moins un test avec valeurs concrètes
- **Documentation bilingue** : Commentaires en français avec références au document DOCX

## Références Document DOCX

| Section | Titre | Concepts Clés |
|---------|-------|---------------|
| Ch. 1 | Oracle d'initialisation | Migration patrimoniale, neutralité énergétique |
| Ch. 2.1 | Compte Utilisateur | Architecture tripartite, unicité |
| Ch. 2.2 | Wallet | RU, conversion V↔U, stacking |
| Ch. 2.3 | Compte Entreprise | Création valeur, TAP, distribution 40/60 |
| Ch. 3 (à lire) | Exchange et RAD | Régulation thermométrique |

---
*Document généré automatiquement lors de l'analyse du fichier DOCX IRIS*
*Date : 2025-11-14*
