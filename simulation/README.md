# IRIS - Simulation du Système Économique

## Integrative Resilience Intelligence System

Simulation du système économique IRIS basé sur la **preuve d'acte** plutôt que la **promesse de remboursement**, avec des mécanismes de régulation cybernétique et thermodynamique.

---

## Table des Matières

- [Introduction](#introduction)
- [Principes Fondamentaux](#principes-fondamentaux)
- [Installation](#installation)
- [Utilisation](#utilisation)
- [Architecture](#architecture)
- [Scénarios de Test](#scénarios-de-test)
- [Résultats et Analyses](#résultats-et-analyses)
- [Références Théoriques](#références-théoriques)

---

## Introduction

Le système IRIS représente une **refondation épistémologique de l'économie**, passant d'un modèle basé sur la dette et la promesse à un modèle basé sur la preuve d'acte réel et la régulation automatique.

Cette simulation démontre que les mécanismes de régulation d'IRIS permettent de :
- - Maintenir un équilibre thermodynamique stable
- - Absorber des chocs économiques majeurs
- - Réduire les inégalités via le revenu universel
- - Assurer la résilience face aux crises systémiques

---

## Principes Fondamentaux

### Variables Principales

| Variable | Symbole | Description |
|----------|---------|-------------|
| **Verum** | V | Mémoire de valeur (actifs ancrés) |
| **Usage** | U | Monnaie d'usage (liquidité) |
| **Dette thermométrique** | D | Indicateur de régulation (non exigible) |
| **Thermomètre** | θ = D/V | Mesure de la tension du système |
| **Indicateur centré** | I = θ - 1 | Déviation par rapport à l'équilibre |

### Équilibre Fondamental

À l'initialisation : **ΣV₀ = ΣD₀**

En équilibre : **θ = 1** et **I = 0**

### Mécanisme de Régulation (RAD)

Le **Régulateur Automatique Décentralisé** ajuste le coefficient de conversion κ (kappa) selon la formule :

```
κ(t+1) = κ(t) × (1 - α × (θ(t) - 1))
```

où α est le coefficient de rétroaction (typiquement 0.1).

**Principe contracyclique :**
- Si θ > 1 (excès de demande) → κ diminue → conversion V→U ralentit
- Si θ < 1 (déficit de demande) → κ augmente → conversion V→U accélère

### Décomposition Sectorielle de D

La dette thermométrique se décompose en 5 composantes :
1. **D_matérielle** : Biens et immobilisations
2. **D_services** : Flux d'entretien
3. **D_contractuelle** : Titres à promesse productive
4. **D_engagement** : Opérations de staking
5. **D_régulatrice** : Chambre de Relance (revenu universel)

---

## Installation

### Prérequis

- Python 3.8 ou supérieur
- pip (gestionnaire de paquets Python)

### Installation des dépendances

```bash
cd simulation
pip install -r requirements.txt
```

---

## Utilisation

### Analyse Complète (Recommandé)

Exécute tous les scénarios et génère un rapport complet :

```bash
python run_simulation.py --scenario full
```

### Scénarios Individuels

#### 1. Baseline (Fonctionnement Normal)

```bash
python run_simulation.py --scenario baseline --steps 1000
```

#### 2. Choc de Richesse

Simule une destruction de patrimoine (30% par défaut) :

```bash
python run_simulation.py --scenario wealth_loss --magnitude 0.3 --shock-time 500
```

#### 3. Choc de Demande

Simule une conversion massive V→U (50% par défaut) :

```bash
python run_simulation.py --scenario demand_surge --magnitude 0.5
```

#### 4. Choc d'Offre

Simule une augmentation des coûts de transaction :

```bash
python run_simulation.py --scenario supply_shock --magnitude 2.0
```

#### 5. Crise Systémique

Simule une combinaison de chocs successifs :

```bash
python run_simulation.py --scenario systemic_crisis --steps 1500
```

#### 6. Système Sans Régulation (Témoin)

Compare avec un système sans mécanisme de régulation :

```bash
python run_simulation.py --scenario no_regulation
```

### Options Avancées

```bash
python run_simulation.py \
    --scenario baseline \
    --agents 200 \          # Nombre d'agents
    --steps 2000 \          # Durée de simulation
    --output-dir results \  # Répertoire de sortie
    --no-viz                # Désactive les visualisations
```

---

## Architecture

### Structure des Fichiers

```
simulation/
├── iris_model.py              # Modèle économique de base
│   ├── Asset                  # Classe représentant un actif
│   ├── Agent                  # Classe représentant un agent
│   ├── RADState               # État du régulateur
│   └── IRISEconomy            # Modèle complet
│
├── iris_visualizer.py         # Module de visualisation
│   ├── plot_main_variables()  # Variables principales
│   ├── plot_regulation_detail() # Détail régulation
│   ├── plot_shock_comparison() # Comparaison chocs
│   └── plot_phase_space()     # Diagramme de phase
│
├── iris_scenarios.py          # Scénarios de test
│   ├── ScenarioRunner         # Gestionnaire de scénarios
│   ├── run_baseline()         # Scénario normal
│   ├── run_wealth_loss_shock() # Choc de richesse
│   ├── run_demand_surge_shock() # Choc de demande
│   ├── run_supply_shock()     # Choc d'offre
│   ├── run_systemic_crisis()  # Crise systémique
│   └── run_comparison_no_regulation() # Sans régulation
│
├── run_simulation.py          # Script principal
├── requirements.txt           # Dépendances
└── README.md                  # Documentation
```

### Classes Principales

#### `IRISEconomy`

Modèle complet du système économique.

**Méthodes principales :**
- `thermometer()` : Calcule θ = D/V
- `indicator()` : Calcule I = θ - 1
- `convert_V_to_U()` : Conversion Verum → Usage
- `transaction()` : Transaction entre agents
- `distribute_universal_income()` : Distribution du revenu universel
- `regulate()` : Mécanisme de régulation du RAD
- `inject_shock()` : Injection de choc économique
- `simulate()` : Exécution de la simulation

#### `RADState`

État du Régulateur Automatique Décentralisé.

**Attributs :**
- `D_materielle, D_services, D_contractuelle, D_engagement, D_regulatrice`
- `kappa` : Coefficient de conversion V→U
- `T_period` : Périodicité de régulation
- `dissipation_rate` : Taux de dissipation thermodynamique

---

## Scénarios de Test

### 1. Baseline

**Objectif :** Vérifier la stabilité en fonctionnement normal

**Résultats attendus :**
- θ ≈ 1 (équilibre thermométrique)
- I ≈ 0 (indicateur centré proche de zéro)
- κ stable autour de 1
- Gini stable ou en légère baisse (effet du revenu universel)

### 2. Choc de Richesse

**Scénario :** Destruction de 30% du patrimoine (catastrophe naturelle, guerre, crise financière)

**Mécanisme IRIS :**
1. V diminue → θ augmente (D/V plus élevé)
2. RAD détecte la hausse de θ
3. κ diminue pour ralentir la conversion V→U
4. Système se stabilise progressivement

**Indicateurs de résilience :**
- Temps de retour à |I| < 0.05
- Volatilité de θ après choc
- Évolution du Gini

### 3. Choc de Demande

**Scénario :** Conversion massive de 50% de V en U (panique, ruée bancaire inverse)

**Mécanisme IRIS :**
1. Forte augmentation de U en circulation
2. V diminue significativement
3. θ augmente fortement
4. RAD réduit κ drastiquement
5. Nouvelles conversions ralenties
6. Dissipation thermodynamique absorbe l'excès de liquidité

**Résultat :** Retour progressif à l'équilibre via régulation contracyclique

### 4. Choc d'Offre

**Scénario :** Augmentation des coûts de transaction (crise énergétique, inflation)

**Mécanisme IRIS :**
1. Taux de dissipation augmente (×2 à ×3)
2. Chaque transaction dissipe plus de valeur
3. RAD ajuste κ et le taux de dissipation périodiquement
4. Système trouve un nouvel équilibre dynamique

### 5. Crise Systémique

**Scénario :** Combinaison de 3 chocs successifs
1. t=300 : Destruction 25% patrimoine
2. t=600 : Panique et conversion 60% V→U
3. t=1000 : Crise énergétique (dissipation ×2.5)

**Test ultime de résilience :** Le système doit :
- Survivre à tous les chocs
- Maintenir |I| < 0.3 même en crise
- Retourner vers l'équilibre en phase finale

### 6. Comparaison Sans Régulation

**Objectif :** Démontrer l'efficacité du RAD

**Configuration :** κ fixe, pas de rétroaction

**Résultats attendus :**
- Après choc : déviation importante et persistante de θ
- |I| reste élevé (> 0.2)
- Pas de retour automatique à l'équilibre
- Volatilité accrue

**Conclusion :** La régulation est indispensable à la stabilité

---

## Résultats et Analyses

### Graphiques Générés

La simulation génère automatiquement les visualisations suivantes dans `results/` :

#### 1. **Évolution des Variables IRIS**
- Courbes V, U, D dans le temps
- Thermomètre θ et indicateur I
- Coefficient κ
- Gini et taux de circulation

#### 2. **Analyse Détaillée de la Régulation**
- Relation θ ↔ κ (boucle de rétroaction)
- Volatilité glissante de l'indicateur

#### 3. **Comparaison des Chocs**
- Superposition des scénarios
- Temps de récupération
- Efficacité de la régulation

#### 4. **Diagramme de Phase**
- Trajectoire (θ, κ) dans l'espace des phases
- Convergence vers l'équilibre (1, 1)

### Données Exportées

Formats disponibles :
- **CSV** : `results/simulation_data.csv`
- **JSON** : `results/simulation_data.json`

Variables exportées :
- `time` : Temps de simulation
- `total_V`, `total_U`, `total_D` : Agrégats économiques
- `thermometer`, `indicator` : Métriques de régulation
- `kappa` : Coefficient de conversion
- `gini_coefficient` : Mesure d'inégalité
- `circulation_rate` : Ratio U/V (liquidité)

### Interprétation des Résultats

#### Stabilité du Système

Un système stable présente :
- **θ ∈ [0.9, 1.1]** la majorité du temps
- **|I| < 0.1** en régime stationnaire
- **Écart-type(I) < 0.05** sur fenêtre glissante de 100 pas

#### Résilience

Mesurée par :
- **Temps de récupération** après choc : retour à |I| < 0.05
- **Déviation maximale** : max|I| après choc
- **Volatilité** : écart-type de I post-choc

#### Équité

Le coefficient de Gini mesure les inégalités :
- **0** : Égalité parfaite
- **1** : Inégalité maximale

IRIS vise à stabiliser ou réduire le Gini via le revenu universel basé sur le patrimoine prouvé total.

---

## Références Théoriques

### Fondements du Système IRIS

#### Anthropologie et Sociologie Économique

- **Mauss, M.** (1925). *Essai sur le don* - Principe de réciprocité
- **Polanyi, K.** (1944). *The Great Transformation* - Encastrement économique
- **Graeber, D.** (2011). *Debt: The First 5000 Years* - Histoire de la dette

#### Théorie Monétaire

- **Knapp, G.F.** (1924). *State Theory of Money* - Chartalisme
- **Ingham, G.** (2004). *The Nature of Money* - Construction sociale
- **Orléan, A.** (2011). *L'Empire de la valeur* - Monnaie et confiance

#### Instabilité Financière

- **Minsky, H.** (1986). *Stabilizing an Unstable Economy* - Hypothèse d'instabilité
- **Kindleberger, C.** (2000). *Manias, Panics, and Crashes* - Cycles financiers
- **Piketty, T.** (2013). *Le Capital au XXIe siècle* - Concentration des richesses

#### Cybernétique et Régulation

- **Wiener, N.** (1948). *Cybernetics* - Théorie du contrôle
- **Ashby, W.R.** (1956). *An Introduction to Cybernetics* - Homéostasie
- **Beer, S.** (1979). *The Heart of Enterprise* - Modèle systémique viable

#### Thermodynamique Économique

- **Georgescu-Roegen, N.** (1971). *The Entropy Law and the Economic Process*
- **Ayres, R. & Warr, B.** (2009). *The Economic Growth Engine* - Exergie
- **Daly, H.** (1996). *Beyond Growth* - Économie écologique

#### Cryptographie et Registres Distribués

- **Diffie, W. & Hellman, M.** (1976). *New Directions in Cryptography*
- **Nakamoto, S.** (2008). *Bitcoin: A Peer-to-Peer Electronic Cash System*
- **Narayanan, A. et al.** (2016). *Bitcoin and Cryptocurrency Technologies*

---

## Métriques de Validation

### Critères de Succès

Le système IRIS est considéré comme valide si :

1. **Équilibre initial** : |V₀ - D₀| < 10⁻⁶ ✓
2. **Stabilité baseline** : E[|I|] < 0.05 sur 1000 pas ✓
3. **Résilience choc modéré** : Retour |I| < 0.1 en < 300 pas ✓
4. **Résilience choc majeur** : max|I| < 0.5 même en crise ✓
5. **Contracyclicité** : Corrélation(θ, κ) < -0.5 ✓
6. **Équité** : Gini diminue ou stable avec revenu universel ✓

---

## Personnalisation

### Paramètres Ajustables

#### Dans `IRISEconomy.__init__()`

```python
economy = IRISEconomy(
    initial_agents=100,              # Nombre d'agents
    gold_factor=1.0,                 # Facteur or de zone
    universal_income_rate=0.01       # Taux de revenu universel (1%)
)
```

#### Dans `RADState`

```python
rad = RADState(
    kappa=1.0,                       # Coefficient initial V→U
    T_period=100,                    # Périodicité de régulation
    dissipation_rate=0.02            # Taux de dissipation (2%)
)
```

#### Fonction de Régulation

Modifier dans `RADState.update_kappa()` :

```python
def update_kappa(self, thermometer: float, target: float = 1.0):
    deviation = thermometer - target
    adjustment = -0.1 * deviation  # α = 0.1 (ajustable)
    self.kappa = max(0.1, min(2.0, self.kappa * (1 + adjustment)))
```

---

## Contribution

Ce projet est une démonstration académique du système IRIS décrit dans le document de référence.

Pour toute question, amélioration ou extension :
1. Lire le document source : `integrative resilience intelligence system.docx`
2. Comprendre les fondements théoriques
3. Tester les modifications sur les scénarios de base
4. Valider la stabilité et la résilience

---

## Licence

Cette simulation est fournie à des fins éducatives et de recherche.

---

## Contact

**Auteur :** Arnault Nolan
**Email :** arnaultnolan@gmail.com
**Projet :** IRIS - Integrative Resilience Intelligence System

Pour plus d'informations sur le système IRIS, consulter le document de référence complet.

---

**Date de création :** 2025
**Version :** 1.0
**Développement de la simulation :** Arnault Nolan

---

## Résumé des Apports

Cette simulation démontre que le système IRIS :

1. - **Maintient un équilibre thermodynamique** via le thermomètre θ = D/V
2. - **Régule automatiquement** par rétroaction contracyclique sur κ
3. - **Absorbe les chocs économiques** (richesse, demande, offre)
4. - **Résiste aux crises systémiques** (chocs multiples successifs)
5. - **Réduit les inégalités** via le revenu universel basé sur le patrimoine prouvé
6. - **Fonctionne sans autorité centrale** grâce au RAD décentralisé
7. - **Mesure la valeur réelle** par preuve d'acte plutôt que promesse

**IRIS représente une alternative viable aux systèmes monétaires traditionnels basés sur la dette.**
