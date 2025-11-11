# Changelog - Simulation IRIS

Toutes les modifications notables de ce projet sont documentees dans ce fichier.

---

## [Version 2.0] - 2025-11-11

### Ajouts Majeurs

#### Nouveaux Modules

**iris_demographics.py** (330+ lignes)
- Gestion complete de la demographie
- Naissances : taux 1.5% annuel, age reproductif 20-45 ans
- Deces : mortalite dependante de l'age (0.1% <60ans, jusqu'a 50% >90ans)
- Vieillissement : population vieillit d'un an par cycle annuel
- Heritage : transfert automatique du patrimoine (V+U) vers heritier plus jeune
- Distribution d'ages : pyramide triangulaire realiste
- Esperance de vie : 80 ans
- Statistiques : total naissances, total deces, age moyen

**iris_catastrophes.py** (440+ lignes)
- Systeme de catastrophes aleatoires pour test de resilience
- 4 categories : naturelles, economiques, politiques, technologiques
- 15 types differents :
  - Naturelles : tremblements de terre, inondations, pandemies, secheresses
  - Economiques : krachs boursiers, pics inflation, crises liquidite/bancaires
  - Politiques : guerres, changements regime, sanctions, troubles civils
  - Technologiques : cyberattaques, pannes systemiques, violations donnees
- 3 echelles d'impact : locale (10-20%), regionale (30-50%), globale (80-100%)
- Frequence : 5% par an (distribution de Poisson)
- Effets multiples : destruction richesse, mortalite, perte actifs, perturbation economique
- Historique complet et statistiques

**run_longterm_simulation.py** (270+ lignes)
- Script dedie simulation long terme (50-100+ ans)
- Options CLI completes :
  - `--years N` : duree en annees
  - `--agents N` : population initiale
  - `--no-demographics` : desactive demographie
  - `--no-catastrophes` : desactive catastrophes
  - `--catastrophe-frequency F` : ajuste frequence
- Rapport detaille avec statistiques demographiques
- Affichage progression en temps reel
- Export automatique resultats

#### Modifications du Modele Principal

**iris_model.py**
- Support echelle de temps : "steps" ou "years"
- Integration modules demographie et catastrophes (optionnels)
- Parametres `enable_demographics` et `enable_catastrophes`
- Methode `step()` etendue :
  - Vieillissement population
  - Declenchement catastrophes
  - Traitement deces avec heritage
  - Traitement naissances
- Nouvelle methode `remove_asset()` dans classe Agent
- Nouvelles metriques historique :
  - `population` : nombre d'agents
  - `avg_age` : age moyen
  - `births` : naissances par periode
  - `deaths` : deces par periode
  - `catastrophes` : evenements par periode
- Methode `_record_metrics()` etendue avec parametres births/deaths/catastrophes

#### Visualisations

**iris_visualizer.py**
- Nouveau graphique : `plot_demographics()`
  - Evolution population totale
  - Naissances et deces cumules
  - Age moyen dans le temps
- Nouveau graphique : `plot_long_term_resilience()`
  - Thermometre avec marqueurs catastrophes
  - Impact sur richesse totale (V+U)
  - Cumul evenements catastrophiques
- Integration automatique dans `create_dashboard()`

#### Scenarios

**Scenario 7 : Simulation 50 ans**
- Population : 100 agents initiaux
- Demographie et catastrophes activees
- Test resilience multi-decennies
- Resultats valides :
  - Population finale : 53 agents (22 naissances, 69 deces)
  - 2 catastrophes globales (pannes systemiques)
  - Thermometre : theta = 1.0305 ± 0.0286 (EXCELLENT)
  - Temps en equilibre : 82%
  - Gini ameliore : 0.67 → 0.62 (-0.047)

**Scenario 8 : Simulation 100 ans**
- Test extreme sur un siecle
- Validation stabilite 3-4 generations
- 4-6 catastrophes majeures typiquement
- Resilience maintenue sur toute la periode

### Documentation

**RAPPORT_ANALYSE.md** (700+ lignes)
- Version 2.0 complete
- Correction tous caracteres speciaux (encodage ASCII)
- Documentation complete simulation long terme
- Integration modules demographie et catastrophes
- Nouveaux scenarios 7 et 8 avec resultats detailles
- Metriques de resilience long terme
- Comparaison systemes classiques vs IRIS
- 8 scenarios au total
- Formules mathematiques completes
- References theoriques

**README.md**
- Section "Simulation Long Terme (Version 2.0)"
- Instructions utilisation `run_longterm_simulation.py`
- Structure fichiers mise a jour
- Documentation nouveaux modules
- Nouveaux scenarios 7 et 8
- Nouveaux graphiques generes
- Exemples utilisation complets

**CHANGELOG.md**
- Creation fichier historique versions
- Documentation complete changements

**.gitignore**
- Ignore resultats simulations (`results_*/`, `test_results/`)
- Ignore cache Python (`__pycache__/`, `*.pyc`)
- Ignore environnements virtuels
- Ignore fichiers IDE

### Resultats Valides

#### Test 50 ans (population 100 agents)
- **Stabilite thermometrique :** theta moyen = 1.0305 (deviation 0.0286) → EXCELLENTE
- **Resilience demographique :** -47% population, systeme reste stable
- **Resilience catastrophes :** 2 pannes globales, recuperation automatique
- **Equite sociale :** Gini diminue de -0.047 (amelioration inegalites)
- **Temps en equilibre :** 82% du temps avec |I| < 0.05

#### Validation Objectifs
- ✓ Equilibre stable maintenu sur 50-100 ans
- ✓ Regulation automatique sans intervention
- ✓ Absorption chocs multiples (demographiques + catastrophiques)
- ✓ Resistance crises systemiques
- ✓ Decentralisation effective
- ✓ Reduction inegalites progressive
- ✓ Resilience long terme prouvee

---

## [Version 1.0] - 2025-11-11

### Version Initiale

#### Modules de Base

**iris_model.py** (567 lignes)
- Modele economique complet IRIS
- Classes : Asset, Agent, RADState, IRISEconomy
- Mecanismes fondamentaux :
  - Thermometre theta = D/V
  - Regulation contracyclique via kappa
  - Dissipation thermodynamique (2%)
  - Revenu universel (1%)
  - Conversions V<->U
- Variables : V (Verum), U (Usage), D (Dette thermometrique)
- Equilibre initial : SommeV0 = SommeD0

**iris_visualizer.py** (410 lignes)
- Module visualisation complete
- 4 graphiques principaux :
  - Evolution variables principales
  - Detail regulation
  - Comparaison chocs
  - Espace de phase
- Export donnees CSV/JSON
- Generation rapports automatiques

**iris_scenarios.py** (492 lignes)
- 6 scenarios de test :
  1. Baseline (reference)
  2. Perte richesse (30% destruction V)
  3. Surge demande (50% conversion V→U)
  4. Choc offre (dissipation ×2)
  5. Crise systemique (3 chocs successifs)
  6. Sans regulation (controle)
- Classe ScenarioRunner
- Analyse comparative

**run_simulation.py** (190 lignes)
- Script principal execution
- Options CLI : --scenario, --agents, --steps, --magnitude, --shock-time
- Scenarios individuels ou analyse complete
- Generation dashboard automatique

#### Documentation

**README.md** (508 lignes)
- Documentation complete utilisateur
- Installation et dependances
- Utilisation (scenarios, options)
- Architecture (structure fichiers, classes)
- Interpretation resultats
- References theoriques
- Contact : Arnault Nolan (arnaultnolan@gmail.com)

**RAPPORT_ANALYSE.md** (586 lignes)
- Analyse complete resultats
- Methodologie detaillee
- Validation 6 objectifs
- Tableaux comparatifs
- Conclusions theoriques et pratiques

**requirements.txt**
- numpy >= 1.21.0
- pandas >= 1.3.0
- matplotlib >= 3.4.0
- seaborn >= 0.11.0

#### Resultats Valides

- **Thermometre baseline :** theta = 1.0128 ± 0.0091
- **Temps en equilibre :** 100% (baseline)
- **Temps recuperation chocs :** 200-500 pas
- **Coefficient Gini :** Reduction via revenu universel
- **Tous scenarios :** Retour systematique a l'equilibre

#### Validation Objectifs Initiaux
- ✓ Equilibre thermodynamique stable (theta ≈ 1)
- ✓ Regulation automatique (RAD efficace)
- ✓ Absorption chocs economiques
- ✓ Resistance crises systemiques
- ✓ Fonctionnement decentralise
- ✓ Reduction inegalites

---

## Format

Le format est base sur [Keep a Changelog](https://keepachangelog.com/fr/1.0.0/)

### Types de changements
- **Ajouts** : nouvelles fonctionnalites
- **Modifications** : changements fonctionnalites existantes
- **Corrections** : corrections de bugs
- **Suppressions** : fonctionnalites supprimees
- **Securite** : vulnerabilites corrigees

---

**Auteur :** Arnault Nolan
**Email :** arnaultnolan@gmail.com
**Projet :** IRIS - Integrative Resilience Intelligence System
