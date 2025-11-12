"""
IRIS Economic System - Core Model
==================================

Modèle du système économique IRIS (Integrative Resilience Intelligence System)
basé sur la preuve d'acte plutôt que la promesse de remboursement.

Auteur: Arnault Nolan
Email: arnaultnolan@gmail.com
Date: 2025

Composantes principales :
- V (Verum) : Valeur/mémoire de valeur
- U (Usage) : Monnaie d'usage
- D (Dette) : Miroir thermométrique (indicateur de régulation)
- RAD : Régulateur Automatique Décentralisé

Références théoriques :
- Cybernétique : Wiener, Ashby, Beer
- Thermodynamique : Georgescu-Roegen, Ayres
- Anthropologie économique : Graeber, Polanyi, Mauss
"""

import numpy as np
from dataclasses import dataclass, field
from typing import Dict, List, Tuple
from enum import Enum


class AssetType(Enum):
    """Types d'actifs dans le système IRIS"""
    IMMOBILIER = "immobilier"
    MOBILIER = "mobilier"
    ENTREPRISE = "entreprise"
    INTELLECTUEL = "intellectuel"
    SERVICE = "service"


class DebtComponent(Enum):
    """Composantes de la dette thermométrique"""
    MATERIELLE = "materielle"  # Biens et immobilisations
    SERVICES = "services"  # Flux d'entretien
    CONTRACTUELLE = "contractuelle"  # Titres à promesse productive
    ENGAGEMENT = "engagement"  # Opérations de staking
    REGULATRICE = "regulatrice"  # Chambre de Relance


@dataclass
class Asset:
    """
    Représente un actif dans le système IRIS

    Un actif est un bien réel (terrain, immeuble, entreprise, etc.) qui est
    ancré dans le système via l'Oracle d'initialisation. Chaque actif génère :
    - Un Verum (V) : la mémoire de sa valeur
    - Un miroir thermométrique (D) : l'indicateur de régulation associé
    - Un NFT fondateur : preuve cryptographique d'existence unique
    """
    id: str  # Identifiant unique de l'actif
    asset_type: AssetType  # Type d'actif (immobilier, mobilier, etc.)
    real_value: float  # Valeur réelle dans le monde physique (en unités monétaires classiques)
    V_initial: float = 0.0  # V₀ : Verum d'initialisation (mémoire de valeur IRIS)
    D_initial: float = 0.0  # D₀ : Miroir thermométrique initial (indicateur de régulation)
    owner_id: str = ""  # Identifiant du propriétaire
    nft_hash: str = ""  # Empreinte cryptographique du NFT fondateur (SHA-256)
    auth_factor: float = 1.0  # Facteur d'authentification (1.0 = source officielle, <1.0 = auto-déclaration)
    creation_time: int = 0  # Moment de l'ancrage dans le système

    def __post_init__(self):
        """
        Initialise V₀ et D₀ selon les règles IRIS

        Principe fondamental : Équilibre initial ΣV₀ = ΣD₀
        Cette égalité garantit que le thermomètre θ = D/V démarre à 1.0
        """
        if self.V_initial == 0.0:
            # Conversion de la valeur réelle en Verum IRIS
            # Formule complète : V_IRIS = V_asset × facteur_or × ajustement_thermométrique × auth_factor
            # Pour simplification dans cette simulation, on utilise directement real_value × auth_factor
            self.V_initial = self.real_value * self.auth_factor

            # Création du miroir thermométrique : D₀ = V₀
            # Ce miroir n'est PAS une dette exigible, mais un indicateur de régulation
            # Il permet au RAD de mesurer la tension thermométrique du système
            self.D_initial = self.V_initial


@dataclass
class Agent:
    """
    Représente un agent économique dans le système IRIS

    Un agent est une personne ou une entité qui possède :
    - Des actifs réels (ancré dans le système)
    - Un solde V (Verum) : mémoire de valeur, patrimoine ancré
    - Un solde U (Usage) : monnaie d'usage, liquidité pour transactions
    - Un score de contribution : mesure des actes prouvés

    L'agent peut :
    - Convertir V en U (activer son patrimoine)
    - Reconvertir U en V (épargner, investir)
    - Effectuer des transactions en U
    - Recevoir le revenu universel
    """
    id: str  # Identifiant unique de l'agent
    V_balance: float = 0.0  # Solde en Verum (patrimoine, mémoire de valeur)
    U_balance: float = 0.0  # Solde en Usage (liquidité, monnaie de transaction)
    assets: List[Asset] = field(default_factory=list)  # Liste des actifs possédés
    contribution_score: float = 0.0  # Score de contribution prouvée (pour gouvernance future)
    sex: str = "female"  # Sexe de l'agent (pour démographie réaliste)

    def add_asset(self, asset: Asset):
        """
        Ajoute un actif et met à jour le solde V

        Quand un agent ancre un nouvel actif :
        - L'actif est ajouté à sa liste
        - Son V_balance augmente du V₀ de l'actif
        - Le système global gagne V₀ en circulation et D₀ dans le RAD
        """
        self.assets.append(asset)
        self.V_balance += asset.V_initial  # Crédite le Verum d'initialisation

    def remove_asset(self, asset_id: str):
        """
        Retire un actif et met à jour le solde V

        Utilise lors de la destruction d'un actif (catastrophe, etc.)
        - L'actif est retire de la liste
        - Le V_balance est reduit du V_initial de l'actif
        """
        for i, asset in enumerate(self.assets):
            if asset.id == asset_id:
                self.V_balance -= asset.V_initial
                self.assets.pop(i)
                break

    def total_wealth(self) -> float:
        """
        Richesse totale de l'agent (V + U)

        La richesse totale combine :
        - V : patrimoine ancré (épargne, actifs)
        - U : liquidité (argent de poche)
        Cette somme est utilisée pour calculer le revenu universel
        """
        return self.V_balance + self.U_balance


@dataclass
class RADState:
    """
    État du Régulateur Automatique Décentralisé (RAD)

    Le RAD est le cœur du système IRIS. C'est un mécanisme autonome
    qui maintient l'équilibre thermodynamique en ajustant les paramètres
    du système selon la tension mesurée.

    Analogie : Le RAD joue le rôle d'un thermostat pour l'économie.
    - Si θ > 1 (trop de demande) → il refroidit (réduit κ)
    - Si θ < 1 (trop d'offre) → il réchauffe (augmente κ)

    Composantes de D (miroir thermométrique sectoriel) :
    - D_materielle : Biens physiques (terrains, immeubles)
    - D_services : Flux d'entretien et services
    - D_contractuelle : Titres et promesses productives
    - D_engagement : Staking et engagements
    - D_regulatrice : Chambre de relance (revenu universel)
    """
    # Composantes sectorielles du miroir thermométrique D
    # Chaque composante suit un type spécifique d'actifs/transactions
    D_materielle: float = 0.0  # Dette thermométrique des biens matériels
    D_services: float = 0.0  # Dette thermométrique des services
    D_contractuelle: float = 0.0  # Dette thermométrique des contrats
    D_engagement: float = 0.0  # Dette thermométrique des engagements
    D_regulatrice: float = 0.0  # Dette thermométrique de la régulation (RU, dissipation)

    # Paramètres de régulation du système
    kappa: float = 1.0  # Coefficient de conversion V → U (κ, kappa)
    T_period: int = 100  # Périodicité de régulation profonde (tous les N pas)
    dissipation_rate: float = 0.02  # Taux de dissipation thermodynamique (friction, 2%)

    def total_D(self) -> float:
        """
        Calcule la dette thermométrique totale D

        D = somme de toutes les composantes sectorielles
        D est utilisé pour calculer le thermomètre : θ = D/V

        Note : D n'est PAS une dette au sens juridique, c'est un
        indicateur de régulation (miroir thermométrique)
        """
        return (self.D_materielle + self.D_services + self.D_contractuelle +
                self.D_engagement + self.D_regulatrice)

    def update_kappa(self, thermometer: float, target: float = 1.0):
        """
        Mise à jour du coefficient κ (kappa) selon la tension thermométrique

        Principe CONTRACYCLIQUE (stabilisateur automatique) :
        - Si θ > 1 (excès de demande) → κ diminue → ralentit conversion V→U
        - Si θ < 1 (déficit de demande) → κ augmente → accélère conversion V→U

        Formule de rétroaction négative :
        κ(t+1) = κ(t) × (1 - α × (θ(t) - 1))
        avec α = 0.1 (coefficient de rétroaction)

        Limites : κ ∈ [0.1, 2.0] pour éviter les divergences
        """
        # Calcul de la déviation par rapport à la cible (normalement θ = 1)
        deviation = thermometer - target

        # Ajustement proportionnel à la déviation (rétroaction négative)
        # Si deviation > 0 (θ > 1) → adjustment < 0 → κ diminue
        # Si deviation < 0 (θ < 1) → adjustment > 0 → κ augmente
        adjustment = -0.1 * deviation  # α = 0.1 (coefficient de rétroaction)

        # Application de l'ajustement avec bornes de sécurité
        # κ ne peut pas descendre sous 0.1 ni monter au-dessus de 2.0
        self.kappa = max(0.1, min(2.0, self.kappa * (1 + adjustment)))


class IRISEconomy:
    """
    Modèle complet de l'économie IRIS

    Principes fondamentaux :
    1. Équilibre initial : ΣV₀ = ΣD₀
    2. Thermomètre global : θ = D/V_circulation
    3. Régulation contracyclique via RAD
    4. Conservation des flux avec dissipation mesurée
    """

    def __init__(self,
                 initial_agents: int = 100,
                 gold_factor: float = 1.0,
                 universal_income_rate: float = 0.01,
                 enable_demographics: bool = False,
                 enable_catastrophes: bool = False,
                 time_scale: str = "steps"):
        """
        Initialise l'économie IRIS

        Args:
            initial_agents: Nombre d'agents initiaux
            gold_factor: Facteur or de zone (équivalent or local)
            universal_income_rate: Taux de revenu universel
            enable_demographics: Active la démographie (naissances/décès)
            enable_catastrophes: Active les catastrophes aléatoires
            time_scale: "steps" ou "years" pour l'échelle de temps
        """
        self.agents: Dict[str, Agent] = {}
        self.assets: Dict[str, Asset] = {}
        self.rad = RADState()
        self.gold_factor = gold_factor
        self.universal_income_rate = universal_income_rate
        self.time_scale = time_scale
        self.enable_demographics = enable_demographics
        self.enable_catastrophes = enable_catastrophes

        # Modules optionnels
        self.demographics = None
        self.catastrophe_manager = None
        self.agent_ages: Dict[str, int] = {}

        # Si démographie activée, initialise le module
        if enable_demographics:
            from iris_demographics import Demographics
            self.demographics = Demographics()

        # Si catastrophes activées, initialise le gestionnaire
        if enable_catastrophes:
            from iris_catastrophes import CatastropheManager
            self.catastrophe_manager = CatastropheManager()

        # Métriques de suivi
        self.time = 0
        self.history = {
            'time': [],
            'total_V': [],
            'total_U': [],
            'total_D': [],
            'thermometer': [],
            'indicator': [],
            'kappa': [],
            'gini_coefficient': [],
            'circulation_rate': [],
            'population': [],
            'avg_age': [],
            'births': [],
            'deaths': [],
            'catastrophes': []
        }

        # Initialisation avec des agents et actifs
        self._initialize_agents(initial_agents)

        # Initialise les âges si démographie activée
        if self.enable_demographics:
            self.agent_ages = self.demographics.initialize_ages(self.agents)

    def _initialize_agents(self, n_agents: int):
        """
        Crée les agents initiaux avec des actifs distribués de manière réaliste

        Cette fonction simule l'Oracle d'initialisation en créant :
        - Des agents avec des identités uniques
        - Des actifs de différents types (immobilier, mobilier, entreprises, etc.)
        - Une distribution log-normale des richesses (réaliste : peu de riches, beaucoup de pauvres)

        Processus :
        1. Pour chaque agent :
           - Génère 1-3 actifs (distribution de Poisson)
           - Chaque actif a une valeur log-normale (réaliste)
           - Chaque actif génère V₀ et D₀ égaux
        2. Les D₀ sont répartis dans le RAD selon le type d'actif
        3. Vérification finale : ΣV₀ = ΣD₀
        """
        # NOTE: Ne fixe PAS la graine ici pour permettre des résultats différents
        # Si reproductibilité nécessaire, utiliser --seed en ligne de commande

        for i in range(n_agents):
            # Crée un nouvel agent avec sexe aléatoire (50/50)
            agent = Agent(id=f"agent_{i}", sex=np.random.choice(['male', 'female']))

            # Distribution log-normale des richesses (réaliste)
            # La plupart des agents ont peu d'actifs, quelques-uns en ont beaucoup
            n_assets = np.random.poisson(2) + 1  # 1 à ~5 actifs (moyenne 3)

            for j in range(n_assets):
                # Type d'actif aléatoire (immobilier, mobilier, entreprise, etc.)
                asset_type = np.random.choice(list(AssetType))

                # Valeur réelle log-normale : e^(10 ± 1.5)
                # Produit une distribution réaliste : beaucoup de petits actifs, peu de grands
                real_value = np.random.lognormal(10, 1.5)

                # Crée l'actif avec sa preuve d'existence
                asset = Asset(
                    id=f"asset_{i}_{j}",
                    asset_type=asset_type,
                    real_value=real_value,
                    owner_id=agent.id,
                    auth_factor=np.random.uniform(0.9, 1.0),  # Facteur d'authentification (90-100%)
                    creation_time=0  # Tous ancrés au temps 0 (initialisation)
                )

                # Ajoute l'actif à l'agent (génère V₀)
                agent.add_asset(asset)
                # Enregistre l'actif dans le système
                self.assets[asset.id] = asset

                # Mise à jour du RAD : distribue D₀ dans la bonne composante
                # Selon le type d'actif, D₀ va dans une composante sectorielle différente
                if asset_type == AssetType.IMMOBILIER or asset_type == AssetType.MOBILIER:
                    # Biens physiques → D_materielle
                    self.rad.D_materielle += asset.D_initial
                elif asset_type == AssetType.SERVICE:
                    # Services → D_services
                    self.rad.D_services += asset.D_initial
                elif asset_type == AssetType.ENTREPRISE:
                    # Entreprises → D_contractuelle
                    self.rad.D_contractuelle += asset.D_initial
                else:
                    # Par défaut → D_materielle
                    self.rad.D_materielle += asset.D_initial

            # Enregistre l'agent dans le système
            self.agents[agent.id] = agent

        # Vérification critique : l'équilibre initial doit être respecté
        self._verify_initial_balance()

    def _verify_initial_balance(self):
        """Vérifie l'équilibre initial : ΣV₀ = ΣD₀"""
        total_V = sum(agent.V_balance for agent in self.agents.values())
        total_D = self.rad.total_D()

        assert abs(total_V - total_D) < 1e-6, \
            f"Déséquilibre initial : V={total_V:.2f}, D={total_D:.2f}"

        print(f"OK: Équilibre initial vérifié : V₀ = D₀ = {total_V:.2f}")

    def thermometer(self) -> float:
        """
        Calcul du thermomètre global : θ = D / V_circulation

        Le thermomètre est LA MÉTRIQUE CENTRALE du système IRIS.
        Il mesure la tension thermodynamique de l'économie :

        θ = D_total / V_circulation

        Interprétation :
        - θ = 1.0 : Équilibre parfait (cible)
        - θ > 1.0 : Excès de demande / pénurie de patrimoine actif
        - θ < 1.0 : Excès d'offre / patrimoine immobilisé

        Analogie : θ est comme la température d'un système thermodynamique.
        Le RAD agit comme un thermostat pour maintenir θ proche de 1.

        Returns:
            Ratio D/V (devrait être proche de 1 en équilibre)
        """
        # Somme de tous les V en circulation (patrimoine actif des agents)
        V_circulation = sum(agent.V_balance for agent in self.agents.values())

        # Somme de tous les D dans le RAD (miroir thermométrique total)
        total_D = self.rad.total_D()

        # Cas limite : si V est presque nul, on retourne 1.0 par défaut
        if V_circulation < 1e-6:
            return 1.0

        # Calcul du thermomètre : θ = D/V
        return total_D / V_circulation

    def indicator(self) -> float:
        """
        Indicateur centré : I = θ - 1

        L'indicateur mesure la DÉVIATION par rapport à l'équilibre :
        - I = 0 : Système en équilibre parfait
        - I > 0 : Tension positive (θ > 1), excès de demande
        - I < 0 : Tension négative (θ < 1), excès d'offre

        L'indicateur est utilisé par le RAD pour décider des ajustements.
        Objectif : maintenir |I| < 0.1 (déviation < 10%)

        Returns:
            Déviation du thermomètre par rapport à l'équilibre (0 = équilibre parfait)
        """
        return self.thermometer() - 1.0

    def gini_coefficient(self) -> float:
        """
        Calcul du coefficient de Gini pour mesurer les inégalités

        Le coefficient de Gini mesure la distribution des richesses :
        - 0.0 : Égalité parfaite (tous ont la même richesse)
        - 1.0 : Inégalité maximale (une personne a tout)

        Dans IRIS, le Gini devrait diminuer grâce au revenu universel
        et à la redistribution thermodynamique.

        Formule de Gini :
        G = (2 × Σ(i × w_i)) / (n × Σw_i) - (n+1)/n

        où w_i est la richesse de l'agent i (classé par richesse croissante)

        Returns:
            Coefficient entre 0 (égalité parfaite) et 1 (inégalité maximale)
        """
        # Récupère toutes les richesses (V + U) de chaque agent
        wealths = np.array([agent.total_wealth() for agent in self.agents.values()])

        # Trie par richesse croissante (nécessaire pour le calcul de Gini)
        wealths = np.sort(wealths)
        n = len(wealths)

        # Cas limite : richesse totale nulle
        if wealths.sum() < 1e-6:
            return 0.0

        # Calcul du coefficient de Gini
        # cumsum[- 1] = somme totale des richesses
        cumsum = np.cumsum(wealths)

        # Formule de Gini :  2 × Σ(rang × richesse) / (n × total) - (n+1)/n
        return (2 * np.sum((np.arange(1, n+1)) * wealths)) / (n * cumsum[-1]) - (n + 1) / n

    def circulation_rate(self) -> float:
        """
        Taux de circulation : ratio entre U (usage) et V (mémoire)

        Mesure la LIQUIDITÉ du système :
        - Taux faible (U/V petit) : patrimoine immobilisé, peu de transactions
        - Taux élevé (U/V grand) : beaucoup de liquidité, économie active

        Un taux optimal se situe autour de 0.1-0.3 (10-30% de liquidité)

        Returns:
            Ratio U/V mesurant la liquidité du système
        """
        # Total du patrimoine ancré (Verum)
        total_V = sum(agent.V_balance for agent in self.agents.values())
        # Total de la liquidité (Usage)
        total_U = sum(agent.U_balance for agent in self.agents.values())

        # Cas limite : pas de patrimoine ancré
        if total_V < 1e-6:
            return 0.0

        # Calcul du taux de circulation
        return total_U / total_V

    def convert_V_to_U(self, agent_id: str, amount: float) -> bool:
        """
        Conversion de V (mémoire) en U (usage) via le coefficient κ

        C'EST LA FONCTION CLE DU SYSTÈME IRIS !

        Logique économique :
        - V (Verum) = patrimoine ancré, "épargne", mémoire de valeur
        - U (Usage) = liquidité, "argent de poche", monnaie de transaction
        - La conversion V→U "active" le patrimoine pour l'utiliser

        Mécanisme :
        1. L'agent "dépense" une partie de son V
        2. Il reçoit U = V × κ (κ est ajusté par le RAD)
        3. D ne change PAS (le miroir thermométrique reste constant)
        4. θ = D/V AUGMENTE (car V diminue) → signale au RAD
        5. Le RAD détecte et ajuste κ pour ralentir les conversions futures

        Analogie : V→U c'est comme retirer de l'argent d'un compte épargne
        pour le mettre en liquidité. Le RAD observe et ajuste les "frais".

        Impact sur le système :
        - V↓ → θ↑ → RAD détecte → κ↓ → futures conversions plus coûteuses
        - C'est le mécanisme CONTRACYCLIQUE qui stabilise le système

        Args:
            agent_id: Identifiant de l'agent
            amount: Montant de V à convertir en U

        Returns:
            True si la conversion a réussi, False si l'agent n'a pas assez de V
        """
        # Vérifie que l'agent existe et a assez de V
        agent = self.agents.get(agent_id)
        if not agent or agent.V_balance < amount:
            return False  # Conversion impossible

        # CONVERSION : U = V × κ
        # κ (kappa) est le coefficient de conversion ajusté par le RAD
        # κ = 1.0 en équilibre, κ < 1.0 si θ > 1 (freine), κ > 1.0 si θ < 1 (stimule)
        U_amount = amount * self.rad.kappa

        # Débite le V de l'agent
        agent.V_balance -= amount
        # Crédite le U de l'agent
        agent.U_balance += U_amount

        # IMPORTANT : D ne change pas lors de la conversion V→U
        # Pourquoi ? Parce que la valeur totale (V+U) reste la même
        # Seule la FORME change (patrimoine → liquidité)

        # Conséquence : θ = D/V augmente naturellement car V↓
        # Le RAD détectera cette hausse et ajustera κ vers le bas
        # C'est le mécanisme de RÉTROACTION NÉGATIVE qui stabilise

        return True

    def transaction(self, from_id: str, to_id: str, amount: float) -> bool:
        """
        Transaction en U (monnaie d'usage) entre deux agents
        Inclut une DISSIPATION THERMODYNAMIQUE (friction)

        Principe thermodynamique :
        - Chaque transaction "consomme" une petite partie de l'énergie (U)
        - Cette dissipation simule : frais de transaction, friction, entropie
        - La valeur dissipée "s'évapore" du système (réduit D_regulatrice)
        - C'est un mécanisme naturel de régulation (comme la friction physique)

        Formule :
        - Dissipation = montant × τ (τ = taux de dissipation, typiquement 2%)
        - Montant net reçu = montant - dissipation
        - Impact : D↓ → θ↓ → le système se "refroidit"

        Cette dissipation est ensuite REDISTRIBUÉE via le revenu universel,
        créant une boucle vertueuse de redistribution automatique.

        Args:
            from_id: Agent émetteur (qui paye)
            to_id: Agent récepteur (qui reçoit)
            amount: Montant en U à transférer

        Returns:
            True si la transaction a réussi, False sinon
        """
        # Vérifie que les deux agents existent
        from_agent = self.agents.get(from_id)
        to_agent = self.agents.get(to_id)

        # Vérifie que l'émetteur a assez de U
        if not from_agent or not to_agent or from_agent.U_balance < amount:
            return False  # Transaction impossible

        # DISSIPATION THERMODYNAMIQUE (friction de la transaction)
        # Simule les coûts naturels : énergie, temps, vérification, etc.
        dissipation = amount * self.rad.dissipation_rate  # τ = 2% par défaut
        net_amount = amount - dissipation  # Ce que reçoit réellement le destinataire

        # Débite l'émetteur du montant total
        from_agent.U_balance -= amount
        # Crédite le récepteur du montant net (après dissipation)
        to_agent.U_balance += net_amount

        # IMPACT THERMODYNAMIQUE : la dissipation réduit D_regulatrice
        # Pourquoi ? Car la valeur dissipée "sort" du système
        # Conséquence : θ = D/V diminue légèrement → système se refroidit
        self.rad.D_regulatrice -= dissipation

        # Note : Cette valeur dissipée sera redistribuée via le revenu universel
        # C'est un mécanisme de REDISTRIBUTION AUTOMATIQUE par la thermodynamique

        return True

    def distribute_universal_income(self):
        """
        Distribution du revenu universel basé sur le patrimoine total prouvé

        C'EST LE MÉCANISME DE JUSTICE SOCIALE D'IRIS !

        Principe :
        - Tous les agents reçoivent un revenu universel égal
        - Montant = τ% du patrimoine total / nombre d'agents (τ = 1%)
        - Financé par la dissipation thermodynamique (redistribution)
        - Distribution régulière (tous les 50 pas de temps)

        Différence avec les systèmes traditionnels :
        - PAS de création monétaire ex nihilo
        - PAS d'endettement pour financer
        - Redistribution de la valeur dissipée naturellement
        - Basé sur le patrimoine PROUVÉ (pas sur des promesses)

        Impact :
        - Réduit les inégalités (coefficient de Gini ↓)
        - Maintient le pouvoir d'achat de tous
        - Compense la dissipation thermodynamique
        - Crée une boucle de redistribution automatique

        Note : Dans cette simulation simplifiée, on ne modifie pas D
        car on considère que la redistribution est "neutre" thermodynamiquement.
        Dans une implémentation complète, il faudrait ajuster D_regulatrice.
        """
        # Calcule le patrimoine total du système (V + U de tous les agents)
        total_wealth = sum(agent.total_wealth() for agent in self.agents.values())

        # Calcule le revenu universel par agent
        # Formule : RU = (patrimoine_total × τ) / nombre_agents
        # τ = universal_income_rate = 1% par défaut
        income_per_agent = total_wealth * self.universal_income_rate / len(self.agents)

        # Distribue le revenu universel à TOUS les agents équitablement
        for agent in self.agents.values():
            agent.U_balance += income_per_agent  # Crédite en liquidité (U)

        # Pas de modification de D dans cette simulation simplifiée
        # La redistribution est considérée comme thermodynamiquement neutre
        # (la valeur circule mais ne change pas la tension globale)

    def regulate(self):
        """
        Mécanisme de régulation du RAD (Régulateur Automatique Décentralisé)

        C'EST LE CŒUR DU SYSTÈME IRIS - LE "THERMOSTAT" DE L'ÉCONOMIE !

        Le RAD opère sur TROIS niveaux complémentaires :

        1. RÉTROACTION CONTINUE sur κ (contracyclique) :
           - Ajuste κ à chaque pas de temps selon θ
           - Si θ > 1 → κ↓ (freine les conversions V→U)
           - Si θ < 1 → κ↑ (stimule les conversions V→U)
           - Stabilisateur automatique, sans intervention humaine

        2. AJUSTEMENT PÉRIODIQUE de la dissipation (tous les 100 pas) :
           - Si |I| > 0.1 (déviation > 10%) → augmente τ (plus de friction)
           - Si |I| < 0.1 (stable) → réduit τ (moins de friction)
           - Permet au système de s'adapter aux changements

        3. REBALANCEMENT THERMODYNAMIQUE (si |I| > 0.2, déviation > 20%) :
           - Ajuste directement D pour ramener θ vers 1
           - Mécanisme de "dernier recours" pour crises majeures
           - Ajuste progressivement (10% par cycle) pour éviter les chocs

        Analogie : Le RAD est comme un pilote automatique d'avion :
        - Niveau 1 : Corrections légères continues (κ)
        - Niveau 2 : Ajustements modérés périodiques (τ)
        - Niveau 3 : Interventions fortes en cas de crise (D)

        Le système est ENTIÈREMENT AUTOMATIQUE et DÉCENTRALISÉ.
        Aucune décision humaine n'est requise. C'est une cybernétique pure.
        """
        # NIVEAU 1 : Rétroaction continue sur κ
        # Mesure la tension actuelle du système
        theta = self.thermometer()
        # Ajuste κ selon la formule : κ(t+1) = κ(t) × (1 - α × (θ - 1))
        # avec α = 0.1 (coefficient de rétroaction)
        self.rad.update_kappa(theta)

        # NIVEAU 2 & 3 : Régulation périodique (tous les T_period pas)
        if self.time % self.rad.T_period == 0:
            # Mesure la déviation par rapport à l'équilibre
            indicator = self.indicator()

            # NIVEAU 2 : Ajustement dynamique de la dissipation
            # La dissipation (friction) est un régulateur thermodynamique
            if abs(indicator) > 0.1:
                # Système instable (|I| > 10%) → AUGMENTE la friction
                # Plus de friction = plus de redistribution = plus de stabilisation
                self.rad.dissipation_rate = min(0.05, self.rad.dissipation_rate * 1.1)
            else:
                # Système stable (|I| < 10%) → RÉDUIT la friction
                # Moins de friction = économie plus fluide = meilleure efficacité
                self.rad.dissipation_rate = max(0.01, self.rad.dissipation_rate * 0.95)

            # NIVEAU 3 : Rebalancement thermodynamique d'urgence
            # Si θ s'éloigne TROP de 1 (|I| > 20%), intervention directe sur D
            if abs(indicator) > 0.2:
                # Calcule le V en circulation
                V_circulation = sum(agent.V_balance for agent in self.agents.values())

                # La cible est D = V pour avoir θ = D/V = 1
                target_D = V_circulation
                current_D = self.rad.total_D()

                # Calcule l'ajustement nécessaire (progressif : 10% par cycle)
                # On ne corrige pas d'un coup pour éviter les chocs brutaux
                adjustment = (target_D - current_D) * 0.1

                # Applique l'ajustement sur D_regulatrice (chambre de relance)
                # C'est la composante "flexible" de D, utilisée pour la régulation
                self.rad.D_regulatrice += adjustment

    def reconvert_U_to_V(self, agent_id: str, amount: float) -> bool:
        """
        Reconversion de U (usage) en V (épargne/investissement)
        Permet aux agents de "cristalliser" leur liquidité en actifs

        Args:
            agent_id: Identifiant de l'agent
            amount: Montant de U à reconvertir

        Returns:
            True si la conversion a réussi
        """
        agent = self.agents.get(agent_id)
        if not agent or agent.U_balance < amount:
            return False

        # Reconversion : U → V (avec un léger coût)
        V_amount = amount * 0.95  # Coût de 5%

        agent.U_balance -= amount
        agent.V_balance += V_amount

        # Ajustement de D pour maintenir l'équilibre
        self.rad.D_materielle += V_amount

        return True

    def step(self, n_transactions: int = 10):
        """
        Avance la simulation d'un pas de temps

        Si time_scale="years", ce pas représente 1 année
        Si time_scale="steps", ce pas représente une période abstraite

        Args:
            n_transactions: Nombre de transactions à simuler
        """
        self.time += 1

        # Variables de suivi démographique pour cette étape
        births_this_step = 0
        deaths_this_step = 0
        catastrophes_this_step = 0

        # 0a. Vieillissement de la population (si démographie activée)
        if self.enable_demographics and self.time_scale == "years":
            self.agent_ages = self.demographics.age_population(self.agent_ages)

        # 0b. Catastrophes aléatoires (si activées)
        if self.enable_catastrophes and self.time_scale == "years":
            new_events = self.catastrophe_manager.update(
                self.time, self.agents, self.agent_ages, self
            )
            catastrophes_this_step = len(new_events)

        agent_ids = list(self.agents.keys())
        if not agent_ids:  # Sécurité : arrête si plus d'agents
            return

        # 1. Conversions V -> U aléatoires (agents activent leur patrimoine)
        # CORRECTION : Réduit la fréquence et le montant pour éviter vidange de V
        for _ in range(max(1, n_transactions // 10)):  # Beaucoup moins de conversions
            agent_id = np.random.choice(agent_ids)
            agent = self.agents[agent_id]

            # Seulement si l'agent a besoin de liquidité (U faible)
            if agent.V_balance > 0 and agent.U_balance < agent.V_balance * 0.1:
                # Conversion modérée : 2% du V au lieu de 10%
                convert_amount = agent.V_balance * 0.02
                self.convert_V_to_U(agent_id, convert_amount)

        # 2. Reconversions U -> V (épargne/investissement)
        for _ in range(max(1, n_transactions // 10)):
            agent_id = np.random.choice(agent_ids)
            agent = self.agents[agent_id]

            # Épargne si l'agent a beaucoup de liquidité
            if agent.U_balance > agent.V_balance * 0.2:
                save_amount = agent.U_balance * 0.05
                self.reconvert_U_to_V(agent_id, save_amount)

        # 3. Transactions U entre agents
        for _ in range(n_transactions):
            agent_ids = list(self.agents.keys())
            if len(agent_ids) < 2:
                break
            from_id = np.random.choice(agent_ids)
            to_id = np.random.choice(agent_ids)
            if from_id != to_id:
                from_agent = self.agents[from_id]
                if from_agent.U_balance > 1.0:  # Seuil minimum
                    amount = min(from_agent.U_balance * 0.1, from_agent.U_balance * 0.5)
                    self.transaction(from_id, to_id, amount)

        # 4. Distribution du revenu universel (moins fréquent)
        if self.time % 50 == 0:
            self.distribute_universal_income()

        # 5. Régulation automatique
        self.regulate()

        # 6. Démographie : décès et naissances (si activée et échelle = années)
        if self.enable_demographics and self.time_scale == "years":
            # 6a. Traitement des décès
            deceased_ids = self.demographics.process_deaths(
                self.agents, self.agent_ages, self.time
            )
            deaths_this_step = len(deceased_ids)

            # 6b. Héritage et suppression des agents décédés
            for deceased_id in deceased_ids:
                if deceased_id in self.agents:
                    # Transfert du patrimoine à un héritier
                    if len(self.agents) > 1:
                        heir_id = self.demographics.inherit_wealth(
                            deceased_id, self.agents, self.agent_ages
                        )

                    # Suppression de l'agent décédé
                    del self.agents[deceased_id]
                    if deceased_id in self.agent_ages:
                        del self.agent_ages[deceased_id]

            # 6c. Traitement des naissances
            new_agents = self.demographics.process_births(
                self.agents, self.agent_ages, self.assets, self.time
            )
            births_this_step = len(new_agents)

            # Ajout des nouveaux agents au système
            for new_agent in new_agents:
                self.agents[new_agent.id] = new_agent
                self.agent_ages[new_agent.id] = 0  # Les nouveau-nés ont 0 ans

            # 6d. Traitement de la migration (stabilisateur de population)
            migrants = self.demographics.process_migration(
                self.agents, self.agent_ages, self.assets, self.time
            )

            # Ajout des migrants au système (ages déjà assignés dans process_migration)
            for migrant in migrants:
                self.agents[migrant.id] = migrant

        # 7. Enregistrement des métriques
        self._record_metrics(births_this_step, deaths_this_step, catastrophes_this_step)

    def _record_metrics(self, births=0, deaths=0, catastrophes=0):
        """
        Enregistre les métriques du système pour analyse

        Args:
            births: Nombre de naissances à cet instant
            deaths: Nombre de décès à cet instant
            catastrophes: Nombre de catastrophes à cet instant
        """
        self.history['time'].append(self.time)
        self.history['total_V'].append(sum(a.V_balance for a in self.agents.values()))
        self.history['total_U'].append(sum(a.U_balance for a in self.agents.values()))
        self.history['total_D'].append(self.rad.total_D())
        self.history['thermometer'].append(self.thermometer())
        self.history['indicator'].append(self.indicator())
        self.history['kappa'].append(self.rad.kappa)
        self.history['gini_coefficient'].append(self.gini_coefficient())
        self.history['circulation_rate'].append(self.circulation_rate())

        # Métriques démographiques
        self.history['population'].append(len(self.agents))
        if self.enable_demographics and self.agent_ages:
            avg_age = sum(self.agent_ages.values()) / len(self.agent_ages)
            self.history['avg_age'].append(avg_age)
        else:
            self.history['avg_age'].append(0)

        self.history['births'].append(births)
        self.history['deaths'].append(deaths)
        self.history['catastrophes'].append(catastrophes)

    def simulate(self, steps: int = 1000, n_transactions: int = 10):
        """
        Exécute la simulation sur plusieurs pas de temps

        Args:
            steps: Nombre de pas de simulation
            n_transactions: Transactions par pas
        """
        print(f"\nDémarrage de la simulation IRIS ({steps} pas)...")

        for i in range(steps):
            self.step(n_transactions)

            if (i + 1) % 100 == 0:
                theta = self.thermometer()
                indicator = self.indicator()
                gini = self.gini_coefficient()
                print(f"  Pas {i+1}/{steps} - θ={theta:.4f}, I={indicator:.4f}, Gini={gini:.4f}")

        print("OK: Simulation terminée\n")

    def inject_shock(self, shock_type: str, magnitude: float):
        """
        Injecte un choc économique pour tester la résilience

        Args:
            shock_type: Type de choc ('wealth_loss', 'demand_surge', 'supply_shock')
            magnitude: Intensité du choc (0-1)
        """
        print(f"\nATTENTION: Injection d'un choc : {shock_type} (magnitude={magnitude:.2f})")

        if shock_type == 'wealth_loss':
            # Destruction d'une partie du patrimoine (catastrophe naturelle, etc.)
            for agent in self.agents.values():
                loss = agent.V_balance * magnitude
                agent.V_balance -= loss
                # Réduction correspondante de D
                self.rad.D_materielle -= loss

        elif shock_type == 'demand_surge':
            # Augmentation soudaine de la demande (conversion massive V -> U)
            for agent in self.agents.values():
                if agent.V_balance > 0:
                    convert = agent.V_balance * magnitude
                    self.convert_V_to_U(agent.id, convert)

        elif shock_type == 'supply_shock':
            # Choc d'offre : augmentation du taux de dissipation
            self.rad.dissipation_rate *= (1 + magnitude)

        print(f"  Thermomètre après choc : {self.thermometer():.4f}")
        print(f"  Indicateur après choc : {self.indicator():.4f}")
