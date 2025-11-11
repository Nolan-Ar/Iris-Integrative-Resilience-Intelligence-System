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
                 universal_income_rate: float = 0.01):
        """
        Initialise l'économie IRIS

        Args:
            initial_agents: Nombre d'agents initiaux
            gold_factor: Facteur or de zone (équivalent or local)
            universal_income_rate: Taux de revenu universel
        """
        self.agents: Dict[str, Agent] = {}
        self.assets: Dict[str, Asset] = {}
        self.rad = RADState()
        self.gold_factor = gold_factor
        self.universal_income_rate = universal_income_rate

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
            'circulation_rate': []
        }

        # Initialisation avec des agents et actifs
        self._initialize_agents(initial_agents)

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
        np.random.seed(42)  # Fixe la graine pour reproductibilité des résultats

        for i in range(n_agents):
            # Crée un nouvel agent
            agent = Agent(id=f"agent_{i}")

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
        Mesure la liquidité du système
        """
        total_V = sum(agent.V_balance for agent in self.agents.values())
        total_U = sum(agent.U_balance for agent in self.agents.values())

        if total_V < 1e-6:
            return 0.0

        return total_U / total_V

    def convert_V_to_U(self, agent_id: str, amount: float) -> bool:
        """
        Conversion de V (mémoire) en U (usage) via le coefficient kappa

        Logique IRIS :
        - V représente la valeur ancrée (mémoire de patrimoine)
        - U représente la liquidité (monnaie d'usage)
        - Quand V→U, on "active" du patrimoine en liquidité
        - D (miroir thermométrique) ne change pas lors de la conversion
        - Le thermomètre θ=D/V augmente naturellement (V diminue)
        - Le RAD détecte cette hausse et ajuste κ pour réguler

        Args:
            agent_id: Identifiant de l'agent
            amount: Montant de V à convertir

        Returns:
            True si la conversion a réussi
        """
        agent = self.agents.get(agent_id)
        if not agent or agent.V_balance < amount:
            return False

        # Conversion : U = V × κ
        U_amount = amount * self.rad.kappa

        agent.V_balance -= amount
        agent.U_balance += U_amount

        # D ne change pas lors de la conversion V→U
        # Le thermomètre θ=D/V augmentera naturellement car V diminue
        # C'est le mécanisme de régulation voulu : le RAD détecte et ajuste κ

        return True

    def transaction(self, from_id: str, to_id: str, amount: float) -> bool:
        """
        Transaction en U (monnaie d'usage) entre deux agents
        Inclut une dissipation thermodynamique

        Args:
            from_id: Agent émetteur
            to_id: Agent récepteur
            amount: Montant à transférer

        Returns:
            True si la transaction a réussi
        """
        from_agent = self.agents.get(from_id)
        to_agent = self.agents.get(to_id)

        if not from_agent or not to_agent or from_agent.U_balance < amount:
            return False

        # Dissipation thermodynamique (simule friction, coûts de transaction)
        dissipation = amount * self.rad.dissipation_rate
        net_amount = amount - dissipation

        from_agent.U_balance -= amount
        to_agent.U_balance += net_amount

        # La dissipation réduit la dette thermométrique
        self.rad.D_regulatrice -= dissipation

        return True

    def distribute_universal_income(self):
        """
        Distribution du revenu universel basé sur le patrimoine total prouvé
        Mécanisme de redistribution fondamental dans IRIS

        Le revenu universel est une redistribution, pas une création monétaire.
        Dans IRIS, il est financé par la dissipation thermodynamique du système
        (friction des transactions) qui est ensuite redistribuée équitablement.

        Pour simplifier, on ne modifie pas D lors de cette redistribution.
        """
        total_wealth = sum(agent.total_wealth() for agent in self.agents.values())
        income_per_agent = total_wealth * self.universal_income_rate / len(self.agents)

        for agent in self.agents.values():
            agent.U_balance += income_per_agent

        # Pas de modification de D : le revenu universel est une redistribution
        # de la valeur dissipée par les transactions, déjà comptabilisée

    def regulate(self):
        """
        Mécanisme de régulation du RAD
        Ajuste kappa selon la tension thermométrique

        Le RAD opère sur deux niveaux :
        1. Rétroaction continue sur κ (contracyclique)
        2. Régulation périodique de D pour maintenir l'équilibre thermodynamique
        """
        theta = self.thermometer()
        self.rad.update_kappa(theta)

        # Régulation périodique pour maintenir l'équilibre du système
        if self.time % self.rad.T_period == 0:
            indicator = self.indicator()

            # Ajustement de la dissipation selon la déviation
            if abs(indicator) > 0.1:
                # Augmente la dissipation si le système s'éloigne de l'équilibre
                self.rad.dissipation_rate = min(0.05, self.rad.dissipation_rate * 1.1)
            else:
                # Réduit la dissipation si le système est stable
                self.rad.dissipation_rate = max(0.01, self.rad.dissipation_rate * 0.95)

            # Mécanisme de rebalancement thermodynamique
            # Si θ s'éloigne trop de 1, le RAD ajuste D pour ramener vers l'équilibre
            if abs(indicator) > 0.2:
                V_circulation = sum(agent.V_balance for agent in self.agents.values())
                target_D = V_circulation  # Cible : D = V pour θ = 1
                current_D = self.rad.total_D()
                adjustment = (target_D - current_D) * 0.1  # Ajustement progressif (10%)

                # Distribue l'ajustement sur D_regulatrice (chambre de relance)
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

        Args:
            n_transactions: Nombre de transactions à simuler
        """
        self.time += 1

        agent_ids = list(self.agents.keys())

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

        # 6. Enregistrement des métriques
        self._record_metrics()

    def _record_metrics(self):
        """Enregistre les métriques du système pour analyse"""
        self.history['time'].append(self.time)
        self.history['total_V'].append(sum(a.V_balance for a in self.agents.values()))
        self.history['total_U'].append(sum(a.U_balance for a in self.agents.values()))
        self.history['total_D'].append(self.rad.total_D())
        self.history['thermometer'].append(self.thermometer())
        self.history['indicator'].append(self.indicator())
        self.history['kappa'].append(self.rad.kappa)
        self.history['gini_coefficient'].append(self.gini_coefficient())
        self.history['circulation_rate'].append(self.circulation_rate())

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
